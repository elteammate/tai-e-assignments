/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.addReachableMethod(method)) return;
        if (method.isAbstract()) return;

        for (var stmt : method.getIR()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(stmt.getLValue()),
                    new PointsToSet(heapModel.getObj(stmt))
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                var f = stmt.getLValue().getFieldRef().resolve();
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(f)
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                var f = stmt.getRValue().getFieldRef().resolve();
                addPFGEdge(
                        pointerFlowGraph.getStaticField(f),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                var m = resolveCallee(null, stmt);
                if (!callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, m))) return null;
                addReachable(m);
                var ir = m.getIR();
                for (var i = 0; i < ir.getParams().size(); ++i) {
                    var arg = stmt.getRValue().getArg(i);
                    var param = ir.getParam(i);
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(arg),
                            pointerFlowGraph.getVarPtr(param)
                    );
                }
                if (stmt.getLValue() != null) {
                    for (var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target)) return;
        var points = source.getPointsToSet();
        if (points.isEmpty()) return;
        workList.addEntry(target, points);
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var task = workList.pollEntry();
            var delta = propagate(task.pointer(), task.pointsToSet());

            if (task.pointer() instanceof VarPtr varPtr) {
                var var = varPtr.getVar();
                for (var point : delta) {
                    for (var load : var.getLoadFields()) {
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(point, load.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(load.getLValue())
                        );
                    }
                    for (var store : var.getStoreFields()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(store.getRValue()),
                                pointerFlowGraph.getInstanceField(point, store.getFieldRef().resolve())
                        );
                    }
                    for (var load : var.getLoadArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(point),
                                pointerFlowGraph.getVarPtr(load.getLValue())
                        );
                    }
                    for (var store : var.getStoreArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(store.getRValue()),
                                pointerFlowGraph.getArrayIndex(point)
                        );
                    }

                    processCall(var, point);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = new PointsToSet();
        var current = pointer.getPointsToSet();
        for (var point : pointsToSet) {
            if (!current.contains(point)) {
                delta.addObject(point);
            }
        }
        if (delta.isEmpty()) return delta;
        for (var point : delta) current.addObject(point);
        for (var succ : pointerFlowGraph.getSuccsOf(pointer)) {
            workList.addEntry(succ, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var call : var.getInvokes()) {
            var m = resolveCallee(recv, call);
            if (m.isAbstract()) continue;
            var ir = m.getIR();
            if (ir.getThis() != null) {
                workList.addEntry(pointerFlowGraph.getVarPtr(ir.getThis()), new PointsToSet(recv));
            }
            if (callGraph.contains(m)) continue;
            addReachable(m);
            var callKind = call.isVirtual() ? CallKind.VIRTUAL
                    : call.isDynamic() ? CallKind.DYNAMIC
                    : call.isInterface() ? CallKind.INTERFACE
                    : call.isSpecial() ? CallKind.SPECIAL
                    : CallKind.OTHER;

            callGraph.addEdge(new Edge<>(callKind, call, m));

            for (var i = 0; i < ir.getParams().size(); ++i) {
                var arg = call.getRValue().getArg(i);
                var param = ir.getParam(i);
                addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
            }
            if (call.getLValue() != null) {
                for (var ret : m.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(call.getLValue()));
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
