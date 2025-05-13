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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.addReachableMethod(csMethod)) return;
        var method = csMethod.getMethod();
        // if (method.isAbstract()) return;

        var visitor = new StmtProcessor(csMethod);
        for (var stmt : method.getIR()) {
            stmt.accept(visitor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            var heapObj = heapModel.getObj(stmt);
            var ctx = contextSelector.selectHeapContext(csMethod, heapObj);
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(ctx, heapObj))
            );
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue())
            );
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                var f = stmt.getLValue().getFieldRef().resolve();
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(f)
                );
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                var f = stmt.getRValue().getFieldRef().resolve();
                addPFGEdge(
                        csManager.getStaticField(f),
                        csManager.getCSVar(context, stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                var m = resolveCallee(null, stmt);
                var call = csManager.getCSCallSite(context, stmt);
                var calleeContext = contextSelector.selectContext(call, m);
                var csm = csManager.getCSMethod(calleeContext, m);
                if (!callGraph.addEdge(new Edge<>(CallKind.STATIC, call, csm))) return null;
                addReachable(csm);
                var ir = m.getIR();
                for (var i = 0; i < ir.getParams().size(); ++i) {
                    var arg = stmt.getRValue().getArg(i);
                    var param = ir.getParam(i);
                    addPFGEdge(
                            csManager.getCSVar(context, arg),
                            csManager.getCSVar(calleeContext, param)
                    );
                }
                if (stmt.getLValue() != null) {
                    for (var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, ret),
                                csManager.getCSVar(context, stmt.getLValue())
                        );
                    }
                }

                taintAnalysis.processCall(m, stmt, context, null);
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

            if (task.pointer() instanceof CSVar varPtr) {
                var var = varPtr.getVar();
                var ctx = varPtr.getContext();
                for (var point : delta) {
                    for (var load : var.getLoadFields()) {
                        addPFGEdge(
                                csManager.getInstanceField(point, load.getFieldRef().resolve()),
                                csManager.getCSVar(ctx, load.getLValue())
                        );
                    }
                    for (var store : var.getStoreFields()) {
                        addPFGEdge(
                                csManager.getCSVar(ctx, store.getRValue()),
                                csManager.getInstanceField(point, store.getFieldRef().resolve())
                        );
                    }
                    for (var load : var.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(point),
                                csManager.getCSVar(ctx, load.getLValue())
                        );
                    }
                    for (var store : var.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(ctx, store.getRValue()),
                                csManager.getArrayIndex(point)
                        );
                    }

                    processCall(varPtr, point);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
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
        taintAnalysis.propagate(pointer, delta);
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (var call : recv.getVar().getInvokes()) {
            var m = resolveCallee(recvObj, call);
            if (m == null) return;
            if (m.isAbstract()) continue;
            var ir = m.getIR();
            var ctxCaller = recv.getContext();
            var csCall = csManager.getCSCallSite(ctxCaller, call);
            var ctxCallee = contextSelector.selectContext(csCall, recvObj, m);
            var csm = csManager.getCSMethod(ctxCallee, m);
            if (ir.getThis() != null) {
                workList.addEntry(csManager.getCSVar(ctxCallee, ir.getThis()), PointsToSetFactory.make(recvObj));
            }

            if (!callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(call), csCall, csm))) continue;
            addReachable(csm);

            for (var i = 0; i < ir.getParams().size(); ++i) {
                var arg = call.getRValue().getArg(i);
                var param = ir.getParam(i);
                addPFGEdge(csManager.getCSVar(ctxCaller, arg), csManager.getCSVar(ctxCallee, param));
            }
            if (call.getLValue() != null) {
                for (var ret : m.getIR().getReturnVars()) {
                    addPFGEdge(csManager.getCSVar(ctxCallee, ret), csManager.getCSVar(ctxCaller, call.getLValue()));
                }
            }

            taintAnalysis.processCall(m, call, ctxCaller, recv);
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    public void enqueue(Pointer pointer, PointsToSet delta) {
        workList.addEntry(pointer, delta);
    }
}
