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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private HashMap<JField, Value> staticValues;
    private HashMap<JField, List<LoadField>> usages;
    private HashMap<Var, List<Var>> aliasGroups;


    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);

        usages = new HashMap<>();
        staticValues = new HashMap<>();
        aliasGroups = new HashMap<>();

        for (var node : icfg) {
            if (node instanceof LoadField load) {
                var f = load.getFieldRef().resolve();
                var usageList = usages.getOrDefault(f, new ArrayList<>());
                usageList.add(load);
                usages.put(f, usageList);
            }
        }

        for (var v1 : pta.getVars()) {
            var points1 = pta.getPointsToSet(v1);
            var aliasGroup = new ArrayList<Var>();
            for (var v2 : pta.getVars()) {
                var points2 = pta.getPointsToSet(v2);
                if (points1.stream().anyMatch(points2::contains)) {
                    aliasGroup.add(v2);
                }
            }
            aliasGroups.put(v1, aliasGroup);
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        var changed = new AtomicBoolean(false);
        in.forEach((var, value) -> changed.set(changed.get() | out.update(var, value)));
        return changed.get();
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        var result = in.copy();
        if (stmt instanceof LoadField load && ConstantPropagation.canHoldInt(load.getLValue())) {
            var f = load.getFieldRef().resolve();
            if (f.isStatic()) {
                var known = staticValues.getOrDefault(f, Value.getUndef());
                result.update(load.getLValue(), known);
            } else {
                var base = ((InstanceFieldAccess)load.getFieldAccess()).getBase();
                var value = Value.getUndef();
                for (var alias : aliasGroups.get(base)) {
                    for (var store : alias.getStoreFields()) {
                        if (store.getFieldRef().resolve() == load.getFieldRef().resolve()) {
                            value = cp.meetValue(value, solver.getInFact(store).get(store.getRValue()));
                        }
                    }
                }
                result.update(load.getLValue(), value);
            }
            return out.copyFrom(result);
        } else if (stmt instanceof StoreField store && ConstantPropagation.canHoldInt(store.getRValue())) {
            var f = store.getFieldRef().resolve();
            if (f.isStatic()) {
                var prev = staticValues.getOrDefault(f, Value.getUndef());
                var meet = cp.meetValue(prev, in.get(store.getRValue()));
                if (prev != meet) {
                    staticValues.put(f, meet);
                    for (var usage : usages.get(f)) {
                        solver.enqueue(usage);
                    }
                }
            } else {
                var base = ((InstanceFieldAccess)store.getFieldAccess()).getBase();
                for (var alias : aliasGroups.get(base)) {
                    for (var load : alias.getLoadFields()) {
                        if (load.getFieldRef().resolve() == store.getFieldRef().resolve()) {
                            solver.enqueue(load);
                        }
                    }
                }
            }
        } else if (stmt instanceof LoadArray load && ConstantPropagation.canHoldInt(load.getLValue())) {
            var base = load.getArrayAccess().getBase();
            var value = Value.getUndef();
            for (var alias : aliasGroups.get(base)) {
                for (var store : alias.getStoreArrays()) {
                    var indexStore = solver.getInFact(store).get(store.getArrayAccess().getIndex());
                    var indexLoad = in.get(load.getArrayAccess().getIndex());
                    boolean aliased;
                    if (indexLoad.isUndef() || indexStore.isUndef()) {
                        aliased = false;
                    } else if (indexLoad.isNAC() || indexStore.isNAC()) {
                        aliased = true;
                    } else {
                        aliased = indexLoad.getConstant() == indexStore.getConstant();
                    }
                    if (aliased) {
                        value = cp.meetValue(value, solver.getOutFact(store).get(store.getRValue()));
                    }
                }
            }
            result.update(load.getLValue(), value);
            return out.copyFrom(result);
        } else if (stmt instanceof StoreArray store && ConstantPropagation.canHoldInt(store.getRValue())) {
            var base = store.getArrayAccess().getBase();
            for (var alias : aliasGroups.get(base)) {
                for (var load : alias.getLoadArrays()) {
                    solver.enqueue(load);
                }
            }
        }

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        var result = out.copy();
        var maybeDef = edge.getSource().getDef();
        if (maybeDef.isPresent()) {
            var def = maybeDef.get();
            if (def instanceof Var var) {
                result.remove(var);
            }
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        var call = (Invoke)edge.getSource();
        var callee = edge.getCallee();
        var result = new CPFact();
        var ir = callee.getIR();
        var numParams = ir.getParams().size();
        for (var i = 0; i < numParams; ++i) {
            var param = ir.getParam(i);
            result.update(param, callSiteOut.get(call.getRValue().getArg(i)));
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        var call = (Invoke)edge.getCallSite();
        if (call.getLValue() == null) return new CPFact();

        var result = Value.getUndef();
        for (var ret : edge.getReturnVars()) {
            result = cp.meetValue(result, returnOut.get(ret));
        }
        var fact = new CPFact();
        fact.update(call.getLValue(), result);
        return fact;
    }
}
