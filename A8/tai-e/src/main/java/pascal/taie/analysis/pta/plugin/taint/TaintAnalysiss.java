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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import javax.annotation.Nullable;
import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final HashMap<Pointer, HashSet<Pointer>> taintTransfers;

    private final HashMap<CSCallSite, HashSet<Sink>> reachableSinks;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        taintTransfers = new HashMap<>();
        reachableSinks = new HashMap<>();
    }

    private boolean registerTaintTransfer(Pointer from, Pointer to) {
        var old = taintTransfers.getOrDefault(from, new HashSet<>());
        var changed = old.add(to);
        taintTransfers.put(from, old);
        return changed;
    }

    public void propagate(Pointer pointer, PointsToSet delta) {
        var newDelta = PointsToSetFactory.make();
        for (var obj : delta) {
            if (manager.isTaint(obj.getObject())) {
                newDelta.addObject(obj);
            }
        }
        if (newDelta.isEmpty()) return;
        for (var succ : taintTransfers.getOrDefault(pointer, new HashSet<>())) {
            solver.enqueue(succ, newDelta);
        }
    }

    public void processCall(JMethod method, Invoke call, Context ctxCaller, @Nullable CSVar recv) {
        var lvalue = call.getLValue() != null ? csManager.getCSVar(ctxCaller, call.getLValue()) : null;
        for (var source : config.getSources()) {
            if (method.equals(source.method()) && lvalue != null) {
                var taint = manager.makeTaint(call, method.getReturnType());
                solver.enqueue(lvalue, PointsToSetFactory.make(csManager.getCSObj(ctxCaller, taint)));
            }
        }

        for (var sink : config.getSinks()) {
            if (method.equals(sink.method())) {
                var csCall = csManager.getCSCallSite(ctxCaller, call);
                var old = reachableSinks.getOrDefault(csCall, new HashSet<>());
                old.add(sink);
                reachableSinks.put(csCall, old);
            }
        }

        for (var transfer : config.getTransfers()) {
            if (!transfer.method().equals(method)) continue;
            if (recv != null && transfer.from() == TaintTransfer.BASE && transfer.to() == TaintTransfer.RESULT) {
                if (lvalue == null) continue;
                if (!registerTaintTransfer(recv, lvalue)) continue;
                for (var obj : recv.getPointsToSet()) {
                    if (!manager.isTaint(obj.getObject())) continue;
                    var taint = manager.makeTaint(manager.getSourceCall(obj.getObject()), method.getReturnType());
                    propagate(recv, PointsToSetFactory.make(csManager.getCSObj(emptyContext, taint)));
                }
            } else if (recv != null && transfer.to() == TaintTransfer.BASE) {
                var arg = csManager.getCSVar(ctxCaller, call.getInvokeExp().getArg(transfer.from()));
                if (!registerTaintTransfer(arg, recv)) continue;
                for (var obj : arg.getPointsToSet()) {
                    if (!manager.isTaint(obj.getObject())) continue;
                    var taint = manager.makeTaint(manager.getSourceCall(obj.getObject()), recv.getType());
                    propagate(arg, PointsToSetFactory.make(csManager.getCSObj(emptyContext, taint)));
                }
            } else if (transfer.to() == TaintTransfer.RESULT) {
                var arg = csManager.getCSVar(ctxCaller, call.getInvokeExp().getArg(transfer.from()));
                if (lvalue == null) continue;
                if (!registerTaintTransfer(arg, lvalue)) continue;
                for (var obj : arg.getPointsToSet()) {
                    if (!manager.isTaint(obj.getObject())) continue;
                    var taint = manager.makeTaint(manager.getSourceCall(obj.getObject()), method.getReturnType());
                    propagate(arg, PointsToSetFactory.make(csManager.getCSObj(emptyContext, taint)));
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        reachableSinks.forEach((call, sinks) -> {
            for (var sink : sinks) {
                var arg = call.getCallSite().getInvokeExp().getArg(sink.index());
                for (var obj : result.getPointsToSet(arg)) {
                    if (manager.isTaint(obj)) {
                        taintFlows.add(new TaintFlow(
                                manager.getSourceCall(obj),
                                call.getCallSite(),
                                sink.index()
                        ));
                    }
                }
            }
        });
        return taintFlows;
    }
}
