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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        var q = new ArrayList<JMethod>();
        q.add(entry);
        while (!q.isEmpty()) {
            var caller = q.remove(q.size() - 1);
            if (callGraph.contains(caller)) continue;
            callGraph.addReachableMethod(caller);

            for (var call : callGraph.getCallSitesIn(caller)) {
                for (var callee : resolve(call)) {
                    q.add(callee);
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(call), call, callee));
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC: {
                var methodRef = callSite.getMethodRef();
                var m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
                return Collections.singleton(m);
            }
            case SPECIAL: {
                var m = dispatch(
                        callSite.getMethodRef().getDeclaringClass(),
                        callSite.getMethodRef().getSubsignature()
                );
                if (m != null) {
                    return Collections.singleton(m);
                } else {
                    return Collections.emptySet();
                }
            }
            case INTERFACE:
            case VIRTUAL: {
                var q = new ArrayList<JClass>();
                var visited = new HashSet<JClass>();
                var methodRef = callSite.getMethodRef();
                q.add(methodRef.getDeclaringClass());
                var result = new HashSet<JMethod>();
                var sig = methodRef.getSubsignature();

                while (!q.isEmpty()) {
                    var jclass = q.remove(q.size() - 1);
                    if (visited.contains(jclass)) continue;
                    visited.add(jclass);

                    var m = dispatch(jclass, sig);
                    if (m != null) result.add(m);
                    if (jclass.isInterface()) {
                        q.addAll(hierarchy.getDirectImplementorsOf(jclass));
                        q.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                    } else {
                        q.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                }

                return result;
            }
            case DYNAMIC:
                break;
            case OTHER:
                break;
        }
        return Collections.emptySet();
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = null;
        while (method == null && jclass != null) {
            method = jclass.getDeclaredMethod(subsignature);
            jclass = jclass.getSuperClass();
        }
        return method.isAbstract() ? null : method;
    }
}
