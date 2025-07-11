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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        var visited = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        var q = new ArrayList<Stmt>();
        q.add(cfg.getEntry());

        while (!q.isEmpty()) {
            var node = q.remove(q.size() - 1);
            if (visited.contains(node)) continue;
            visited.add(node);

            if (node instanceof AssignStmt<?,?> assignment && assignment.getLValue() instanceof Var var) {
                if (hasNoSideEffect(assignment.getRValue()) && !liveVars.getResult(node).contains(var)) {
                    deadCode.add(node);
                }
                q.addAll(cfg.getSuccsOf(node));
            } else if (node instanceof If ifNode) {
                var condVar = ConstantPropagation.evaluate(ifNode.getCondition(), constants.getResult(node));
                for (var branch : cfg.getOutEdgesOf(ifNode)) {
                    if (!condVar.isConstant()
                        || (condVar.getConstant() != 0 && branch.getKind() == Edge.Kind.IF_TRUE)
                        || (condVar.getConstant() == 0 && branch.getKind() == Edge.Kind.IF_FALSE)
                    ) {
                        q.add(branch.getTarget());
                    }
                }
            } else if (node instanceof SwitchStmt switchNode) {
                var condVar = ConstantPropagation.evaluate(switchNode.getVar(), constants.getResult(node));
                for (var branch : cfg.getOutEdgesOf(switchNode)) {
                    if (!condVar.isConstant()
                        || (branch.getKind() == Edge.Kind.SWITCH_CASE && condVar.getConstant() == branch.getCaseValue())
                        || (branch.getKind() == Edge.Kind.SWITCH_DEFAULT &&
                            cfg.getOutEdgesOf(switchNode).stream().noneMatch(
                                    b -> b.getKind() == Edge.Kind.SWITCH_CASE &&
                                            b.getCaseValue() == condVar.getConstant()
                            ))
                    ) {
                        q.add(branch.getTarget());
                    }
                }
            } else {
                q.addAll(cfg.getSuccsOf(node));
            }
        }

        for (var node : cfg.getNodes()) {
            if (!visited.contains(node) && !node.equals(cfg.getExit())) {
                deadCode.add(node);
            }
        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
