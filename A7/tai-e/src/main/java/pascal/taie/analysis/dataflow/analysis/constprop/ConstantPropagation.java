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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import polyglot.ast.BooleanLit;
import polyglot.ast.CharLit;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var result = new CPFact();
        for (var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                result.update(param, Value.getNAC());
            }
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC()) return v1;
        if (v2.isNAC()) return v2;
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.equals(v2)) return v1;
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = out.copyFrom(in);

        if (stmt instanceof DefinitionStmt<?, ?> def) {
            var lvalue = def.getLValue();
            var rvalue = def.getRValue();
            if (lvalue instanceof Var var && canHoldInt(var)) {
                changed |= out.update(var, evaluate(rvalue, in));
            }
        }

        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral intLit) {
            return Value.makeConstant(intLit.getValue());
        } else if (exp instanceof BooleanLit booleanLit) {
            return Value.makeConstant(booleanLit.value() ? 1 : 0);
        } else if (exp instanceof CharLit charLit) {
            return Value.makeConstant(charLit.value());
        } else if (exp instanceof Var var) {
            return canHoldInt(var) ? in.get(var) : Value.getNAC();
        } else if (exp instanceof BinaryExp binop) {
            var lhs = in.get(binop.getOperand1());
            var rhs = in.get(binop.getOperand2());
            if (lhs.isUndef() || rhs.isUndef()) return Value.getUndef();
            var bothConstants = lhs.isConstant() && rhs.isConstant();
            var op = binop.getOperator();

            if (op instanceof ArithmeticExp.Op concreteOp) {
                switch (concreteOp) {
                    case ADD -> {
                        if (!bothConstants) return Value.getNAC();
                        return Value.makeConstant(lhs.getConstant() + rhs.getConstant());
                    }
                    case SUB -> {
                        if (!bothConstants) return Value.getNAC();
                        return Value.makeConstant(lhs.getConstant() - rhs.getConstant());
                    }
                    case MUL -> {
                        if ((lhs.isConstant() && lhs.getConstant() == 0) ||
                                (rhs.isConstant() && rhs.getConstant() == 0)) {
                            return Value.makeConstant(0);
                        }
                        if (!bothConstants) return Value.getNAC();
                        return Value.makeConstant(lhs.getConstant() * rhs.getConstant());
                    }
                    case DIV -> {
                        if ((rhs.isConstant() && rhs.getConstant() == 0)) {
                            return Value.getUndef();
                        } /* else if (lhs.isConstant() && lhs.getConstant() == 0) {
                            return Value.makeConstant(0);
                        } */
                        if (!bothConstants) return Value.getNAC();
                        return Value.makeConstant(lhs.getConstant() / rhs.getConstant());
                    }
                    case REM -> {
                        if ((rhs.isConstant() && rhs.getConstant() == 0)) {
                            return Value.getUndef();
                        } /* else if (lhs.isConstant() && lhs.getConstant() == 0) {
                            return Value.makeConstant(0);
                        } */
                        if (!bothConstants) return Value.getNAC();
                        return Value.makeConstant(lhs.getConstant() % rhs.getConstant());
                    }
                }
            } else if (op instanceof ConditionExp.Op concreteOp) {
                if (!bothConstants) return Value.getNAC();
                var l = lhs.getConstant();
                var r = rhs.getConstant();
                switch (concreteOp) {
                    case EQ -> {
                        return Value.makeConstant(l == r ? 1 : 0);
                    }
                    case NE -> {
                        return Value.makeConstant(l != r ? 1 : 0);
                    }
                    case LT -> {
                        return Value.makeConstant(l < r ? 1 : 0);
                    }
                    case GT -> {
                        return Value.makeConstant(l > r ? 1 : 0);
                    }
                    case LE -> {
                        return Value.makeConstant(l <= r ? 1 : 0);
                    }
                    case GE -> {
                        return Value.makeConstant(l >= r ? 1 : 0);
                    }
                }
            } else if (op instanceof ShiftExp.Op concreteOp) {
                if (!bothConstants) return Value.getNAC();
                var l = lhs.getConstant();
                var r = rhs.getConstant();
                switch (concreteOp) {
                    case SHL -> {
                        return Value.makeConstant(l << r);
                    }
                    case SHR -> {
                        return Value.makeConstant(l >> r);
                    }
                    case USHR -> {
                        return Value.makeConstant(l >>> r);
                    }
                }
            } else if (op instanceof BitwiseExp.Op concreteOp) {
                if (!bothConstants) return Value.getNAC();
                var l = lhs.getConstant();
                var r = rhs.getConstant();
                switch (concreteOp) {
                    case OR -> {
                        return Value.makeConstant(l | r);
                    }
                    case AND -> {
                        return Value.makeConstant(l & r);
                    }
                    case XOR -> {
                        return Value.makeConstant(l ^ r);
                    }
                }
            }
        }
        return Value.getNAC();
    }
}
