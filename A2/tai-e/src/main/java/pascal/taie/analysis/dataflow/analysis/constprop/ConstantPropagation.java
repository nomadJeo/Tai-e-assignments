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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
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
        // TODO - finish me
        if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }else if (exp instanceof Var) {
            return in.get((Var) exp);
        }else if (exp instanceof BinaryExp binaryExp) {

            Value left  = in.get(binaryExp.getOperand1());
            Value right = in.get(binaryExp.getOperand2());

            // 1. NAC 传播（但要先处理除 0）
            if (left.isNAC() || right.isNAC()) {
                if (binaryExp instanceof ArithmeticExp arith) {
                    if ((arith.getOperator() == ArithmeticExp.Op.DIV ||
                            arith.getOperator() == ArithmeticExp.Op.REM)
                            && right.isConstant()
                            && right.getConstant() == 0) {
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }

            // 2. 常量折叠
            if (left.isConstant() && right.isConstant()) {
                int l = left.getConstant();
                int r = right.getConstant();

                if (binaryExp instanceof ArithmeticExp arith) {
                    return switch (arith.getOperator()) {
                        case ADD -> Value.makeConstant(l + r);
                        case SUB -> Value.makeConstant(l - r);
                        case MUL -> Value.makeConstant(l * r);
                        case DIV -> (r == 0) ? Value.getUndef()
                                : Value.makeConstant(l / r);
                        case REM -> (r == 0) ? Value.getUndef()
                                : Value.makeConstant(l % r);
                    };
                }

                if (binaryExp instanceof BitwiseExp bitwise) {
                    return switch (bitwise.getOperator()) {
                        case AND -> Value.makeConstant(l & r);
                        case OR  -> Value.makeConstant(l | r);
                        case XOR -> Value.makeConstant(l ^ r);
                    };
                }

                if (binaryExp instanceof ShiftExp shift) {
                    return switch (shift.getOperator()) {
                        case SHL  -> Value.makeConstant(l << r);
                        case SHR  -> Value.makeConstant(l >> r);
                        case USHR -> Value.makeConstant(l >>> r);
                    };
                }

                if (binaryExp instanceof ConditionExp cond) {
                    return switch (cond.getOperator()) {
                        case EQ -> Value.makeConstant(l == r ? 1 : 0);
                        case NE -> Value.makeConstant(l != r ? 1 : 0);
                        case LT -> Value.makeConstant(l <  r ? 1 : 0);
                        case LE -> Value.makeConstant(l <= r ? 1 : 0);
                        case GT -> Value.makeConstant(l >  r ? 1 : 0);
                        case GE -> Value.makeConstant(l >= r ? 1 : 0);
                    };
                }

                return Value.getUndef();
            }

            // 3. 剩下的情况：包含 UNDEF
            return Value.getUndef();
        }
        return Value.getNAC();
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        //不考虑跨方法传递常量，参数变量初始值均为NAC
        for (Var var : cfg.getMethod().getIR().getParams()) {
            if (canHoldInt(var)) {
                cpFact.update(var, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            Value v1 = fact.get(var);
            Value v2 = target.get(var);
            Value meetV = meetValue(v1, v2);
            target.update(var, meetV);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef()) {
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.equals(v2)) {
            return Value.makeConstant(v1.getConstant());
        }
        //不同值常量
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact newOut = in.copy();

        if (stmt instanceof DefinitionStmt defStmt) {
            if (defStmt.getLValue() instanceof Var defVar) {
                if (canHoldInt(defVar)) {
                    // remove the previous mapping
                    newOut.remove(defVar);
                    Exp rhs = defStmt.getRValue();

                    Value rhsValue = evaluate(rhs, in);

                    newOut.update(defVar, rhsValue);
                }
            }

        }

        if (!newOut.equals(out)) {
            out.clear();
            out.copyFrom(newOut);
            return true;
        }

        return false;
    }
}
