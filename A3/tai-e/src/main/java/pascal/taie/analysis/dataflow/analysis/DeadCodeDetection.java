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
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);

        // Phase 1: compute reachable statements
        Set<Stmt> reachable = computeReachable(cfg, constants);

        // Phase 2: compute dead code

        return computeDeadCode(cfg, reachable, liveVars);
    }

    private Set<Stmt> computeReachable(
            CFG<Stmt> cfg,
            DataflowResult<Stmt, CPFact> constants) {

        Set<Stmt> reachable = new HashSet<>();
        Queue<Stmt> worklist = new LinkedList<>();

        Stmt entry = cfg.getEntry();
        reachable.add(entry);
        worklist.add(entry);

        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.poll();

            if (stmt instanceof If ifStmt) {
                CPFact inFact = constants.getInFact(stmt);
                Value cond = ConstantPropagation.evaluate(
                        ifStmt.getCondition(), inFact);

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    if (!isReachableBranch(cond, edge)) {
                        continue;
                    }
                    Stmt target = edge.getTarget();
                    if (reachable.add(target)) {
                        worklist.add(target);
                    }
                }

            } else if (stmt instanceof SwitchStmt switchStmt) {
                CPFact inFact = constants.getInFact(stmt);
                Value switchVal = ConstantPropagation.evaluate(
                        switchStmt.getVar(), inFact);

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    if (!isReachableSwitchEdge(switchStmt, switchVal, edge)) {
                        continue;
                    }
                    Stmt target = edge.getTarget();
                    if (reachable.add(target)) {
                        worklist.add(target);
                    }
                }

            } else {
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    Stmt target = edge.getTarget();
                    if (reachable.add(target)) {
                        worklist.add(target);
                    }
                }
            }
        }

        return reachable;
    }

    private boolean isReachableBranch(Value cond, Edge<Stmt> edge) {
        if (!cond.isConstant()) {
            return true;
        }
        int c = cond.getConstant();
        return (c == 1 && edge.getKind() == Edge.Kind.IF_TRUE)
                || (c == 0 && edge.getKind() == Edge.Kind.IF_FALSE);
    }

    private boolean isReachableSwitchEdge(
            SwitchStmt stmt,
            Value switchVal,
            Edge<Stmt> edge) {

        if (!switchVal.isConstant()) {
            return true;
        }

        int constVal = switchVal.getConstant();

        boolean matched = false;
        for (int caseVal : stmt.getCaseValues()) {
            if (caseVal == constVal) {
                matched = true;
                break;
            }
        }

        if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
            return edge.getCaseValue() == constVal;
        } else {
            return !matched;
        }
    }

    private Set<Stmt> computeDeadCode(
            CFG<Stmt> cfg,
            Set<Stmt> reachable,
            DataflowResult<Stmt, SetFact<Var>> liveVars) {

        Set<Stmt> deadCode =
                new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        for (Stmt stmt : cfg.getNodes()) {

            if (!reachable.contains(stmt)&&stmt.getLineNumber()>0) {
                deadCode.add(stmt);
                continue;
            }

            if (stmt instanceof AssignStmt<?,?> assignStmt) {
                if (!(assignStmt.getLValue() instanceof Var lVar)) {
                    continue;
                }
                SetFact<Var> out = liveVars.getOutFact(stmt);

                if (!out.contains(lVar)
                        && hasNoSideEffect(assignStmt.getRValue())) {
                    deadCode.add(stmt);
                }
            }
        }

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
