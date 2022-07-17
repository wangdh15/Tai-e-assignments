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
import pascal.taie.ir.exp.*;
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
        // Your task is to recognize dead code in ir and add it to deadCode

        // unreachable branch
        Set<Stmt> reachable_stmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> vis = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        vis.add(cfg.getEntry());
        while (!queue.isEmpty()) {
            Stmt cur_stmt = queue.remove();
            reachable_stmts.add(cur_stmt);
            Set<Edge<Stmt>> out_edges = cfg.getOutEdgesOf(cur_stmt);
            if (cur_stmt instanceof If) {
                Value eval_result = ConstantPropagation.evaluate(((If) cur_stmt).getCondition(), constants.getOutFact(cur_stmt));
                boolean add_true_branch = false, add_false_branch = false;
                if (eval_result.isConstant()) {
                    if (eval_result.getConstant() == 0) {
                        add_false_branch = true;
                    } else {
                        add_true_branch = true;
                    }
                } else {
                    add_true_branch = true;
                    add_false_branch = true;
                }
                for (Edge<Stmt> edge : out_edges) {
                    if (add_true_branch && edge.getKind() == Edge.Kind.IF_TRUE)  {
                        if (!vis.contains(edge.getTarget())) {
                            vis.add(edge.getTarget());
                            queue.add(edge.getTarget());
                        }
                    }
                    if (add_false_branch && edge.getKind() == Edge.Kind.IF_FALSE)  {
                        if (!vis.contains(edge.getTarget())) {
                            vis.add(edge.getTarget());
                            queue.add(edge.getTarget());
                        }
                    }
                }
            } else if (cur_stmt instanceof SwitchStmt) {
                Value eval_result = ConstantPropagation.evaluate(((SwitchStmt) cur_stmt).getVar(), constants.getOutFact(cur_stmt));
                if (eval_result.isConstant()) {
                    int eval_value = eval_result.getConstant();
                    boolean find_branch = false;
                    Stmt default_branch = null;
                    for (Edge<Stmt> edge : out_edges) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == eval_value) {
                            find_branch = true;
                            if (!vis.contains(edge.getTarget())) {
                                vis.add(edge.getTarget());
                                queue.add(edge.getTarget());
                            }
                            break;
                        } else if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            default_branch = edge.getTarget();
                        }
                    }
                    if (!find_branch) {
                        if (!vis.contains(default_branch)) {
                            vis.add(default_branch);
                            queue.add(default_branch);
                        }
                    }
                } else {
                    // 不是常量则全部加入
                    for (Edge<Stmt> edge : out_edges) {
                        if (!vis.contains(edge.getTarget())) {
                            vis.add(edge.getTarget());
                            queue.add(edge.getTarget());
                        }
                    }
                }
            } else {

                for (Edge<Stmt> edge : out_edges) {
                    if (!vis.contains(edge.getTarget())) {
                        vis.add(edge.getTarget());
                        queue.add(edge.getTarget());
                    }
                }
            }
        }
        for (Stmt stmt : ir.getStmts()) {
            if (!reachable_stmts.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

//        System.out.printf("11: %d\n", deadCode.size());

        // unused assignment
        for (Stmt stmt : ir.getStmts()) {
            if (deadCode.contains(stmt)) continue;

            if (!(stmt instanceof AssignStmt<?,?>)) continue;

            LValue lValue = ((AssignStmt<?, ?>) stmt).getLValue();
            if (!(lValue instanceof  Var)) continue;

            RValue rValue = ((AssignStmt<?, ?>) stmt).getRValue();
            if (!hasNoSideEffect(rValue)) continue;

            if (!liveVars.getOutFact(stmt).contains((Var) lValue)) {
                deadCode.add(stmt);
            }
        }

//        System.out.printf("22: %d\n", deadCode.size());
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
