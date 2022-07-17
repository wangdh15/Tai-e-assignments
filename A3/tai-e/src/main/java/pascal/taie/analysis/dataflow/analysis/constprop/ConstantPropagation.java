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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Optional;
import java.util.Set;

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
        // 将方法的参数设置为NAC，避免直接被优化掉
        CPFact res = new CPFact();
        IR ir = cfg.getIR();
        List<Var> paras = ir.getParams();
        for (Var para : paras) {
            if (canHoldInt(para)) {
                res.update(para, Value.getNAC());
            }
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // 一开始的变量类型全部是undefined，
        // 这样在meet的时候才ok
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> keys = fact.keySet();
        // 只需要遍历fact的key即可，因为对应在target而没有在fact里的key，
        // value不需要修改
        for (Var k : keys) {
            Value val = fact.get(k);
            Value new_val = meetValue(val, target.get(k));
            target.update(k, new_val);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // 有一个不是常量，则就不是常量
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        // 都是常量，相同，则返回常量，否则的话，则不是常量
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v1.isConstant() && v2.isUndef()) {
            return v1;
        } else {
            return Value.getUndef();
        }
    }

    private boolean compare(CPFact new_out, CPFact out) {
        if (new_out.equals(out)) {
            return false;
        } else {
            out.copyFrom(new_out);
            return true;
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // 不考虑不是赋值语句的表达式
        if (!(stmt instanceof DefinitionStmt<?,?>)) {
            return compare(in, out);
        }
        Optional<LValue> def = stmt.getDef();
        // 当时invoke函数的时候，def为空
        if (def.isEmpty()) {
            return compare(in, out);
        }
        LValue def_ = def.get();
        // 对于赋值类型的语句，只处理左边为Var的类型，
        // 对于字段存储等类型，不进行处理。
        if (!(def_ instanceof  Var)) {
            return compare(in, out);
        }
        // 只处理int类型的变量
        if (!canHoldInt((Var)def_)){
            return compare(in, out);
        }
        CPFact new_out = in.copy();
        // 将对def_的定义进行删除
        new_out.remove((Var)def_);
        RValue r_expr = ((DefinitionStmt<?, ?>)stmt).getRValue();
        new_out.update((Var)def_, evaluate(r_expr, in));
        // 判断新的out和之前的out是否相同
        return compare(new_out, out);
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
        Value res = null;
        boolean flag = true;
        if (exp instanceof IntLiteral) {
            // 如果右侧是一个常量表达式的话
            res = Value.makeConstant(((IntLiteral)exp).getValue());
        } else if (exp instanceof Var) {
            // 如果右侧是一个变量的话
            res = in.get((Var)exp);
        } else if (exp instanceof ArithmeticExp) {
            // 算术表达式
            Var var1 = ((ArithmeticExp) exp).getOperand1();
            Var var2 = ((ArithmeticExp) exp).getOperand2();
            ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
            if (in.get(var2).isConstant() && in.get(var2).getConstant() == 0 && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)) {
                res = Value.getUndef();
            } else if (in.get(var1).isConstant() && in.get(var2).isConstant()) {
                // 两个都是常量的情况
                int val = 0;
                int val1 =  in.get(var1).getConstant();
                int val2 = in.get(var2).getConstant();
                if (op == ArithmeticExp.Op.ADD) {
                    val = val1 + val2;
                } else if (op == ArithmeticExp.Op.SUB) {
                    val = val1 - val2;
                } else if (op == ArithmeticExp.Op.MUL) {
                    val = val1 * val2;
                } else if (op == ArithmeticExp.Op.DIV) {
                    if (val2 == 0) {
                        res = Value.getUndef();
                        flag = false;
                    } else {
                        val = val1 / val2;
                    }
                } else {
                    if (val2 == 0) {
                        res = Value.getUndef();
                        flag = false;
                    } else {
                        val = val1 % val2;
                    }
                }
                if (flag) {
                    res = Value.makeConstant(val);
                }
            } else if (in.get(var1).isNAC() || in.get(var2).isNAC()) {
                // 有一个不是常量
                res = Value.getNAC();
            } else {
                // 其他情况
                res = Value.getUndef();
            }
        } else if (exp instanceof  ConditionExp) {
            // 条件表达式
            Var var1 = ((ConditionExp) exp).getOperand1();
            Var var2 = ((ConditionExp) exp).getOperand2();
            ConditionExp.Op op = ((ConditionExp) exp).getOperator();
            if (in.get(var1).isConstant() && in.get(var2).isConstant()) {
                int val = 0;
                int val1 = in.get(var1).getConstant();
                int val2 = in.get(var2).getConstant();
                if (op == ConditionExp.Op.EQ) {
                    if (val1 == val2) val = 1;
                } else if (op == ConditionExp.Op.NE) {
                    if (val1 != val2) val = 1;
                } else if (op == ConditionExp.Op.LT){
                    if (val1 < val2) val = 1;
                } else if (op == ConditionExp.Op.GT){
                    if (val1 > val2) val = 1;
                } else if (op == ConditionExp.Op.LE) {
                    if (val1 <= val2) val = 1;
                } else {
                    if (val1 >= val2) val = 1;
                }
                res = Value.makeConstant(val);
            } else if (in.get(var1).isNAC() || in.get(var2).isNAC()) {
                res = Value.getNAC();
            } else {
                res = Value.getUndef();
            }
        } else if (exp instanceof  ShiftExp) {
            // 移位表达式
            Var var1 = ((ShiftExp) exp).getOperand1();
            Var var2 = ((ShiftExp) exp).getOperand2();
            ShiftExp.Op op = ((ShiftExp) exp).getOperator();
            if (in.get(var1).isConstant() && in.get(var2).isConstant()) {
                int val = 0;
                int val1 = in.get(var1).getConstant();
                int val2 = in.get(var2).getConstant();
                if (op == ShiftExp.Op.SHL) {
                    val = val1 << val2;
                } else if (op == ShiftExp.Op.SHR) {
                    val = val1 >> val2;
                } else {
                    val = val1 >>> val2;
                }
                res = Value.makeConstant(val);
            } else if (in.get(var1).isNAC() || in.get(var2).isNAC()) {
                res = Value.getNAC();
            } else {
                res = Value.getUndef();
            }
        } else if (exp instanceof BitwiseExp) {
            // 位运算
            Var var1 = ((BitwiseExp) exp).getOperand1();
            Var var2 = ((BitwiseExp) exp).getOperand2();
            BinaryExp.Op op = ((BitwiseExp) exp).getOperator();
            if (in.get(var1).isConstant() && in.get(var2).isConstant()) {
                int val = 0;
                int val1 = in.get(var1).getConstant(), val2 = in.get(var2).getConstant();
                if (op == BitwiseExp.Op.OR) {
                    val = val1 | val2;
                } else if (op == BitwiseExp.Op.AND) {
                    val =  val1 & val2;
                } else {
                    val = val1 ^ val2;
                }
                res = Value.makeConstant(val);
            }  else if (in.get(var1).isNAC() || in.get(var2).isNAC()) {
                res = Value.getNAC();
            } else {
                res = Value.getUndef();
            }
        } else {
            // 其他表达式
            res = Value.getNAC();
        }
        return res;
    }
}
