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

import pascal.taie.Assignment;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
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
        // TODO - finish me
        // 将方法的参数设置为NAC，避免直接被优化掉
        CPFact res = new CPFact();
        IR ir = cfg.getIR();
        List<Var> paras = ir.getParams();
        for (Var para : paras) {
            res.update(para, Value.getNAC());
        }
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        // 一开始的变量类型全部是undefined，
        // 这样在meet的时候才ok
        CPFact res = new CPFact();
        return res;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
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
     * 对同一个变量的两个值，他们meet的情况下的处理
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
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
            return v2;
        } else {
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 不考虑不是赋值语句的表达式
        if (!(stmt instanceof DefinitionStmt<?,?>)) {
            return false;
        }
        Optional<LValue> def = stmt.getDef();
        assert def.isPresent();
        LValue def_ = def.get();
        // 对于赋值类型的语句，只处理左边为Var的类型，
        // 对于字段存储等类型，不进行处理。
        if (!(def_ instanceof  Var)) return false;
        CPFact new_out = new CPFact();


        return false;
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
        return null;
    }
}
