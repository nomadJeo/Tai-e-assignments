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
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Objects;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.canHoldInt;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private MultiMap<StoreField, LoadField> fieldStoreTOLoadMap;
    private MultiMap<StoreArray, LoadArray> arrayStoreToLoadMap;
    private MultiMap<LoadArray, StoreArray> arrayLoadToStoreMap;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        MultiMap<JField, StoreField> staticFiledStore = Maps.newMultiMap();
        MultiMap<JField, LoadField> staticFiledLoad = Maps.newMultiMap();

        fieldStoreTOLoadMap = Maps.newMultiMap();

        //处理静态字段
        for (Stmt stmt : icfg) {
            if (stmt instanceof StoreField storeField) {
                if (storeField.isStatic() && canHoldInt(storeField.getRValue())) {
                    staticFiledStore.put(storeField.getFieldRef().resolve(), storeField);
                }
            }
            if (stmt instanceof LoadField loadField) {
                if (loadField.isStatic() && canHoldInt(loadField.getLValue())) {
                    staticFiledLoad.put(loadField.getFieldRef().resolve(), loadField);
                }
            }
        }
        staticFiledStore.forEach((field, store) -> {
            for (LoadField load : staticFiledLoad.get(field)) {
                fieldStoreTOLoadMap.put(store, load);
            }
        });
        //处理实例字段 和 数组元素
        /*
        为什么数组需要双向映射？因为load语句在下表index变化时需要主动拉去store的信息，同时
        也保留store主动推送信息的能力。
         */
        MultiMap<Obj, Var> pointedBy = Maps.newMultiMap();
        arrayStoreToLoadMap = Maps.newMultiMap();
        arrayLoadToStoreMap = Maps.newMultiMap();

        for (Var v : pta.getVars()) {
            for (Obj obj : pta.getPointsToSet(v)) {
                pointedBy.put(obj, v);
            }
        }

        pointedBy.forEachSet(((obj, aliases) -> {
            for (Var v : aliases) {
                for (StoreField storeField : v.getStoreFields()) {
                    if (canHoldInt(storeField.getRValue())) {
                        JField f1 = storeField.getFieldRef().resolve();
                        for (Var u : aliases) {
                            for (LoadField loadField : u.getLoadFields()) {
                                JField f2 = loadField.getFieldRef().resolve();
                                if (f1.equals(f2)) {
                                    fieldStoreTOLoadMap.put(storeField, loadField);
                                }
                            }
                        }
                    }
                }
                for (StoreArray storeArray : v.getStoreArrays()) {
                    if (canHoldInt(storeArray.getRValue())) {
                        for (Var u : aliases) {
                            for (LoadArray loadArray : u.getLoadArrays()) {
                                arrayStoreToLoadMap.put(storeArray, loadArray);
                                arrayLoadToStoreMap.put(loadArray, storeArray);
                            }
                        }
                    }
                }
            }
        }));

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
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof StoreField storeField) {
            return transferStoreField(storeField, in, out);
        } else if (stmt instanceof LoadField loadField) {
            return transferLoadField(loadField, in, out);
        } else if(stmt instanceof StoreArray storeArray){
            return transferStoreArray(storeArray, in, out);
        } else if(stmt instanceof LoadArray loadArray){
            return transferLoadArray(loadArray, in, out);
        }
        return cp.transferNode(stmt, in, out);
    }

    private boolean isAlias(Value i1,Value i2) {
        if (!i1.isUndef() && !i2.isUndef()) {
            if (i1.isConstant() && i2.isConstant() && i1.equals(i2)
                    || i1.isNAC() || i2.isNAC()) {
                return true;
            }
        }
        return false;
    }

    private boolean transferLoadArray(LoadArray stmt, CPFact in, CPFact out) {
        boolean changed = false;
        Var lhs = stmt.getLValue();

        for (Var v : in.keySet()) {
            if (!v.equals(lhs)) {
                changed |=out.update(v, in.get(v));
            }
        }
        Value loadIndex = out.get(stmt.getArrayAccess().getIndex());
        for (StoreArray store : arrayLoadToStoreMap.get(stmt)) {
            CPFact storeOut = solver.getOutFact(store);
            Value storeIndex = storeOut.get(store.getArrayAccess().getIndex());
            if (isAlias(loadIndex, storeIndex)) {
                Value rValue = storeOut.get(store.getRValue());
                Value oldValue = out.get(stmt.getLValue());
                Value newValue = cp.meetValue(oldValue, rValue);
                if (out.update(stmt.getLValue(), newValue)) {
                    changed = true;
                }
            }
        }
        return changed;
    }

    private boolean transferStoreArray(StoreArray stmt, CPFact in, CPFact out) {
        boolean change = out.copyFrom(in);
        if (canHoldInt(stmt.getRValue())) {
            Value rValue = out.get(stmt.getRValue());
            Value storeIndex = out.get(stmt.getArrayAccess().getIndex());

            for (LoadArray load : arrayStoreToLoadMap.get(stmt)) {
                CPFact loadOut = solver.getOutFact(load);
                Value loadIndex = loadOut.get(load.getArrayAccess().getIndex());
                if (isAlias(loadIndex, storeIndex)) {
                    Value oldValue = solver.getOutFact(load).get(load.getLValue());
                    Value newValue = cp.meetValue(oldValue, rValue);
                    if (loadOut.update(load.getLValue(), newValue)) {
                        solver.propagate(load);
                    }
                }
            }
        }
        return change;
    }

    private boolean transferStoreField(StoreField stmt, CPFact in, CPFact out) {
        //store 不改变当前的out
        boolean change = out.copyFrom(in);
        if (canHoldInt(stmt.getRValue())) {
            Value rValue = in.get(stmt.getRValue());
            for (LoadField load : fieldStoreTOLoadMap.get(stmt)) {
                CPFact loadOut = solver.getOutFact(load);
                Value oldValue = loadOut.get(load.getLValue());
                Value newValue = cp.meetValue(oldValue, rValue);
                if (loadOut.update(load.getLValue(), newValue)) {
                    solver.propagate(load);
                }
            }
        }
        return change;
    }

    private boolean transferLoadField(LoadField stmt, CPFact in, CPFact out) {
        boolean changed = false;
        Var lhs = stmt.getLValue();
        for(Var inVar:in.keySet()){
            if(!inVar.equals(lhs)){
                changed|=out.update(inVar, in.get(inVar));
            }
        }
        return changed;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Invoke invoke = (Invoke) edge.getSource();
        Var lhs = invoke.getLValue();
        if (lhs != null) {
            CPFact newOut = out.copy();
            newOut.remove(lhs);
            return newOut;
        } else {
            return out;
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact targetIn = cp.newInitialFact();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        JMethod callee = edge.getCallee();
        for (int i = 0; i < invokeExp.getArgs().size(); i++) {
            Var argVar = invokeExp.getArgs().get(i);
            Var paramVar = callee.getIR().getParams().get(i);
            Value argValue = callSiteOut.get(argVar);
            targetIn.update(paramVar, argValue);
        }
        return targetIn;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        Var lhs = ((Invoke) edge.getCallSite()).getResult();
        CPFact result = newInitialFact();
        if (lhs != null && canHoldInt(lhs)) {
            Value retValue = edge.getReturnVars()
                    .stream()
                    .map(returnOut::get)
                    .reduce(Value.getUndef(), cp::meetValue);
            result.update(lhs, retValue);
        }
        return result;
    }
}
