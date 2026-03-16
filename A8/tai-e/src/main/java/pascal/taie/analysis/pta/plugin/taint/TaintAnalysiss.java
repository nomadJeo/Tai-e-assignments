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
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

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
    }

    // TODO - finish me
    public CSObj makeTaint(Invoke invoke, JMethod callee) {

        Type type = callee.getReturnType();
        Source source = new Source(callee, type);
        if(config.getSources().contains(source)){
            return csManager.getCSObj(emptyContext,manager.makeTaint(invoke, type));
        }
        return null;
    }
    /**
     * 处理由于 Base 变量变化引起的污点传播
     * @param taintObj 此时就是作为 Receiver 的污点对象
     */
    public void handleBaseProp(Invoke invoke, CSVar baseVar, CSObj taintObj) {
        Context callerCtx = baseVar.getContext();

        JMethod callee = solver.resolveCallee(taintObj, invoke);

        if (callee != null) {
            for (TaintTransfer transfer : config.getTransfers()) {
                if (transfer.method().equals(callee) && transfer.from() == TaintTransfer.BASE) {
                    applyTransfer(invoke, callerCtx, transfer, taintObj);
                }
            }
        }
    }

    public void handleArgProp(Invoke invoke, CSVar argVar, CSObj taintObj) {
        Context callerCtx = argVar.getContext();
        InvokeExp invokeExp = invoke.getInvokeExp();

        int argIndex = -1;
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            if (argVar.equals(csManager.getCSVar(callerCtx, invokeExp.getArg(i)))) {
                argIndex = i;
                break;
            }
        }
        if (argIndex == -1) return;

        CSCallSite csCallSite = csManager.getCSCallSite(callerCtx, invoke);
        for (CSMethod method : solver.getCallGraph().getCalleesOf(csCallSite)) {
            JMethod callee = method.getMethod();

            for (TaintTransfer transfer : config.getTransfers()) {
                if (transfer.method().equals(callee) && transfer.from() == argIndex) {
                    applyTransfer(invoke, callerCtx, transfer, taintObj);
                }
            }
        }
    }

    /**
     * 当 Base 变量获得新对象，解析出新的被调用者时，
     * 回头检查参数集合中是否已经存在污点对象，防止时序丢失。
     */
    public void checkExistingArgsForNewBase(Invoke invoke, CSVar baseVar, CSObj baseObj) {
        Context callerCtx = baseVar.getContext();

        JMethod callee = solver.resolveCallee(baseObj, invoke);
        if (callee == null) return;

        InvokeExp invokeExp = invoke.getInvokeExp();
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            CSVar argVar = csManager.getCSVar(callerCtx, invokeExp.getArg(i));

            PointsToSet argPts = argVar.getPointsToSet();

            for (CSObj argObj : argPts) {
                if (isTaint(argObj)) {

                    for (TaintTransfer transfer : config.getTransfers()) {
                        if (transfer.method().equals(callee) && transfer.from() == i) {
                            applyTransfer(invoke, callerCtx, transfer, argObj);
                        }
                    }
                }
            }
        }
    }


    private void applyTransfer(Invoke invoke, Context ctx, TaintTransfer transfer, CSObj taintObj) {
        CSVar toVar = null;
        if (transfer.to() == TaintTransfer.RESULT) {
            Var lValue = invoke.getLValue();
            if (lValue != null) toVar = csManager.getCSVar(ctx, lValue);
        } else if (transfer.to() == TaintTransfer.BASE) {
            Var base = ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
            toVar = csManager.getCSVar(ctx, base);
        }

        if (toVar != null) {
            Invoke sourceCall = manager.getSourceCall(taintObj.getObject());
            Obj newTaint = manager.makeTaint(sourceCall, transfer.type());
            CSObj newCSObj = csManager.getCSObj(ctx, newTaint);
            // 触发 WorkList 增量更新
            solver.addEntry(toVar, PointsToSetFactory.make(newCSObj));
        }
    }

    public boolean isTaint(CSObj obj) {
        return manager.isTaint(obj.getObject());
    }


    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        PointerAnalysisResult result = solver.getResult();
        Set<TaintFlow> taintFlows = new TreeSet<>();

        // 遍历所有上下文敏感方法
        for (CSMethod csMethod : result.getCSCallGraph().getNodes()) {

            Context context = csMethod.getContext();
            JMethod method = csMethod.getMethod();

            if (method.getIR() == null) {
                continue;
            }

            // 遍历方法中的所有语句
            for (Stmt stmt : method.getIR().getStmts()) {

                if (!(stmt instanceof Invoke invoke)) {
                    continue;
                }

                InvokeExp invokeExp = invoke.getInvokeExp();
                JMethod callee = invokeExp.getMethodRef().resolve();

                int argCount = invokeExp.getArgCount();

                // 检查每个参数位置是否是 sink
                for (int i = 0; i < argCount; i++) {

                    Sink sink = new Sink(callee, i);

                    if (!config.getSinks().contains(sink)) {
                        continue;
                    }

                    Var arg = invokeExp.getArg(i);

                    // 获取 context-sensitive 变量
                    CSVar csVar = csManager.getCSVar(context, arg);

                    if (csVar == null) {
                        continue;
                    }

                    // 查看该变量的 points-to 集
                    for (CSObj obj : result.getPointsToSet(csVar)) {

                        Obj baseObj = obj.getObject();

                        // 如果是 taint object
                        if (manager.isTaint(baseObj)) {

                            Invoke sourceCall = manager.getSourceCall(baseObj);

                            taintFlows.add(
                                    new TaintFlow(sourceCall, invoke, i)
                            );
                        }
                    }
                }
            }
        }

        return taintFlows;
    }
}
