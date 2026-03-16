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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import static pascal.taie.analysis.graph.callgraph.CallGraphs.getCallKind;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;
    private MultiMap<CSVar, LoadField> loads;
    private MultiMap<CSVar, StoreField> stores;
    private MultiMap<CSVar, StoreArray> arrayStores;
    private MultiMap<CSVar, LoadArray> arrayLoads;
    private MultiMap<CSVar, Invoke> instanceCalls;
    private MultiMap<CSVar, Invoke> argumentToCalls;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        loads = Maps.newMultiMap();
        stores = Maps.newMultiMap();
        arrayStores = Maps.newMultiMap();
        arrayLoads = Maps.newMultiMap();
        instanceCalls = Maps.newMultiMap();
        argumentToCalls = Maps.newMultiMap();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    public void addEntry(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    public void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (source.getPointsToSet() != null && !source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer cur = entry.pointer();
            PointsToSet curPts = entry.pointsToSet();
            PointsToSet difference = propagate(cur, curPts);
            if (!difference.isEmpty() && cur instanceof CSVar csVar) {
                for (CSObj csObj : difference) {
                    if (loads.containsKey(csVar)) {
                        for (LoadField load : loads.get(csVar)) {
                            InstanceField instanceField = csManager.getInstanceField(csObj, load.getFieldRef().resolve());
                            CSVar target = csManager.getCSVar(csVar.getContext(), load.getLValue());
                            addPFGEdge(instanceField, target);
                        }
                    }
                    if (stores.containsKey(csVar)) {
                        for (StoreField store : stores.get(csVar)) {
                            InstanceField instanceField = csManager.getInstanceField(csObj, store.getFieldRef().resolve());
                            CSVar source = csManager.getCSVar(csVar.getContext(), store.getRValue());
                            addPFGEdge(source, instanceField);
                        }
                    }
                    if (arrayLoads.containsKey(csVar)) {
                        for (LoadArray load : arrayLoads.get(csVar)) {
                            ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                            CSVar target = csManager.getCSVar(csVar.getContext(), load.getLValue());
                            addPFGEdge(arrayIndex, target);
                        }
                    }
                    if (arrayStores.containsKey(csVar)) {
                        for (StoreArray store : arrayStores.get(csVar)) {
                            ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                            CSVar source = csManager.getCSVar(csVar.getContext(), store.getRValue());
                            addPFGEdge(source, arrayIndex);
                        }
                    }
                    if (instanceCalls.containsKey(csVar)) {
                        processCall(csVar, csObj);

                        for (Invoke invoke : instanceCalls.get(csVar)) {
                            if (taintAnalysis.isTaint(csObj)) {
                                taintAnalysis.handleBaseProp(invoke, csVar, csObj);
                            }
                            taintAnalysis.checkExistingArgsForNewBase(invoke, csVar, csObj);
                        }
                    }
                    if (taintAnalysis.isTaint(csObj) && argumentToCalls.containsKey(csVar)) {
                        for (Invoke invoke : argumentToCalls.get(csVar)) {
                            taintAnalysis.handleArgProp(invoke, csVar, csObj);
                        }
                    }
                }
            }
        }
    }

    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet oldPointsToSet = pointer.getPointsToSet();
        PointsToSet difference = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
            if (!oldPointsToSet.contains(obj)) {
                difference.addObject(obj);
                oldPointsToSet.addObject(obj);
            }
        }
        if (!difference.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, difference);
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke callSite : instanceCalls.get(recv)) {
            //dispatch method
            JMethod callee = resolveCallee(recvObj, callSite);

            Var lValue = callSite.getLValue();
            CSVar r = (lValue != null) ? csManager.getCSVar(recv.getContext(), lValue) : null;

            if (callee != null) {
                CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
                Context newContext = contextSelector.selectContext(csCallSite, recvObj, callee);
                CSMethod csCallee = csManager.getCSMethod(newContext, callee);
                //处理this指针
                CSVar thisPtr = csManager.getCSVar(newContext, callee.getIR().getThis());
                workList.addEntry(thisPtr, PointsToSetFactory.make(recvObj));


                if (callGraph.addEdge(new Edge<>(getCallKind(callSite), csCallSite, csCallee))) {
                    addReachable(csCallee);
                    //处理参数
                    for (int i = 0; i < callSite.getInvokeExp().getArgCount(); i++) {
                        Var arg = callSite.getInvokeExp().getArg(i);
                        Pointer argPtr = csManager.getCSVar(recv.getContext(), arg);
                        Var param = callee.getIR().getParam(i);
                        Pointer paramPtr = csManager.getCSVar(newContext, param);
                        addPFGEdge(argPtr, paramPtr);
                    }

                    if (lValue != null) {
                        if (r != null) {
                            for (Var ret : callee.getIR().getReturnVars()) {
                                CSVar retPtr = csManager.getCSVar(newContext, ret);
                                addPFGEdge(retPtr, r);
                            }
                        }
                        CSObj taintObj = taintAnalysis.makeTaint(callSite, callee);
                        if (taintObj != null) {
                            workList.addEntry(r, PointsToSetFactory.make(taintObj));
                        }
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            Var var = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);

            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj newObj = csManager.getCSObj(heapContext, obj);

            Pointer newPtr = csManager.getCSVar(context, var);
            workList.addEntry(newPtr, PointsToSetFactory.make(newObj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var left = stmt.getLValue();
            Var right = stmt.getRValue();
            Pointer leftPtr = csManager.getCSVar(context, left);
            Pointer rightPtr = csManager.getCSVar(context, right);
            addPFGEdge(rightPtr, leftPtr);
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
            arrayLoads.put(base, stmt);
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            CSVar base = csManager.getCSVar(context, stmt.getArrayAccess().getBase());
            arrayStores.put(base, stmt);
            return null;
        }

        //x = y.f or x = C.f
        @Override
        public Void visit(LoadField stmt) {
            FieldAccess fieldAccess = stmt.getFieldAccess();
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                CSVar baseVar = csManager.getCSVar(context, instanceFieldAccess.getBase());
                loads.put(baseVar, stmt);
            } else if (fieldAccess instanceof StaticFieldAccess staticFieldAccess) {
                StaticField staticField = csManager.getStaticField(staticFieldAccess.getFieldRef().resolve());
                Pointer target = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(staticField, target);
            }
            return null;
        }

        // y.f = x or C.f = x
        @Override
        public Void visit(StoreField stmt) {
            FieldAccess fieldAccess = stmt.getFieldAccess();
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                CSVar baseVar = csManager.getCSVar(context, instanceFieldAccess.getBase());
                stores.put(baseVar, stmt);
            } else if (fieldAccess instanceof StaticFieldAccess staticFieldAccess) {
                StaticField staticField = csManager.getStaticField(staticFieldAccess.getFieldRef().resolve());
                Pointer source = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(source, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context newContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(newContext, callee);
                //对于静态调用，直接添加调用图边，并将callee方法加入可达方法集合
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))) {
                    addReachable(csCallee);
                }
                //处理参数
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    Var arg = stmt.getInvokeExp().getArg(i);
                    CSVar argPtr = csManager.getCSVar(context, arg);
                    Var param = callee.getIR().getParam(i);
                    Pointer paramPtr = csManager.getCSVar(newContext, param);
                    addPFGEdge(argPtr, paramPtr);
                    //静态调用可能触发arg-to-result的污点传播
                    argumentToCalls.put(argPtr, stmt);
                }
                //处理返回值
                Var lValue = stmt.getLValue();
                if (lValue != null) {
                    CSVar r = csManager.getCSVar(context, lValue);
                    if (r != null) {
                        for (Var ret : callee.getIR().getReturnVars()) {
                            Pointer retPtr = csManager.getCSVar(newContext, ret);
                            addPFGEdge(retPtr, r);
                        }
                        //处理taint
                        CSObj taintObj = taintAnalysis.makeTaint(stmt, callee);
                        if (taintObj != null) {
                            workList.addEntry(r, PointsToSetFactory.make(taintObj));
                        }
                    }
                }
            } else {
                InvokeInstanceExp invokeInstanceExp = (InvokeInstanceExp) stmt.getInvokeExp();
                CSVar recvVar = csManager.getCSVar(context, invokeInstanceExp.getBase());
                instanceCalls.put(recvVar, stmt);
                //参数也可能导致传播
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    Var arg = stmt.getInvokeExp().getArg(i);
                    CSVar argPtr = csManager.getCSVar(context, arg);
                    argumentToCalls.put(argPtr, stmt);
                }
            }
            return null;
        }
    }
}
