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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import static pascal.taie.analysis.graph.callgraph.CallGraphs.getCallKind;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;
    private DefaultCallGraph callGraph;
    private PointerFlowGraph pointerFlowGraph;
    private WorkList workList;
    private StmtProcessor stmtProcessor;
    private ClassHierarchy hierarchy;
    private MultiMap<Var, LoadField> loads;
    private MultiMap<Var, StoreField> stores;
    private MultiMap<Var, StoreArray> arrayStores;
    private MultiMap<Var, LoadArray> arrayLoads;
    private MultiMap<Var, Invoke> instanceCalls;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        stores = Maps.newMultiMap();
        loads = Maps.newMultiMap();
        arrayStores = Maps.newMultiMap();
        arrayLoads = Maps.newMultiMap();
        instanceCalls = Maps.newMultiMap();

        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // callGraph don't contain method,then analyze method.
        if (callGraph.addReachableMethod(method)) {
            var ir = method.getIR();
            ir.getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet sourcePts = source.getPointsToSet();
            if (sourcePts != null && !sourcePts.isEmpty()) {
                workList.addEntry(target, sourcePts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet difference = propagate(pointer, entry.pointsToSet());

            if (difference.isEmpty()) {
                continue;
            }

            if (pointer instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                for (Obj obj : difference) {
                    // y = x.f -> add edge (obj.f -> y)
                    if (loads.containsKey(x)) {
                        processLoad(x, obj);
                    }
                    // x.f = z -> add edge (z -> obj.f)
                    if (stores.containsKey(x)) {
                        processStore(x, obj);
                    }
                    if (arrayLoads.containsKey(x)) {
                        for (LoadArray load : arrayLoads.get(x)) {
                            Pointer loadPtr = pointerFlowGraph.getArrayIndex(obj);
                            Pointer yPtr = pointerFlowGraph.getVarPtr(load.getLValue());
                            addPFGEdge(loadPtr, yPtr);
                        }
                    }
                    if (arrayStores.containsKey(x)) {
                        for (StoreArray store : arrayStores.get(x)) {
                            Pointer storePtr = pointerFlowGraph.getArrayIndex(obj);
                            Pointer zPtr = pointerFlowGraph.getVarPtr(store.getRValue());
                            addPFGEdge(zPtr, storePtr);
                        }
                    }
                    // process call x.m(...)
                    if (instanceCalls.containsKey(x)) {
                        processCall(x, obj);
                    }
                }
            }
        }
    }

    private void processLoad(Var base, Obj obj) {
        for (LoadField load : loads.get(base)) {
            Pointer yPtr = pointerFlowGraph.getVarPtr(load.getLValue());
            Pointer loadPtr = pointerFlowGraph.getInstanceField(obj, load.getFieldRef().resolve());
            addPFGEdge(loadPtr, yPtr);
        }
    }

    private void processStore(Var base, Obj obj) {
        for (StoreField store : stores.get(base)) {
            Pointer zPtr = pointerFlowGraph.getVarPtr(store.getRValue());
            Pointer storePtr = pointerFlowGraph.getInstanceField(obj, store.getFieldRef().resolve());
            addPFGEdge(zPtr, storePtr);
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet oldPointsToSet = pointer.getPointsToSet();
        PointsToSet difference = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!oldPointsToSet.contains(obj)) {
                difference.addObject(obj);
                oldPointsToSet.addObject(obj);
            }
        }
        if(!difference.isEmpty()){
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, difference);
            }
        }
        return difference;
    }

    //不考虑参数类型是否为引用类型
    private void transferParams(JMethod callee, Invoke callSite) {
        for (int i = 0; i < callSite.getInvokeExp().getArgCount(); i++) {
            Var arg = callSite.getInvokeExp().getArg(i);
            Var param = callee.getIR().getParam(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke callSite : instanceCalls.get(var)) {
            JMethod callee = resolveCallee(recv, callSite);
            if (callee == null) continue;

            Pointer thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(thisPtr, new PointsToSet(recv));

            if (callGraph.addEdge(new Edge<>(getCallKind(callSite), callSite, callee))) {
                addReachable(callee);

                transferParams(callee, callSite);

                Var lhs = callSite.getLValue();
                if (lhs != null) {
                    for (Var ret : callee.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lhs));
                    }
                }
            }
        }
    }

    private void processStaticCall(Invoke stmt) {
        JMethod callee = resolveCallee(null, stmt);
        if (callee != null) {
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))) {
                addReachable(callee);
            }

            transferParams(callee, stmt);

            Var lhs = stmt.getLValue();
            if (lhs != null) {
                for (Var ret : callee.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lhs));
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
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // TODO - finish me
            Var lhs = stmt.getLValue();
            Pointer lhsPtr = pointerFlowGraph.getVarPtr(lhs);
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(lhsPtr, new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // TODO - finish me
            Pointer lhsPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer rhsPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(rhsPtr, lhsPtr);
            return null;
        }

        // x = y.f || x = T.f
        @Override
        public Void visit(LoadField stmt) {
            // TODO - finish me
            FieldAccess fieldAccess = stmt.getFieldAccess();
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                Var base = instanceFieldAccess.getBase();
                loads.put(base, stmt);
            } else if (fieldAccess instanceof StaticFieldAccess staticFieldAccess) {
                StaticField staticField = pointerFlowGraph.getStaticField(staticFieldAccess.getFieldRef().resolve());
                Pointer lhsPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                addPFGEdge(staticField, lhsPtr);
            }
            return null;
        }

        // o.f = x || T.f = x
        @Override
        public Void visit(StoreField stmt) {
            // TODO - finish me
            FieldAccess fieldAccess = stmt.getFieldAccess();
            if (fieldAccess instanceof InstanceFieldAccess instanceFieldAccess) {
                Var base = instanceFieldAccess.getBase();
                stores.put(base, stmt);
            } else if (fieldAccess instanceof StaticFieldAccess staticFieldAccess) {
                StaticField staticField = pointerFlowGraph.getStaticField(staticFieldAccess.getFieldRef().resolve());
                Pointer rhsPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(rhsPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            Var base = stmt.getArrayAccess().getBase();
            arrayStores.put(base, stmt);
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) {
            Var base = stmt.getArrayAccess().getBase();
            arrayLoads.put(base, stmt);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                processStaticCall(stmt);
            } else {
                InvokeInstanceExp invokeExp = (InvokeInstanceExp) stmt.getInvokeExp();
                Var base = invokeExp.getBase();
                instanceCalls.put(base, stmt);
            }
            return null;
        }
    }
}
