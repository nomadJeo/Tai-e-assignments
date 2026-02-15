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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;
import java.util.Set;


/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (callGraph.reachableMethods.contains(method)) {
                continue;
            }
            callGraph.addReachableMethod(method);
            callGraph.callSitesIn(method).forEach(
                    callSite -> {
                        Set<JMethod> targets = resolve(callSite);
                        targets.forEach(
                                target -> {
                                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, target));
                                    worklist.add(target);
                                }
                        );
                    }
            );
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        Set<JMethod> targets = new java.util.HashSet<>();
        if (callSite.isStatic()) {
            targets.add(dispatch(methodRef.getDeclaringClass(), subsignature));
        } else if (callSite.isSpecial()) {
            JClass declaringClass = methodRef.getDeclaringClass();
            targets.add(dispatch(declaringClass, subsignature));
        } else {
            Set<JClass> possibleClasses = new java.util.HashSet<>();
            JClass declaringClass = methodRef.getDeclaringClass();
            if (callSite.isInterface()) {
                possibleClasses.addAll(getAllConcreteSubtypes(declaringClass));
            } else if (callSite.isVirtual()) {
                possibleClasses.add(declaringClass);
                possibleClasses.addAll(getAllSubclasses(declaringClass));
            }
            for (JClass possibleClass : possibleClasses) {
                JMethod method = dispatch(possibleClass, subsignature);
                if (method != null) {
                    targets.add(method);
                }
            }
        }
        return targets;
    }

    private Set<JClass> getAllConcreteSubtypes(JClass type) {
        Set<JClass> result = new java.util.HashSet<>();
        Queue<JClass> worklist = new ArrayDeque<>();
        worklist.add(type);

        while (!worklist.isEmpty()) {
            JClass current = worklist.poll();

            if (current.isInterface()) {

                Collection<JClass> impls =
                        hierarchy.getDirectImplementorsOf(current);
                worklist.addAll(impls);

                Collection<JClass> subInterfaces =
                        hierarchy.getDirectSubinterfacesOf(current);
                worklist.addAll(subInterfaces);

            } else {

                Collection<JClass> subclasses =
                        hierarchy.getDirectSubclassesOf(current);
                worklist.addAll(subclasses);

                if (!current.isAbstract()) {
                    result.add(current);
                }
            }
        }

        return result;
    }

    private Set<JClass> getAllSubclasses(JClass jclass) {
        Set<JClass> subclasses = new java.util.HashSet<>();
        Queue<JClass> worklist = new ArrayDeque<>();
        worklist.add(jclass);
        while (!worklist.isEmpty()) {
            JClass current = worklist.poll();
            Collection<JClass> directSubclasses = hierarchy.getDirectSubclassesOf(current);
            worklist.addAll(directSubclasses);
            if (!current.isAbstract()) {
                subclasses.add(current);
            }
        }
        return subclasses;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()) {
            return method;
        } else {
            JClass superClass = jclass.getSuperClass();
            if (superClass != null) {
                return dispatch(superClass, subsignature);
            }
        }
        return null;
    }
}
