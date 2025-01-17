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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.Edge;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> qe = new LinkedList<>();
        Set<Node> vis = new HashSet<>();
        Node entry = cfg.getEntry();
        for (Node node : cfg) {
            qe.add(node);
            vis.add(node);
        }

        while (!qe.isEmpty()) {
            Node node = qe.remove();
            vis.remove(node);
            Set<Edge<Node>> in_edges = cfg.getInEdgesOf(node);
            Fact new_in = analysis.newInitialFact();
            for (Edge<Node> edge : in_edges) {
                Node in_node = edge.getSource();
                analysis.meetInto(result.getOutFact(in_node), new_in);
            }
            if (analysis.transferNode(node, new_in, result.getOutFact(node))) {
                Set<Edge<Node>> out_edges = cfg.getOutEdgesOf(node);
                for (Edge<Node> edge : out_edges) {
                    Node out_node = edge.getTarget();
                    if (!vis.contains(out_node)) {
                        vis.add(out_node);
                        qe.add(out_node);
                    }
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean need_continue = true;
        while (need_continue) {
            need_continue = false;
            for (Node node : cfg) {
                if (cfg.isEntry(node) || cfg.isExit(node))  continue;
                Fact new_out = analysis.newBoundaryFact(cfg);
                Set<Edge<Node>> out_edges = cfg.getOutEdgesOf(node);
                for (Edge<Node> edge : out_edges) {
                    Node target = edge.getTarget();
                    analysis.meetInto(result.getInFact(target), new_out);
                }
                result.setOutFact(node, new_out);
                need_continue = analysis.transferNode(node, result.getInFact(node), new_out) || need_continue;
            }
        }
    }
}
