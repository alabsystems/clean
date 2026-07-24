// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Directed dependency graph for mutual declaration analysis.
//!
//! Provides cycle detection, topological sorting, and strongly connected
//! component (SCC) computation for declaration dependency graphs.

// ─────────────────────────────────────────────────────────────────────────────
// DependencyGraph
// ─────────────────────────────────────────────────────────────────────────────

/// Directed dependency graph between declarations in a mutual block.
///
/// Edges represent "declaration A references declaration B in its body".
/// Indices correspond to positions in the parent [`MutualBlock::declarations`]
/// vector.
#[derive(Debug, Clone, Default)]
pub(crate) struct DependencyGraph {
    /// (from, to) index pairs. Both indices are into the declarations vec.
    pub(crate) edges: Vec<(usize, usize)>,
}

impl DependencyGraph {
    /// Create an empty dependency graph.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self { edges: Vec::new() }
    }

    /// Add a directed edge from declaration `from` to declaration `to`.
    pub(crate) fn add_edge(&mut self, from: usize, to: usize) {
        self.edges.push((from, to));
    }

    /// Return the set of direct successors (dependencies) of `node`.
    #[must_use]
    pub(crate) fn successors(&self, node: usize) -> Vec<usize> {
        self.edges
            .iter()
            .filter(|(f, _)| *f == node)
            .map(|(_, t)| *t)
            .collect()
    }

    /// Check whether the graph contains a cycle.
    ///
    /// Uses iterative DFS with three-colour marking:
    /// - White (unvisited), Grey (on current path), Black (fully explored).
    ///
    /// Returns `Some(cycle)` with the node indices forming a cycle, or `None`
    /// if the graph is acyclic.
    #[must_use]
    pub(crate) fn find_cycle(&self, num_nodes: usize) -> Option<Vec<usize>> {
        find_cycle_dfs(&self.edges, num_nodes, |node| self.successors(node))
    }

    /// Compute a topological ordering of the nodes.
    ///
    /// Returns `Ok(order)` with indices in dependency-first order, or
    /// `Err(cycle)` if the graph contains a cycle.
    pub(crate) fn topological_sort(&self, num_nodes: usize) -> Result<Vec<usize>, Vec<usize>> {
        if let Some(cycle) = self.find_cycle(num_nodes) {
            return Err(cycle);
        }
        Ok(kahn_topological_sort(&self.edges, num_nodes, |node| {
            self.successors(node)
        }))
    }

    /// Return the number of strongly connected components with size > 1.
    ///
    /// A mutual block is well-formed only if these SCCs are all explicitly
    /// marked with termination measures or are accepted by the structural
    /// recursion checker.
    #[must_use]
    pub(crate) fn num_nontrivial_sccs(&self, num_nodes: usize) -> usize {
        let sccs = tarjan_sccs_iterative(num_nodes, |node| self.successors(node));
        sccs.iter().filter(|scc| scc.len() > 1).count()
    }

    /// Compute all strongly connected components via Tarjan's algorithm.
    ///
    /// Returns a list of SCCs, each being a vector of node indices. SCCs of
    /// size 1 without a self-loop are non-recursive singletons.
    #[must_use]
    pub(crate) fn compute_sccs(&self, num_nodes: usize) -> Vec<Vec<usize>> {
        tarjan_sccs_iterative(num_nodes, |node| self.successors(node))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Graph algorithms (free functions)
// ─────────────────────────────────────────────────────────────────────────────

/// Iterative DFS cycle detection with three-colour marking.
fn find_cycle_dfs(
    _edges: &[(usize, usize)],
    num_nodes: usize,
    successors: impl Fn(usize) -> Vec<usize>,
) -> Option<Vec<usize>> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Colour {
        White,
        Grey,
        Black,
    }

    let mut colour = vec![Colour::White; num_nodes];
    let mut parent = vec![usize::MAX; num_nodes];

    for start in 0..num_nodes {
        if colour[start] != Colour::White {
            continue;
        }

        let mut stack: Vec<(usize, bool)> = vec![(start, true)];

        while let Some((node, entering)) = stack.pop() {
            if !entering {
                colour[node] = Colour::Black;
                continue;
            }
            if colour[node] == Colour::Grey {
                continue;
            }

            colour[node] = Colour::Grey;
            stack.push((node, false));

            for succ in successors(node) {
                if colour[succ] == Colour::Grey {
                    let mut cycle = vec![succ, node];
                    let mut cur = node;
                    while cur != succ && parent[cur] != usize::MAX {
                        cur = parent[cur];
                        if cur != succ {
                            cycle.push(cur);
                        }
                    }
                    cycle.push(succ);
                    cycle.reverse();
                    return Some(cycle);
                }
                if colour[succ] == Colour::White {
                    parent[succ] = node;
                    stack.push((succ, true));
                }
            }
        }
    }

    None
}

/// Kahn's algorithm for topological sorting (assumes no cycles).
fn kahn_topological_sort(
    edges: &[(usize, usize)],
    num_nodes: usize,
    successors: impl Fn(usize) -> Vec<usize>,
) -> Vec<usize> {
    let mut in_degree = vec![0u32; num_nodes];
    for &(_, to) in edges {
        if to < num_nodes {
            in_degree[to] += 1;
        }
    }

    let mut queue: Vec<usize> = (0..num_nodes).filter(|&i| in_degree[i] == 0).collect();
    let mut order = Vec::with_capacity(num_nodes);

    while let Some(node) = queue.pop() {
        order.push(node);
        for succ in successors(node) {
            if succ < num_nodes {
                in_degree[succ] -= 1;
                if in_degree[succ] == 0 {
                    queue.push(succ);
                }
            }
        }
    }

    order
}

/// Iterative Tarjan's SCC algorithm.
fn tarjan_sccs_iterative(
    num_nodes: usize,
    successors: impl Fn(usize) -> Vec<usize>,
) -> Vec<Vec<usize>> {
    let mut index_counter: usize = 0;
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; num_nodes];
    let mut indices = vec![usize::MAX; num_nodes];
    let mut lowlinks = vec![usize::MAX; num_nodes];
    let mut result: Vec<Vec<usize>> = Vec::new();

    for v in 0..num_nodes {
        if indices[v] != usize::MAX {
            continue;
        }

        let mut dfs_stack: Vec<(usize, usize)> = vec![(v, 0)];
        indices[v] = index_counter;
        lowlinks[v] = index_counter;
        index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        while let Some(&mut (node, ref mut succ_idx)) = dfs_stack.last_mut() {
            let succs = successors(node);
            if *succ_idx < succs.len() {
                let w = succs[*succ_idx];
                *succ_idx += 1;

                if w >= num_nodes {
                    continue;
                }

                if indices[w] == usize::MAX {
                    indices[w] = index_counter;
                    lowlinks[w] = index_counter;
                    index_counter += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    dfs_stack.push((w, 0));
                } else if on_stack[w] {
                    lowlinks[node] = lowlinks[node].min(indices[w]);
                }
            } else {
                if lowlinks[node] == indices[node] {
                    let mut scc = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        scc.push(w);
                        if w == node {
                            break;
                        }
                    }
                    result.push(scc);
                }

                dfs_stack.pop();
                if let Some(&mut (parent_node, _)) = dfs_stack.last_mut() {
                    lowlinks[parent_node] = lowlinks[parent_node].min(lowlinks[node]);
                }
            }
        }
    }

    result
}
