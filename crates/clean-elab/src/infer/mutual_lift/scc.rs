// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The call graph of a `mutual` block's pre-definitions and its strongly
//! connected components (design `designs/2026-10-08-mutual-nested-recursion.md`
//! §5.2).
//!
//! An edge `i → j` means member `i`'s pre-definition (type or value) mentions
//! member `j`'s forward-declared local. A component is RECURSIVE when it has
//! more than one member or its only member mentions itself; only those go to
//! the structural lift. The registration order is a topological order of the
//! components (callees first), ties broken by source order, so a block whose
//! source order is already a dependency order is registered exactly as before.

use clean_kernel::{Expr, ExprVisitor, FVarId};
use std::collections::HashSet;

/// Collects which of a fixed set of forward locals an expression mentions.
struct ForwardLocalFinder<'t> {
    targets: &'t [FVarId],
    found: HashSet<usize>,
}

impl ExprVisitor for ForwardLocalFinder<'_> {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_fvar(&mut self, id: FVarId) {
        if let Some(index) = self.targets.iter().position(|target| *target == id) {
            self.found.insert(index);
        }
    }
}

/// The indices of `forward` (member forward locals) that occur in `exprs`.
pub(super) fn mentioned_members(forward: &[FVarId], exprs: &[&Expr]) -> HashSet<usize> {
    let mut finder = ForwardLocalFinder {
        targets: forward,
        found: HashSet::new(),
    };
    for expr in exprs {
        finder.visit_expr(expr);
    }
    finder.found
}

/// Every free variable of `expr`.
pub(super) fn free_fvars(expr: &Expr) -> HashSet<FVarId> {
    struct All(HashSet<FVarId>);
    impl ExprVisitor for All {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            self.0.insert(id);
        }
    }
    let mut all = All(HashSet::new());
    all.visit_expr(expr);
    all.0
}

/// One strongly connected component of the call graph, members in source
/// order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Component {
    pub(super) members: Vec<usize>,
    /// More than one member, or one member that mentions itself.
    pub(super) recursive: bool,
}

/// Tarjan's algorithm over `edges` (adjacency lists by member index), then
/// a topological order of the condensation with callees first and ties
/// broken by the smallest source index in each component.
pub(super) fn components_in_dependency_order(edges: &[Vec<usize>]) -> Vec<Component> {
    let n = edges.len();
    let comp_of = tarjan(edges);
    let num_comps = comp_of.iter().copied().max().map_or(0, |max| max + 1);
    let mut members: Vec<Vec<usize>> = vec![Vec::new(); num_comps];
    for (node, comp) in comp_of.iter().enumerate() {
        members[*comp].push(node);
    }
    // Condensation: `deps[c]` = components `c` calls (other than itself).
    let mut deps: Vec<HashSet<usize>> = vec![HashSet::new(); num_comps];
    let mut self_loop = vec![false; num_comps];
    for (node, targets) in edges.iter().enumerate() {
        for target in targets {
            let (from, to) = (comp_of[node], comp_of[*target]);
            if from == to {
                if node == *target || members[from].len() > 1 {
                    self_loop[from] = true;
                }
            } else {
                deps[from].insert(to);
            }
        }
    }
    // Kahn's algorithm: repeatedly emit the ready component (all of its
    // callees emitted) with the smallest source index.
    let mut emitted = vec![false; num_comps];
    let mut order = Vec::with_capacity(num_comps);
    while order.len() < num_comps {
        let next = (0..num_comps)
            .filter(|c| !emitted[*c] && deps[*c].iter().all(|d| emitted[*d]))
            .min_by_key(|c| members[*c].first().copied().unwrap_or(n));
        let Some(next) = next else {
            break; // unreachable: the condensation of a graph is acyclic
        };
        emitted[next] = true;
        order.push(Component {
            members: members[next].clone(),
            recursive: members[next].len() > 1 || self_loop[next],
        });
    }
    order
}

/// Component index of every node (Tarjan, iterative to stay stack-safe).
fn tarjan(edges: &[Vec<usize>]) -> Vec<usize> {
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut comp = vec![usize::MAX; n];
    let mut next_index = 0usize;
    let mut next_comp = 0usize;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, next edge position)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some((node, pos)) = work.pop() {
            if let Some(&succ) = edges[node].get(pos) {
                work.push((node, pos + 1));
                if index[succ] == usize::MAX {
                    index[succ] = next_index;
                    low[succ] = next_index;
                    next_index += 1;
                    stack.push(succ);
                    on_stack[succ] = true;
                    work.push((succ, 0));
                } else if on_stack[succ] {
                    low[node] = low[node].min(index[succ]);
                }
                continue;
            }
            if low[node] == index[node] {
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    comp[member] = next_comp;
                    if member == node {
                        break;
                    }
                }
                next_comp += 1;
            }
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[node]);
            }
        }
    }
    comp
}

#[cfg(test)]
mod tests {
    use super::*;

    fn comps(edges: &[Vec<usize>]) -> Vec<(Vec<usize>, bool)> {
        components_in_dependency_order(edges)
            .into_iter()
            .map(|c| (c.members, c.recursive))
            .collect()
    }

    #[test]
    fn test_scc_independent_members_keep_source_order() {
        assert_eq!(
            comps(&[vec![], vec![]]),
            vec![(vec![0], false), (vec![1], false)]
        );
    }

    #[test]
    fn test_scc_first_member_naming_second_is_registered_after_it() {
        assert_eq!(
            comps(&[vec![1], vec![]]),
            vec![(vec![1], false), (vec![0], false)]
        );
    }

    #[test]
    fn test_scc_mutual_pair_is_one_recursive_component() {
        assert_eq!(comps(&[vec![1], vec![0, 1]]), vec![(vec![0, 1], true)]);
    }

    #[test]
    fn test_scc_self_loop_is_recursive() {
        assert_eq!(
            comps(&[vec![0], vec![0]]),
            vec![(vec![0], true), (vec![1], false)]
        );
    }

    #[test]
    fn test_scc_non_recursive_helper_before_its_recursive_users() {
        // 0 is a helper; 1 and 2 are mutually recursive and call 0.
        assert_eq!(
            comps(&[vec![], vec![2, 0], vec![1]]),
            vec![(vec![0], false), (vec![1, 2], true)]
        );
        // The helper declared LAST is still registered first.
        assert_eq!(
            comps(&[vec![1, 2], vec![0], vec![]]),
            vec![(vec![2], false), (vec![0, 1], true)]
        );
    }
}
