// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Congruence closure tactic
//!
//! Provides the `cc` tactic for proving equalities using congruence closure.

use std::collections::HashMap;

use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::{match_eq_simple, rfl, ProofState, TacticError, TacticResult};
use crate::stack_safe;

// ============================================================================
// CC (Congruence Closure) Tactic
// ============================================================================

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CCConfig {
    pub max_iterations: usize,
    pub verbose: bool,
}

impl Default for CCConfig {
    fn default() -> Self {
        Self {
            max_iterations: 1000,
            verbose: false,
        }
    }
}

pub(crate) struct CCState {
    parent: HashMap<usize, usize>,
    rank: HashMap<usize, usize>,
    expr_to_id: HashMap<Expr, usize>,
    id_to_expr: Vec<Expr>,
    pending: Vec<(usize, usize)>,
    use_list: HashMap<usize, Vec<usize>>,
}

impl CCState {
    /// ENSURES: Returns an empty union-find state with no registered expressions.
    pub(crate) fn new() -> Self {
        Self {
            parent: HashMap::new(),
            rank: HashMap::new(),
            expr_to_id: HashMap::new(),
            id_to_expr: Vec::new(),
            pending: Vec::new(),
            use_list: HashMap::new(),
        }
    }

    /// REQUIRES: `expr` is a well-formed kernel expression.
    /// ENSURES: Returns a unique ID for `expr`; same `expr` always returns same ID.
    /// ENSURES: For `App(f, a)`, recursively registers `f` and `a` and adds
    ///   use-list entries so congruence propagation can find them.
    pub(crate) fn add_expr(&mut self, expr: &Expr) -> usize {
        stack_safe(|| {
            if let Some(&id) = self.expr_to_id.get(expr) {
                return id;
            }

            let id = self.id_to_expr.len();
            self.expr_to_id.insert(expr.clone(), id);
            self.id_to_expr.push(expr.clone());
            self.parent.insert(id, id);
            self.rank.insert(id, 0);

            if let ExprKind::App(f, a) = expr.kind() {
                let f_id = self.add_expr(f);
                let a_id = self.add_expr(a);
                self.use_list.entry(f_id).or_default().push(id);
                self.use_list.entry(a_id).or_default().push(id);
            }
            id
        })
    }

    /// REQUIRES: `x` was returned by a prior `add_expr` call on this state.
    /// ENSURES: Returns the canonical root representative for `x`'s equivalence class.
    /// ENSURES: Path compression is applied (amortized near-O(1)).
    pub(crate) fn find(&mut self, mut x: usize) -> usize {
        let mut root = x;
        while self.parent[&root] != root {
            root = self.parent[&root];
        }
        while self.parent[&x] != root {
            let next = self.parent[&x];
            self.parent.insert(x, root);
            x = next;
        }
        root
    }

    /// REQUIRES: `x` and `y` were returned by prior `add_expr` calls.
    /// ENSURES: After return, `find(x) == find(y)` (same equivalence class).
    /// ENSURES: Union-by-rank keeps the tree balanced.
    pub(crate) fn union(&mut self, x: usize, y: usize) {
        let x_root = self.find(x);
        let y_root = self.find(y);
        if x_root == y_root {
            return;
        }

        let x_rank = self.rank[&x_root];
        let y_rank = self.rank[&y_root];

        if x_rank < y_rank {
            self.parent.insert(x_root, y_root);
        } else if x_rank > y_rank {
            self.parent.insert(y_root, x_root);
        } else {
            self.parent.insert(y_root, x_root);
            self.rank.insert(x_root, x_rank + 1);
        }
    }

    fn process_pending(&mut self, max_iterations: usize) {
        for _ in 0..max_iterations {
            if let Some((a, b)) = self.pending.pop() {
                self.union(a, b);
                continue;
            }

            let Some((a, b)) = self.find_congruent_applications() else {
                break;
            };
            self.union(a, b);
        }
    }

    fn find_congruent_applications(&mut self) -> Option<(usize, usize)> {
        let mut application_ids: Vec<_> = self
            .use_list
            .values()
            .flat_map(|ids| ids.iter().copied())
            .collect();
        application_ids.sort_unstable();
        application_ids.dedup();

        let mut applications = Vec::new();
        for id in application_ids {
            let expr = &self.id_to_expr[id];
            let ExprKind::App(f, a) = expr.kind() else {
                continue;
            };
            let f_id = self.expr_to_id[f];
            let a_id = self.expr_to_id[a];
            applications.push((id, f_id, a_id));
        }

        for (index, &(left_id, left_fn, left_arg)) in applications.iter().enumerate() {
            for &(right_id, right_fn, right_arg) in applications.iter().skip(index + 1) {
                if self.find(left_id) == self.find(right_id) {
                    continue;
                }
                if self.find(left_fn) == self.find(right_fn)
                    && self.find(left_arg) == self.find(right_arg)
                {
                    return Some((left_id, right_id));
                }
            }
        }

        None
    }
}

/// Tactic: cc - Congruence closure tactic.
///
/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: Current goal target is an equality `lhs = rhs`.
/// ENSURES: On `Ok`, the goal is closed via `rfl` because congruence closure
///   proved `lhs` and `rhs` are in the same equivalence class.
/// ENSURES: On `Err(NoProgress)`, no equivalence path was found.
pub fn cc(state: &mut ProofState) -> TacticResult {
    cc_with_config(state, CCConfig::default())
}

/// REQUIRES: At least one goal exists in `state`.
/// REQUIRES: Current goal target is an equality `lhs = rhs`.
/// ENSURES: Equality hypotheses from local context are added to the CC graph.
/// ENSURES: Pending merges are processed up to `config.max_iterations`.
/// ENSURES: On `Ok`, the goal is closed via `rfl`.
pub fn cc_with_config(state: &mut ProofState, config: CCConfig) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);

    let (lhs, rhs) = match_eq_simple(&target)
        .ok_or_else(|| TacticError::GoalMismatch("goal must be an equality".into()))?;

    let mut cc_state = CCState::new();
    let lhs_id = cc_state.add_expr(&lhs);
    let rhs_id = cc_state.add_expr(&rhs);

    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        if let Some((eq_lhs, eq_rhs)) = match_eq_simple(&ty) {
            let l_id = cc_state.add_expr(&eq_lhs);
            let r_id = cc_state.add_expr(&eq_rhs);
            cc_state.union(l_id, r_id);
        }
    }

    cc_state.process_pending(config.max_iterations);

    if cc_state.find(lhs_id) == cc_state.find(rhs_id) {
        rfl(state)
    } else {
        Err(TacticError::NoProgress {
            tactic: "cc".into(),
        })
    }
}

#[cfg(test)]
mod tests {
    use clean_kernel::name::Name;

    use super::*;

    #[test]
    fn cc_state_propagates_application_congruence() {
        let mut cc_state = CCState::new();
        let f = Expr::const_(Name::from_string("f"), vec![]);
        let g = Expr::const_(Name::from_string("g"), vec![]);
        let a = Expr::const_(Name::from_string("a"), vec![]);
        let b = Expr::const_(Name::from_string("b"), vec![]);
        let fa = Expr::app(f.clone(), a.clone());
        let gb = Expr::app(g.clone(), b.clone());

        let fa_id = cc_state.add_expr(&fa);
        let gb_id = cc_state.add_expr(&gb);
        let f_id = cc_state.add_expr(&f);
        let g_id = cc_state.add_expr(&g);
        let a_id = cc_state.add_expr(&a);
        let b_id = cc_state.add_expr(&b);

        cc_state.union(f_id, g_id);
        cc_state.union(a_id, b_id);
        assert_ne!(cc_state.find(fa_id), cc_state.find(gb_id));

        cc_state.process_pending(8);

        assert_eq!(cc_state.find(fa_id), cc_state.find(gb_id));
    }
}
