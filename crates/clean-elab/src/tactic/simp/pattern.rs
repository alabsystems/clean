// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! BVar-to-metavariable conversion for simp pattern matching.
//!
//! Extracted from `simp/expr.rs` for file size enforcement (#307).
//! Converts bound variables in lemma patterns to fresh metavariables
//! for unification-based matching, and substitutes matched BVars back.

use std::sync::Arc;

use clean_kernel::{Expr, ExprKind, FVarId};
use hashbrown::HashMap;

use crate::stack_safe;
use crate::unify::MetaState;

/// Convert bound variables in a pattern to fresh metavariables.
///
/// `scope` is the local-variable scope recorded on each minted meta: the
/// matcher unifies the pattern against a GOAL subterm, so a pattern variable
/// must be allowed to bind a term mentioning the goal's own locals
/// (`Nat.mul ?n 1` against `a * 1` binds `?n := a`, a goal FVar). Passing the
/// goal's locals here keeps the unifier's scope discipline intact: metas still
/// cannot capture binder-opened temporaries or anything outside the goal (B102).
///
/// Returns the transformed expression and a mapping from BVar indices to MetaIds.
///
/// # Contract
///
/// REQUIRES: `pattern` is a well-formed expression (valid BVar indices)
/// ENSURES: All top-level BVars in `pattern` are replaced by fresh metavariables
/// ENSURES: Inner BVars bound by Lam/Pi/Let binders are preserved unchanged
/// ENSURES: Returned map keys correspond to adjusted BVar indices (0-based from top)
pub(crate) fn convert_bvars_to_metas(
    pattern: &Expr,
    metas: &mut MetaState,
    scope: &[(clean_parser::SurfaceName, FVarId, Expr)],
) -> (Expr, HashMap<u32, Expr>) {
    let mut bvar_to_meta = HashMap::new();
    let result = map_pattern(pattern, |index| {
        let replacement = bvar_to_meta.entry(index).or_insert_with(|| {
            // The scope is the goal's locals. Each adjusted index gets the
            // same fresh metavariable at every occurrence.
            let meta_id = metas.fresh_with_locals(Expr::type_(), scope.to_vec());
            Expr::fvar(MetaState::to_fvar(meta_id))
        });
        Some(replacement.clone())
    });
    (result, bvar_to_meta)
}

/// Substitute BVars in an expression using a mapping to metavariable expressions.
/// REQUIRES: `bvar_to_meta` uses the adjusted top-level indexing from `convert_bvars_to_metas`
/// ENSURES: Only mapped top-level BVars are replaced; inner bound BVars are preserved
pub(crate) fn substitute_bvars_with_metas(expr: &Expr, bvar_to_meta: &HashMap<u32, Expr>) -> Expr {
    map_pattern(expr, |index| bvar_to_meta.get(&index).cloned())
}

fn map_pattern(expr: &Expr, replace: impl FnMut(u32) -> Option<Expr>) -> Expr {
    PatternMapper {
        replace,
        shared: HashMap::new(),
    }
    .term(expr, 0)
}

struct PatternMapper<F> {
    replace: F,
    // Input Arcs live for the whole conversion. Binder depth matters even
    // when the same input node recurs, since it selects a different BVar.
    shared: HashMap<(*const Expr, u32), Arc<Expr>>,
}

impl<F: FnMut(u32) -> Option<Expr>> PatternMapper<F> {
    fn child(&mut self, input: &Arc<Expr>, depth: u32) -> Arc<Expr> {
        if depth >= input.loose_bvar_range() {
            return Arc::clone(input);
        }
        if Arc::strong_count(input) == 1 {
            return Arc::new(self.term(input, depth));
        }
        let key = (Arc::as_ptr(input), depth);
        if let Some(result) = self.shared.get(&key) {
            return Arc::clone(result);
        }
        let result = Arc::new(self.term(input, depth));
        self.shared.insert(key, Arc::clone(&result));
        result
    }

    fn term(&mut self, expr: &Expr, depth: u32) -> Expr {
        if depth >= expr.loose_bvar_range() {
            return expr.clone();
        }
        stack_safe(|| match expr.kind() {
            ExprKind::BVar(index) => (self.replace)(index - depth).unwrap_or_else(|| expr.clone()),
            ExprKind::App(f, a) => Expr::app_arc(self.child(f, depth), self.child(a, depth)),
            ExprKind::Lam(info, ty, body) => {
                Expr::lam_arc(*info, self.child(ty, depth), self.child(body, depth + 1))
            }
            ExprKind::Pi(info, ty, body) => {
                Expr::pi_arc(*info, self.child(ty, depth), self.child(body, depth + 1))
            }
            ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named_arc(
                name.clone(),
                self.child(ty, depth),
                self.child(val, depth),
                self.child(body, depth + 1),
                *non_dep,
            ),
            ExprKind::Proj(name, index, child) => {
                Expr::proj_arc(name.clone(), *index, self.child(child, depth))
            }
            ExprKind::MData(data, child) => {
                Expr::from_kind(ExprKind::MData(data.clone(), self.child(child, depth)))
            }
            ExprKind::Squash(child) => Expr::from_kind(ExprKind::Squash(self.child(child, depth))),
            _ => expr.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::BinderInfo;

    #[test]
    fn shared_pattern_nodes_reuse_the_result_at_the_same_binder_depth() {
        let argument = Arc::new(Expr::bvar(1));
        let domain = Arc::new(Expr::type_());
        let repeated = Expr::app_arc(Arc::clone(&argument), Arc::clone(&argument));
        let under_binder = Expr::lam_arc(BinderInfo::Default, domain, argument);
        let pattern = Expr::app(repeated, under_binder);
        let mut metas = MetaState::new();
        let (mapped, replacements) = convert_bvars_to_metas(&pattern, &mut metas, &[]);
        let ExprKind::App(repeated, under_binder) = mapped.kind() else {
            panic!("application expected");
        };
        let ExprKind::App(first, second) = repeated.kind() else {
            panic!("shared pair expected");
        };
        let ExprKind::Lam(_, _, bound) = under_binder.kind() else {
            panic!("binder expected");
        };
        assert!(Arc::ptr_eq(first, second));
        assert_eq!(first.as_ref(), &replacements[&1]);
        assert_eq!(bound.as_ref(), &replacements[&0]);
        assert_ne!(first, bound);
        assert_eq!(mapped, substitute_bvars_with_metas(&pattern, &replacements));
    }
}
