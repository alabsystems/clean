// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The one real "does this term still mention a metavariable?" scan (G46,
//! ledger (116)).
//!
//! An elaborator metavariable is a free variable whose id carries
//! [`MetaState`]'s bit-63 tag (`MetaState::to_fvar`). The kernel's cached
//! `Expr::has_expr_mvar_quick()` flag can never see one: the kernel `Expr` has
//! no metavariable constructor, and its `FVar` arm packs `has_expr_mvar =
//! false` (`clean-kernel/src/expr/kind.rs`, `compute_meta`), so the flag is
//! constant `false` for every expression Clean builds. Every guard that asked
//! the flag "is this term ground?" was vacuous. This scan answers it: a
//! DAG-aware walk pruned by the O(1) cached `has_fvar` flag (a subtree with no
//! free variable at all has no metavariable either), so a ground or
//! fvar-free term costs one flag read.
//!
//! After `MetaState::instantiate`, any tagged fvar that survives is unassigned.

use super::MetaState;
use clean_kernel::{Expr, ExprKind};
use hashbrown::HashSet;

impl MetaState {
    /// Whether `expr` mentions any elaborator metavariable (a bit-63-tagged
    /// `FVar`). Instantiate first to ask about UNASSIGNED ones.
    #[must_use]
    pub fn expr_has_meta(expr: &Expr) -> bool {
        if !expr.has_fvar_quick() {
            return false;
        }
        let mut visited: HashSet<*const Expr> = HashSet::new();
        let mut stack: Vec<&Expr> = vec![expr];
        while let Some(cur) = stack.pop() {
            if !cur.has_fvar_quick() || !visited.insert(cur as *const Expr) {
                continue;
            }
            match cur.kind() {
                ExprKind::FVar(id) => {
                    if Self::from_fvar(*id).is_some() {
                        return true;
                    }
                }
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    stack.push(t);
                    stack.push(b);
                }
                ExprKind::Let(_, t, v, b, _) => {
                    stack.push(t);
                    stack.push(v);
                    stack.push(b);
                }
                ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => stack.push(x),
                _ => {}
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unify::MetaId;
    use clean_kernel::{BinderInfo, FVarId, Name};

    fn meta(n: u64) -> Expr {
        Expr::fvar(MetaState::to_fvar(MetaId(n)))
    }

    #[test]
    fn test_expr_has_meta_kernel_flag_is_blind_to_elaborator_metas() {
        // The mutation the old guards could not see: a bare metavariable.
        let m = meta(3);
        assert!(
            !m.has_expr_mvar_quick(),
            "the kernel flag is constant false"
        );
        assert!(MetaState::expr_has_meta(&m));
    }

    #[test]
    fn test_expr_has_meta_finds_a_nested_meta() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let body = Expr::app(Expr::app(nat.clone(), meta(0)), Expr::bvar(0));
        let lam = Expr::lam(BinderInfo::Default, nat.clone(), body);
        let e = Expr::let_named(Name::from_string("x"), nat.clone(), nat, lam, false);
        assert!(!e.has_expr_mvar_quick());
        assert!(MetaState::expr_has_meta(&e));
    }

    #[test]
    fn test_expr_has_meta_ignores_ordinary_fvars_and_ground_terms() {
        let local = Expr::fvar(FVarId::new(7));
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        assert!(!MetaState::expr_has_meta(&local));
        assert!(!MetaState::expr_has_meta(&Expr::app(nat.clone(), local)));
        assert!(!MetaState::expr_has_meta(&nat));
    }
}
