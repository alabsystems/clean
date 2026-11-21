// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression reduction utilities for the simp tactic.
//!
//! Provides beta reduction, eta reduction, bound variable substitution,
//! expression shifting, and BVar containment checks. These are pure
//! expression transformations with no simp-internal dependencies.
//!
//! BVar operations are delegated to `tactic::bvar_ops` so the tactic crate
//! shares one traversal for substitution, shifting, and loose-BVar checks.

use clean_kernel::{Expr, ExprFolder, ExprKind};

use crate::tactic::bvar_ops::{has_loose_bvar, instantiate_bvar, lift_bvar};

/// Perform beta reduction on an expression
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: No beta redexes `(λ x => body) arg` remain in the returned expression
/// ENSURES: Let-bindings are fully substituted (let x := v in body → body[v/x])
/// ENSURES: The returned expression is definitionally equal to the input
pub(crate) fn beta_reduce(expr: &Expr) -> Expr {
    struct BetaReducer;

    impl ExprFolder for BetaReducer {
        fn fold_app(&mut self, f: &Expr, arg: &Expr) -> Expr {
            let f_reduced = self.fold_expr(f);
            let arg_reduced = self.fold_expr(arg);

            // Check for beta redex: (λ x => body) arg
            if let ExprKind::Lam(_bi, _ty, body) = f_reduced.kind() {
                return substitute_bvar(body, 0, &arg_reduced);
            }

            Expr::app(f_reduced, arg_reduced)
        }

        fn fold_let(
            &mut self,
            name: &clean_kernel::Name,
            ty: &Expr,
            val: &Expr,
            body: &Expr,
            non_dep: bool,
        ) -> Expr {
            let val_reduced = self.fold_expr(val);
            let body_reduced = self.fold_expr(body);
            // A match join point stays a `let` (`crate::infer::MATCH_JOIN_BINDER`):
            // substituting it copies the catch-all body into every
            // constructor it covers, at every nesting level.
            if crate::infer::is_match_join_binder(name) {
                return Expr::let_named(
                    name.clone(),
                    ty.clone(),
                    val_reduced,
                    body_reduced,
                    non_dep,
                );
            }
            // Let reduction: substitute value into body
            substitute_bvar(&body_reduced, 0, &val_reduced)
        }
    }

    BetaReducer.fold_expr(expr)
}

/// Substitute `replacement` for a bound variable, decrementing higher BVar indices.
///
/// Uses the shared `tactic::bvar_ops::BVarFolder` traversal.
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression with valid de Bruijn indices
/// ENSURES: Returns `expr[replacement/bvar(idx)]` with correct de Bruijn shifting
/// ENSURES: No occurrence of `bvar(idx)` at depth 0 remains in the result
/// ENSURES: BVars above `idx` are decremented by 1 (capturing the removed binder)
/// ENSURES: `replacement` is shifted up by the binder depth at each substitution site
pub(crate) fn substitute_bvar(expr: &Expr, idx: u32, replacement: &Expr) -> Expr {
    instantiate_bvar(expr, replacement, idx)
}

/// Shift free variables in an expression
///
/// Uses the shared `tactic::bvar_ops::BVarFolder` traversal.
///
/// # Contract
///
/// REQUIRES: For negative `amount`, all affected BVar indices must be >= |amount|
/// ENSURES: Every free `bvar(i)` is replaced by `bvar(i + amount)`
/// ENSURES: The result is well-formed if the precondition holds
pub(crate) fn shift_expr(expr: &Expr, amount: i64) -> Expr {
    lift_bvar(expr, amount, 0)
}

/// Contract the outer lambda when its body is an eta-expansion.
pub(super) fn eta_contract_body(body: &Expr) -> Option<Expr> {
    let ExprKind::App(function, argument) = body.kind() else {
        return None;
    };
    if matches!(argument.kind(), ExprKind::BVar(0)) && !contains_bvar(function, 0) {
        Some(shift_expr(function, -1))
    } else {
        None
    }
}

/// Perform eta reduction: λ x => f x → f (when x not free in f)
///
/// ONE contraction per `Lam` node, NOT a fixpoint. `fold_lam` rebuilds the
/// node from its already-folded body and never re-examines the node it just
/// built, so a multi-binder eta expansion loses one binder per call:
/// `fun a b => f a b` lands on `fun a => f a`, which is still eta-reducible.
/// The simp TRAVERSAL does not notice, because its outer loop re-simplifies
/// the rewritten target and gets the fixpoint over successive passes; a caller
/// that normalizes a term exactly once wants [`eta_reduce_fixpoint`].
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Every `Lam` node of the input whose body is `f (bvar 0)` with
///   `bvar 0 ∉ FV(f)` is contracted — but a contraction that EXPOSES a new
///   one at the enclosing binder is not re-examined (see above)
/// ENSURES: The returned expression is definitionally equal to the input
/// ENSURES: De Bruijn indices are correctly shifted down after eta contraction
pub(crate) fn eta_reduce(expr: &Expr) -> Expr {
    struct EtaReducer;

    impl ExprFolder for EtaReducer {
        fn fold_lam(&mut self, bi: clean_kernel::BinderData, ty: &Expr, body: &Expr) -> Expr {
            if let Some(contracted) = eta_contract_body(body) {
                return contracted;
            }
            Expr::lam(bi, self.fold_expr(ty), self.fold_binder_body(body))
        }
    }

    EtaReducer.fold_expr(expr)
}

/// [`eta_reduce`] applied until it stops changing the term.
///
/// A round that changes anything removes at least one binder, so the fixpoint
/// is reached in at most the term's binder depth and the loop exits on the
/// first no-op round. `ETA_FIXPOINT_ROUNDS` bounds a folder that has stopped
/// shrinking; it is not the normal exit.
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: No eta-reducible lambda remains, at any binder depth, within
///   `ETA_FIXPOINT_ROUNDS` rounds
/// ENSURES: The returned expression is definitionally equal to the input
pub(crate) fn eta_reduce_fixpoint(expr: &Expr) -> Expr {
    /// Rounds before the loop stops asking. Each round that changes the term
    /// drops a binder, so this is far above any real term's binder depth.
    const ETA_FIXPOINT_ROUNDS: usize = 16;

    let mut reduced = eta_reduce(expr);
    for _ in 1..ETA_FIXPOINT_ROUNDS {
        let next = eta_reduce(&reduced);
        if next == reduced {
            break;
        }
        reduced = next;
    }
    reduced
}

/// Check if an expression contains a specific bound variable.
///
/// Uses the shared `tactic::bvar_ops::BVarFolder` traversal.
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `true` iff `bvar(idx)` occurs free (at depth 0) in `expr`
pub(crate) fn contains_bvar(expr: &Expr, idx: u32) -> bool {
    has_loose_bvar(expr, idx)
}

#[cfg(test)]
mod eta_fixpoint_tests {
    use super::{eta_reduce, eta_reduce_fixpoint};
    use clean_kernel::{BinderInfo, Expr, Level, Name};

    fn f_const() -> Expr {
        Expr::const_(Name::from_string("f"), vec![])
    }

    /// `fun a => f a`.
    fn one_binder_eta() -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::app(f_const(), Expr::bvar(0)),
        )
    }

    /// `fun a => fun b => f a b`.
    fn two_binder_eta() -> Expr {
        let body = Expr::app(Expr::app(f_const(), Expr::bvar(1)), Expr::bvar(0));
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), body),
        )
    }

    #[test]
    fn test_eta_reduce_one_binder_contracts_fully() {
        assert_eq!(eta_reduce(&one_binder_eta()), f_const());
    }

    /// The measured shortfall the matcher's fixpoint exists for: a single
    /// `eta_reduce` call contracts the INNER binder and leaves the outer one,
    /// because `fold_lam` never re-examines the node it just rebuilt.
    #[test]
    fn test_eta_reduce_two_binders_leaves_one_uncontracted() {
        let once = eta_reduce(&two_binder_eta());
        assert_ne!(once, f_const(), "one call must not reach the fixpoint");
        assert_eq!(
            once,
            one_binder_eta(),
            "one call contracts exactly the inner binder"
        );
    }

    #[test]
    fn test_eta_reduce_fixpoint_two_binders_contracts_fully() {
        assert_eq!(eta_reduce_fixpoint(&two_binder_eta()), f_const());
    }

    /// The loop must be a no-op on a term with nothing to contract: it exits
    /// on the first unchanged round rather than rewriting the term.
    #[test]
    fn test_eta_reduce_fixpoint_leaves_a_non_eta_lambda_alone() {
        // `fun a => f a a` — `a` occurs in the function part, so no contraction.
        let body = Expr::app(Expr::app(f_const(), Expr::bvar(0)), Expr::bvar(0));
        let lam = Expr::lam(BinderInfo::Default, Expr::sort(Level::zero()), body);
        assert_eq!(eta_reduce_fixpoint(&lam), lam);
    }
}
