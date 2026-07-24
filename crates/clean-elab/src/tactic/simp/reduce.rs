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
            _name: &clean_kernel::Name,
            _ty: &Expr,
            val: &Expr,
            body: &Expr,
            _non_dep: bool,
        ) -> Expr {
            // Let reduction: substitute value into body
            let val_reduced = self.fold_expr(val);
            let body_reduced = self.fold_expr(body);
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

/// Perform eta reduction: λ x => f x → f (when x not free in f)
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: No eta-reducible lambdas `(λ x => f x)` where `x ∉ FV(f)` remain in the result
/// ENSURES: The returned expression is definitionally equal to the input
/// ENSURES: De Bruijn indices are correctly shifted down after eta contraction
pub(crate) fn eta_reduce(expr: &Expr) -> Expr {
    struct EtaReducer;

    impl ExprFolder for EtaReducer {
        fn fold_lam(&mut self, bi: clean_kernel::BinderData, ty: &Expr, body: &Expr) -> Expr {
            if let ExprKind::App(f, arg) = body.kind() {
                // Check if arg is bvar(0) and f doesn't contain bvar(0)
                if let ExprKind::BVar(0) = arg.kind() {
                    if !contains_bvar(f, 0) {
                        // Eta reduce: λ x => f x → f (with shifted indices)
                        return shift_expr(f, -1);
                    }
                }
            }
            Expr::lam(bi, self.fold_expr(ty), self.fold_binder_body(body))
        }
    }

    EtaReducer.fold_expr(expr)
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
