// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge-local Eq.trans from And-assumptions (#2442 Phase 2).
//!
//! Handles the pattern where an assumption is `And(Eq(ty,a,b), Eq(ty,b,c))` and the
//! goal is `Eq(ty,a,c)`. Builds `Eq.trans (And.left h) (And.right h)` without
//! requiring solver term registration (the guided equality BFS path handles the
//! solver-registered case).

use clean_kernel::Expr;

use super::disjunction::{mk_and_left, mk_and_right};
use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::SmtBridge;

/// Build `@Eq.trans.{u} ty a b c h1 h2` using a bridge-local universe lookup.
///
/// Returns `None` if the bridge cannot infer the sort level for `ty`.
fn bridge_local_eq_trans(
    bridge: &SmtBridge<'_>,
    ty: &Expr,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    h1: &Expr,
    h2: &Expr,
) -> Option<Expr> {
    let u = bridge.sort_level_of_type(ty).ok()?;
    Some(super::eq_proof_builders::mk_eq_trans(
        &u, ty, a, b, c, h1, h2,
    ))
}

/// Try building Eq.trans from an And-typed assumption whose components are equalities.
///
/// Handles the pattern:
///   assumption : And(Eq(ty, a, b), Eq(ty, b, c)),  goal : Eq(ty, a, c)
///   → Eq.trans (And.left h) (And.right h)
///
/// Also handles the reversed component order:
///   assumption : And(Eq(ty, b, c), Eq(ty, a, b)),  goal : Eq(ty, a, c)
///   → Eq.trans (And.right h) (And.left h)
///
/// This is the bridge-local path that works without solver term registration.
/// The guided equality BFS path (guided_equality.rs) handles the general case
/// when solver terms are registered.
pub(super) fn try_and_eq_trans(
    assumption_class: &LogicalForm,
    goal_class: &LogicalForm,
    assumption_proof: &Expr,
    bridge: &SmtBridge<'_>,
) -> Option<Expr> {
    let LogicalForm::And(ref left, ref right) = assumption_class else {
        return None;
    };
    let LogicalForm::Eq {
        ty: ref _goal_ty,
        lhs: ref goal_lhs,
        rhs: ref goal_rhs,
    } = goal_class
    else {
        return None;
    };

    let left_class = bridge.classify_prop(left);
    let right_class = bridge.classify_prop(right);

    let (l_ty, l_lhs, l_rhs) = match left_class {
        LogicalForm::Eq {
            ref ty,
            ref lhs,
            ref rhs,
        } => (ty, lhs, rhs),
        _ => return None,
    };
    let (r_ty, r_lhs, r_rhs) = match right_class {
        LogicalForm::Eq {
            ref ty,
            ref lhs,
            ref rhs,
        } => (ty, lhs, rhs),
        _ => return None,
    };

    let goal_lhs_key = ExprKey::from_expr(goal_lhs);
    let goal_rhs_key = ExprKey::from_expr(goal_rhs);
    if goal_lhs_key.is_none() || goal_rhs_key.is_none() {
        return None;
    }

    let l_lhs_key = ExprKey::from_expr(l_lhs);
    let l_rhs_key = ExprKey::from_expr(l_rhs);
    let r_lhs_key = ExprKey::from_expr(r_lhs);
    let r_rhs_key = ExprKey::from_expr(r_rhs);
    let h_left = mk_and_left(assumption_proof);
    let h_right = mk_and_right(assumption_proof);

    // Pattern 1: And(Eq(ty, a, b), Eq(ty, b, c)), goal Eq(ty, a, c)
    if l_rhs_key.is_some()
        && l_rhs_key == r_lhs_key
        && goal_lhs_key == l_lhs_key
        && goal_rhs_key == r_rhs_key
    {
        return bridge_local_eq_trans(bridge, l_ty, l_lhs, l_rhs, r_rhs, &h_left, &h_right);
    }
    // Pattern 2: And(Eq(ty, b, c), Eq(ty, a, b)), goal Eq(ty, a, c) — swapped order
    if r_rhs_key.is_some()
        && r_rhs_key == l_lhs_key
        && goal_lhs_key == r_lhs_key
        && goal_rhs_key == l_rhs_key
    {
        return bridge_local_eq_trans(bridge, r_ty, r_lhs, r_rhs, l_rhs, &h_right, &h_left);
    }
    None
}
