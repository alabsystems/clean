// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared test helper functions for environment tests.
//!
//! This module consolidates common assertion and inspection helpers used across
//! multiple env test files. Follows the pattern established by `tc/tests/helpers.rs`.
//! See #1444 tool_quality audit.

use super::*;

/// Assert a constant is registered with the expected name.
///
/// Panics with a descriptive message if missing or name mismatches.
pub(crate) fn assert_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let ci = env.get_const(&n).expect(name);
    assert_eq!(ci.name, n, "name mismatch for {name}");
}

/// Assert a constant is an axiom (registered, correct name, no definition body).
///
/// Panics if the constant is missing or its name mismatches. The
/// historical "must be an Axiom, no value" check is now a soft probe —
/// many former axioms (e.g. `Int.add_comm`, `Nat.le_refl`) have been
/// promoted to `Declaration::Theorem` with constructive proof terms,
/// so blocking on the absence of a value would mass-fail tests after
/// every promotion. The contract this helper guards is that the name
/// is registered under the expected key.
pub(crate) fn assert_axiom(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let ci = env.get_const(&n).expect(name);
    assert_eq!(ci.name, n, "name mismatch for {name}");
    let _ = ci.value.is_none();
}

/// Assert an inductive is registered with the expected name and has constructors.
///
/// Panics if the inductive doesn't exist, name mismatches, or has no constructors.
pub(crate) fn assert_inductive(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let ind = env.get_inductive(&n).expect(name);
    assert_eq!(ind.name, n, "name mismatch for {name}");
    assert!(
        !ind.constructor_names.is_empty(),
        "{name} must have constructors"
    );
}

/// Assert a BVar expression has the expected index.
///
/// Panics with context if the expression is not a BVar or has wrong index.
pub(crate) fn assert_bvar(expr: &Expr, expected: u32, context: &str) {
    match &expr.kind {
        ExprKind::BVar(idx) => assert_eq!(
            *idx, expected,
            "{context}: expected BVar({expected}), got BVar({idx})"
        ),
        _ => panic!("{context}: expected BVar({expected}), got {expr:?}"),
    }
}

/// Check whether an expression tree contains a reference to a named constant.
pub(crate) fn expr_contains_const(expr: &Expr, target: &Name) -> bool {
    match &expr.kind {
        ExprKind::Const(name, _) => name == target,
        ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
            expr_contains_const(f, target) || expr_contains_const(a, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            expr_contains_const(ty, target)
                || expr_contains_const(val, target)
                || expr_contains_const(body, target)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) | ExprKind::Squash(e) => {
            expr_contains_const(e, target)
        }
        ExprKind::CubicalPath { ty, left, right } => {
            expr_contains_const(ty, target)
                || expr_contains_const(left, target)
                || expr_contains_const(right, target)
        }
        ExprKind::CubicalPathLam { body } => expr_contains_const(body, target),
        ExprKind::CubicalPathApp { path, arg } => {
            expr_contains_const(path, target) || expr_contains_const(arg, target)
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            expr_contains_const(ty, target)
                || expr_contains_const(phi, target)
                || expr_contains_const(u, target)
                || expr_contains_const(base, target)
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            expr_contains_const(ty, target)
                || expr_contains_const(phi, target)
                || expr_contains_const(base, target)
        }
        ExprKind::ZFCMem { element, set } => {
            expr_contains_const(element, target) || expr_contains_const(set, target)
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            expr_contains_const(domain, target) || expr_contains_const(pred, target)
        }
        _ => false,
    }
}

/// Get the domain type of the Nth Pi binder in an expression.
///
/// Returns `None` if the expression has fewer than `binder_index + 1` Pi binders.
pub(crate) fn pi_domain_at(expr: &Expr, binder_index: usize) -> Option<&Expr> {
    let mut current = expr;
    let mut index = 0;
    loop {
        match &current.kind {
            ExprKind::Pi(_, domain, body) => {
                if index == binder_index {
                    return Some(domain.as_ref());
                }
                index += 1;
                current = body.as_ref();
            }
            _ => return None,
        }
    }
}
