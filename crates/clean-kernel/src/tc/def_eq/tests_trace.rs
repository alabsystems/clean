// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `debug-def-eq` diagnostic tracing.
//!
//! These tests verify the tracing infrastructure compiles and runs correctly
//! regardless of whether the `debug-def-eq` feature is enabled. The trace
//! output goes to stderr via `eprintln!` and is only present when the feature
//! is active.
//!
//! To see trace output: `cargo test -p clean-kernel --lib --features debug-def-eq -- tests_trace`

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

#[test]
fn test_trace_reflexive_nat_lit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let a = Expr::nat_lit(42);
    // Reflexive comparison should succeed via quick_is_def_eq (Lit == Lit).
    assert!(tc.is_def_eq(&a, &a));
}

#[test]
fn test_trace_different_nat_lits() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    // Different literals should fail, exercising the full pipeline.
    assert!(!tc.is_def_eq(&a, &b));
}

#[test]
fn test_trace_sort_comparison() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // Sort(0) =?= Sort(0) — should succeed via quick_is_def_eq (Sort branch).
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    assert!(tc.is_def_eq(&prop, &prop));
}

#[test]
fn test_trace_lambda_binding() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // fun (x : Nat) => x  =?=  fun (y : Nat) => y
    // Should succeed via is_def_eq_binding (alpha-equivalence).
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lam1 = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let lam2 = Expr::lam(BinderInfo::Default, nat, Expr::bvar(0));
    assert!(tc.is_def_eq(&lam1, &lam2));
}

#[test]
fn test_trace_lambda_mismatch() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // fun (x : Nat) => x  =?=  fun (x : Nat) => 0
    // Should fail: bodies differ (BVar(0) vs Lit(0)).
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let lam1 = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));
    let lam2 = Expr::lam(BinderInfo::Default, nat, Expr::nat_lit(0));
    assert!(!tc.is_def_eq(&lam1, &lam2));
}

#[test]
fn test_trace_structural_app_comparison() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // App(f, a) =?= App(f, b) where a != b exercises the structural App branch.
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let app1 = Expr::app(f.clone(), Expr::nat_lit(1));
    let app2 = Expr::app(f, Expr::nat_lit(2));
    assert!(!tc.is_def_eq(&app1, &app2));
}

#[test]
fn test_trace_const_no_unfold() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // Const("Foo", []) =?= Const("Bar", []) — neither in environment,
    // delta exhausts immediately, structural comparison fails.
    let a = Expr::const_(Name::from_string("Foo"), vec![]);
    let b = Expr::const_(Name::from_string("Bar"), vec![]);
    assert!(!tc.is_def_eq(&a, &b));
}

#[test]
fn test_trace_same_const_succeeds() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // Const("Nat", []) =?= Const("Nat", [])
    let a = Expr::const_(Name::from_string("Nat"), vec![]);
    let b = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(tc.is_def_eq(&a, &b));
}
