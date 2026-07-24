// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TC regression tests: beta reduction and delta chain unfolding.
//!
//! Covers multi-arg beta reduction and deep delta chains (HPow-like pattern)
//! that caused heartbeat exhaustion in .olean loading (#3134).

use super::support::make_nat_env;
use super::*;
use crate::env::{ConstantInfo, Reducibility};

/// Add a reducible definition to the environment.
fn add_reducible(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), true);
    info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Add a semireducible (Regular(0)) definition.
fn add_semireducible(env: &mut Environment, name: &str, ty: Expr, value: Expr) {
    let mut info = ConstantInfo::new(Name::from_string(name), vec![], ty, Some(value), false);
    info.reducibility = Reducibility::Regular(0);
    env.extend_constants_unchecked(std::iter::once(info));
}

/// Build a constant reference with no universe parameters.
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

// ============================================================================
// 1. Multi-arg beta reduction
// ============================================================================

/// Regression: multi-arg beta reduction must substitute all args correctly.
///
/// `(fun (a : Type) (b : Type) (x : a) => x) Nat Nat 42` should reduce to `42`.
#[test]
fn test_regression_multi_arg_beta_reduction() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);

    let nat = cst("Nat");
    // fun (a : Type) (b : Type) (x : a) => x
    let body = Expr::lam(
        BinderInfo::Default,
        Expr::type_(), // a : Type
        Expr::lam(
            BinderInfo::Default,
            Expr::type_(), // b : Type
            Expr::lam(
                BinderInfo::Default,
                Expr::bvar(1), // x : a (= bvar(1) after two outer lambdas)
                Expr::bvar(0), // => x
            ),
        ),
    );

    let applied = Expr::app(
        Expr::app(Expr::app(body, nat.clone()), nat),
        Expr::nat_lit(42),
    );

    let result = tc.whnf(&applied);
    assert_eq!(
        result,
        Expr::nat_lit(42),
        "Multi-arg beta reduction should yield the identity on the third arg"
    );
}

/// Regression: nested beta redexes with all args consumed.
///
/// `((fun x => fun y => x) A) B` should reduce to `A`.
#[test]
fn test_regression_nested_beta_redex_saturation() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let body = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(1)),
    );

    let a = Expr::prop();
    let b = Expr::type_();
    let applied = Expr::app(Expr::app(body, a.clone()), b);

    let result = tc.whnf(&applied);
    assert_eq!(result, a, "Nested beta should return first arg");
}

// ============================================================================
// 2. Deep delta chains (HPow-like pattern)
// ============================================================================

/// Regression: multi-level delta chain unfolding.
///
/// Simulates the HPow chain: `c := b := a := Prop`.
#[test]
fn test_regression_deep_delta_chain_three_levels() {
    let mut env = Environment::new();

    add_reducible(&mut env, "a", Expr::type_(), Expr::prop());
    add_reducible(&mut env, "b", Expr::type_(), cst("a"));
    add_reducible(&mut env, "c", Expr::type_(), cst("b"));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&cst("c"), &Expr::prop()),
        "Three-level delta chain: c -> b -> a -> Prop"
    );
}

/// Regression: deep delta chain with mixed reducibility.
#[test]
fn test_regression_delta_chain_mixed_reducibility() {
    let mut env = Environment::new();

    add_semireducible(&mut env, "semi_mid", Expr::type_(), Expr::prop());
    add_reducible(&mut env, "reducible_top", Expr::type_(), cst("semi_mid"));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&cst("reducible_top"), &Expr::prop()),
        "Reducible -> semireducible -> Prop chain should unfold"
    );
}

/// Regression: 5-level delta chain (HPow-like pattern, #3134).
#[test]
fn test_regression_deep_delta_chain_five_levels() {
    let mut env = Environment::new();

    add_reducible(&mut env, "nat_pow", Expr::type_(), Expr::prop());
    add_reducible(&mut env, "Pow.pow", Expr::type_(), cst("nat_pow"));
    add_reducible(&mut env, "instPowNat", Expr::type_(), cst("Pow.pow"));
    add_reducible(&mut env, "instHPow", Expr::type_(), cst("instPowNat"));
    add_reducible(&mut env, "HPow.hPow", Expr::type_(), cst("instHPow"));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&cst("HPow.hPow"), &Expr::prop()),
        "5-level delta chain should unfold to Prop"
    );
}

/// Regression: delta chain where both sides need unfolding.
#[test]
fn test_regression_delta_both_sides_unfold() {
    let mut env = Environment::new();

    add_reducible(&mut env, "target", Expr::type_(), Expr::prop());
    add_reducible(&mut env, "mid", Expr::type_(), cst("target"));
    add_reducible(&mut env, "lhs", Expr::type_(), cst("mid"));
    add_reducible(&mut env, "rhs", Expr::type_(), cst("mid"));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&cst("lhs"), &cst("rhs")),
        "Both sides unfold through mid to target; should be def-eq"
    );
}
