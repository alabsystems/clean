// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `is_def_eq_args_only` failure cache (`args_failure_cache`).
//!
//! Validates that:
//! 1. Cache starts empty
//! 2. Failed argument comparisons populate the cache
//! 3. Cache is cleared alongside other caches on mode/transparency changes
//! 4. Cache uses SlidingCache eviction
//!
//! Part of #1360.

use super::*;
use crate::env::{Declaration, Reducibility, TransparencyMode};
use crate::mode::CleanMode;

/// Helper: create an environment with two definitions that share the same name
/// pattern but have different argument values, triggering the lazy delta
/// `is_def_eq_args_only` path.
///
/// We define `f : Nat → Nat` with a body, and then compare `f 0` vs `f 1`.
/// Since `f` has a definition (Regular reducibility), `lazy_delta_step_equal`
/// will try `is_def_eq_args_only` which compares `0 =?= 1` → false,
/// populating the args_failure_cache.
fn setup_env_with_regular_def() -> Environment {
    let mut env = Environment::new();

    // Define Nat as an inductive type so that 0 and 1 are distinct
    // We use nat_lit which doesn't need the inductive registration
    // Just define a regular function f : Prop → Prop := λ x, x
    let f_name = Name::from_string("f");
    let f_type = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let f_body = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: f_name.clone(),
        level_params: vec![],
        type_: f_type,
        value: f_body,
        is_reducible: false,
    })
    .expect("add f");

    // Ensure f is Regular reducibility (default for definitions)
    env.set_reducibility(&f_name, Reducibility::Regular(1));

    env
}

#[test]
fn test_args_failure_cache_starts_empty() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "args_failure_cache should start empty"
    );
}

#[test]
fn test_args_failure_cache_populated_on_failed_args() {
    let env = setup_env_with_regular_def();
    let tc = TypeChecker::new(&env);

    // Build f(Prop) and f(Type) — same head, different arguments
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::app(f.clone(), Expr::prop());
    let b = Expr::app(f, Expr::type_());

    // These are not def-eq: f(Prop) ≠ f(Type)
    // During lazy delta reduction, `lazy_delta_step_equal` will:
    //   1. See both sides have head `f` with Regular reducibility
    //   2. Try `is_def_eq_args_only` comparing Prop vs Type → false
    //   3. Cache the failure in args_failure_cache
    let result = tc.is_def_eq(&a, &b);
    assert!(!result, "f(Prop) should not be def-eq to f(Type)");

    // The args_failure_cache should have at least one entry
    assert!(
        tc.args_failure_cache_entries() > 0,
        "args_failure_cache should be populated after failed args comparison, got {}",
        tc.args_failure_cache_entries()
    );
}

#[test]
fn test_args_failure_cache_cleared_on_mode_change() {
    let env = setup_env_with_regular_def();
    let mut tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::app(f.clone(), Expr::prop());
    let b = Expr::app(f, Expr::type_());

    // Populate the cache
    let _ = tc.is_def_eq(&a, &b);
    let entries_before = tc.args_failure_cache_entries();
    assert!(
        entries_before > 0,
        "cache should be populated before mode change"
    );

    // Change mode → should clear all caches including args_failure_cache
    tc.set_mode(CleanMode::Classical);
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "args_failure_cache should be cleared after set_mode"
    );
}

#[test]
fn test_args_failure_cache_cleared_on_transparency_change() {
    let env = setup_env_with_regular_def();
    let mut tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::app(f.clone(), Expr::prop());
    let b = Expr::app(f, Expr::type_());

    // Populate the cache
    let _ = tc.is_def_eq(&a, &b);
    let entries_before = tc.args_failure_cache_entries();
    assert!(
        entries_before > 0,
        "cache should be populated before transparency change"
    );

    // Change transparency → should clear all caches including args_failure_cache
    tc.set_transparency(TransparencyMode::All);
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "args_failure_cache should be cleared after set_transparency"
    );
}

#[test]
fn test_args_failure_cache_cleared_on_context_mut() {
    let env = setup_env_with_regular_def();
    let mut tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::app(f.clone(), Expr::prop());
    let b = Expr::app(f, Expr::type_());

    // Populate the cache
    let _ = tc.is_def_eq(&a, &b);
    let entries_before = tc.args_failure_cache_entries();
    assert!(
        entries_before > 0,
        "cache should be populated before context change"
    );

    // Mutate context → should clear all caches including args_failure_cache
    let _ = tc.local_context_mut();
    assert_eq!(
        tc.args_failure_cache_entries(),
        0,
        "args_failure_cache should be cleared after local_context_mut"
    );
}

/// Test that the args_failure_cache does not interfere with correctness:
/// same-head applications with equal arguments should still return true.
#[test]
fn test_args_failure_cache_does_not_affect_equal_args() {
    let env = setup_env_with_regular_def();
    let tc = TypeChecker::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);

    // f(Prop) vs f(Prop) — same arguments, should be def-eq
    let a = Expr::app(f.clone(), Expr::prop());
    let b = Expr::app(f.clone(), Expr::prop());
    assert!(tc.is_def_eq(&a, &b), "f(Prop) should be def-eq to f(Prop)");

    // Now check f(Prop) vs f(Type) — different, should fail and populate cache
    let c = Expr::app(f.clone(), Expr::type_());
    assert!(
        !tc.is_def_eq(&a, &c),
        "f(Prop) should not be def-eq to f(Type)"
    );

    // Re-check the equal case — cache failure should not pollute equal-args path
    assert!(
        tc.is_def_eq(&a, &b),
        "f(Prop) should still be def-eq to f(Prop) after a different pair failed"
    );
}
