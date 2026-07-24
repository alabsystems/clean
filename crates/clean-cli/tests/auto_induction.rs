// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for the structural-induction lane in `clean-auto`
//! (`AutomationEngine::prove_by_induction` + the `run_pipeline` hook).
//!
//! This test lives in `clean-cli` (not `clean-auto`) on purpose: `clean-auto`'s
//! lib *test* binary pulls in the trust-cg/trust-ir dev-dependencies, whose
//! linkability is being repaired in a parallel session. `clean-cli` depends only
//! on `clean-auto`'s *lib* (no trust-cg), so this test drives the public API
//! surface (`AutomationEngine`) without that dev-dep.
//!
//! SOUNDNESS (load-bearing): the induction lane is on the *search* side, not the
//! TCB. Each test below re-checks the emitted proof term through the kernel
//! (`TypeChecker::infer_type` + `is_def_eq` against the goal) and asserts the
//! term is a genuine `Nat.rec` recursor application — never a `sorry`/axiom
//! shortcut. A lane that returned `Some` with a bogus term would fail these
//! checks.

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, TypeChecker};

/// Environment with the real `Nat` inductive (so `Nat.rec` exists and `Nat.add`
/// is a reducible definition), `Eq`, and the classical bootstrap the SMT bridge
/// expects.
fn nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_classical().expect("init_classical");
    env
}

fn nat() -> Expr {
    Expr::const_str("Nat")
}

/// `Eq Nat lhs rhs` at universe level 1 (`Nat : Type = Sort 1`).
fn nat_eq(lhs: Expr, rhs: Expr) -> Expr {
    let eq = Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]);
    Expr::apps(eq, [nat(), lhs, rhs])
}

/// `Nat.add a b`.
fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}

/// `∀ (n : Nat), body` where `body` is built from `BVar(0) = n`.
fn forall_nat(body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, nat(), body)
}

/// Assert `term : goal` in `env` (kernel `infer_type` + `is_def_eq`).
fn assert_kernel_checks(env: &Environment, term: &Expr, goal: &Expr, what: &str) {
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(term)
        .unwrap_or_else(|e| panic!("[{what}] proof term failed to type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, goal),
        "[{what}] inferred type is not def-eq to the goal\n  inferred: {inferred:?}\n  goal: {goal:?}"
    );
}

/// Assert that `term`'s application head is the `Nat.rec` recursor constant
/// (i.e. this is a genuine induction proof, not a `sorry`/axiom).
fn assert_is_nat_rec(term: &Expr, what: &str) {
    let head = term.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            "Nat.rec",
            "[{what}] proof head should be Nat.rec, got {name}"
        ),
        other => panic!("[{what}] proof head is not a constant: {other:?}"),
    }
}

/// `∀ n, 0 + n = n` — the classic identity that REQUIRES induction:
/// `Nat.add` recurses on its second argument, so `0 + n` is stuck for a free
/// `n` and no EUF/superposition step closes it.
#[test]
fn test_induction_zero_add_n_kernel_checks() {
    let env = nat_env();
    let goal = forall_nat(nat_eq(
        nat_add(Expr::const_str("Nat.zero"), Expr::bvar(0)),
        Expr::bvar(0),
    ));

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, Duration::from_secs(30))
        .expect("∀ n, 0 + n = n should be provable by induction");

    assert_is_nat_rec(result.proof_term(), "0+n=n");
    assert_kernel_checks(&env, result.proof_term(), &goal, "0+n=n");
}

/// `∀ n, n + 0 = n` — also discharged through the induction lane to a
/// kernel-checked `Nat.rec` term.
#[test]
fn test_induction_n_add_zero_kernel_checks() {
    let env = nat_env();
    let goal = forall_nat(nat_eq(
        nat_add(Expr::bvar(0), Expr::const_str("Nat.zero")),
        Expr::bvar(0),
    ));

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, Duration::from_secs(30))
        .expect("∀ n, n + 0 = n should be provable by induction");

    assert_is_nat_rec(result.proof_term(), "n+0=n");
    assert_kernel_checks(&env, result.proof_term(), &goal, "n+0=n");
}

/// The full `auto_prove` pipeline routes `∀ n, 0 + n = n` to the induction lane
/// (after SMT + superposition fail) and returns a kernel-checking proof.
#[test]
fn test_auto_prove_pipeline_routes_to_induction() {
    let env = nat_env();
    let goal = forall_nat(nat_eq(
        nat_add(Expr::const_str("Nat.zero"), Expr::bvar(0)),
        Expr::bvar(0),
    ));

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, Duration::from_secs(30), None)
        .expect("auto_prove should solve ∀ n, 0 + n = n via the induction lane");

    assert_is_nat_rec(result.proof_term(), "auto_prove 0+n=n");
    assert_kernel_checks(&env, result.proof_term(), &goal, "auto_prove 0+n=n");
}

/// The lane is additive: a non-`∀(·:Nat)` goal is left to the other engines.
#[test]
fn test_induction_declines_non_nat_forall() {
    let env = nat_env();
    // `0 = 0` is not a `∀ (n:Nat), _`, so the induction lane must decline.
    let goal = nat_eq(Expr::const_str("Nat.zero"), Expr::const_str("Nat.zero"));

    let engine = AutomationEngine::new();
    assert!(
        engine
            .prove_by_induction(&env, &goal, Duration::from_secs(5))
            .is_none(),
        "induction lane should decline a non-forall goal"
    );
}
