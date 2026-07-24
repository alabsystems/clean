// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for **universe-polymorphic** premise injection in
//! `clean-auto`'s `try_premise_injection` lane.
//!
//! The injection lane previously skipped any premise carrying universe
//! parameters (`@C` needs no level args only when monomorphic). This test
//! exercises the added universe-poly path: a polymorphic lemma `L.{u}` is
//! instantiated at a candidate level drawn from the goal and injected as
//! `@L.{ℓ}`.
//!
//! SOUNDNESS (load-bearing): the level instantiation is *guessed* from a small
//! bounded menu, never trusted. The test asserts the emitted proof term
//! KERNEL-CHECKS against the goal (`infer_type` + `is_def_eq`), so a wrong-level
//! instantiation could never pass — it would fail the kernel re-check and the
//! lane would return `None`.

use std::time::Duration;

use clean_auto::premise::PremiseDatabase;
use clean_auto::AutomationEngine;
use clean_kernel::{Declaration, Environment, Expr, Level, Name, TypeChecker};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn add_axiom(env: &mut Environment, n: &str, level_params: Vec<Name>, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: name(n),
        level_params,
        type_,
    })
    .unwrap_or_else(|e| panic!("axiom `{n}` should type-check: {e:?}"));
}

/// `@Eq.{lvl} ty l r`.
fn eq_at(lvl: Level, ty: Expr, l: Expr, r: Expr) -> Expr {
    Expr::apps(Expr::const_str_levels("Eq", vec![lvl]), [ty, l, r])
}

/// Env with `Eq`, a universe-polymorphic carrier `B.{u} : Sort u`, elements
/// `x.{u} y.{u} : B.{u}`, and a universe-polymorphic lemma
/// `L.{u} : @Eq.{u} B x y`. Returns the env, a premise DB containing `L`, and
/// the goal — the `u := 1` instance, which only the correctly-leveled `@L.{1}`
/// closes.
fn poly_env_and_db() -> (Environment, PremiseDatabase, Expr) {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");

    let u = || Level::param(name("u"));
    let su = || Expr::sort(u());

    add_axiom(&mut env, "B", vec![name("u")], su());
    let b_u = || Expr::const_str_levels("B", vec![u()]);
    add_axiom(&mut env, "x", vec![name("u")], b_u());
    add_axiom(&mut env, "y", vec![name("u")], b_u());
    let x_u = || Expr::const_str_levels("x", vec![u()]);
    let y_u = || Expr::const_str_levels("y", vec![u()]);

    let l_type = eq_at(u(), b_u(), x_u(), y_u());
    add_axiom(&mut env, "L", vec![name("u")], l_type.clone());

    let mut db = PremiseDatabase::new();
    db.add(name("L"), l_type);

    let one = Level::succ(Level::zero());
    let goal = eq_at(
        one.clone(),
        Expr::const_str_levels("B", vec![one.clone()]),
        Expr::const_str_levels("x", vec![one.clone()]),
        Expr::const_str_levels("y", vec![one]),
    );

    (env, db, goal)
}

/// Baseline: without the lemma, the goal is unprovable.
#[test]
fn test_poly_goal_unprovable_without_premises() {
    let (env, _db, goal) = poly_env_and_db();
    let engine = AutomationEngine::new();
    assert!(
        engine
            .auto_prove(&env, &goal, Duration::from_secs(10), None)
            .is_none(),
        "universe-poly goal must be unprovable without the lemma"
    );
}

/// With the DB, the injection lane instantiates `L` at the goal's level
/// (`u := 1`), and the closed `@L.{1}` proof KERNEL-CHECKS against the goal.
#[test]
fn test_univpoly_premise_injection_kernel_checks() {
    let (env, db, goal) = poly_env_and_db();

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove_with_premises(&env, &goal, Vec::new(), &db, Duration::from_secs(20), None)
        .expect("universe-poly lemma injection should close the goal");

    let proof_term = result.proof_term();
    assert!(
        result.proof_context().is_none(),
        "a closed-goal injected proof must itself be closed"
    );
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof_term)
        .unwrap_or_else(|e| panic!("injected universe-poly proof failed to type-check: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &goal),
        "injected universe-poly proof kernel-checks to {inferred:?}, not the goal {goal:?}"
    );
}
