// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for the **generalized** structural-induction lane in
//! `clean-auto` — induction over `List` (and, by the same generic recursor
//! path, any registered non-mutual, index-free inductive), not just `Nat`.
//!
//! Companion to `auto_induction.rs` (the `Nat` lane). Lives in `clean-cli` for
//! the same reason: `clean-auto`'s lib *test* binary pulls in the
//! trust-cg/trust-ir dev-dependencies; `clean-cli` depends only on `clean-auto`'s
//! *lib*, so it drives the public `AutomationEngine` surface without that dep.
//!
//! SOUNDNESS (load-bearing): the induction lane is on the *search* side, not the
//! TCB. Each test re-checks the emitted proof term through the kernel
//! (`TypeChecker::infer_type` + `is_def_eq` against the goal) and asserts the
//! term's head is the genuine recursor (`List.rec` / `Nat.rec`) — never a
//! `sorry`/axiom. The generic assembly builds the recursor with the correct
//! parameter and universe instantiation; a wrong one would fail these checks.

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, Level, Name, TypeChecker,
};

fn lvl0() -> Level {
    Level::zero()
}
fn lvl1() -> Level {
    Level::succ(Level::zero())
}
fn nat() -> Expr {
    Expr::const_str("Nat")
}
/// `List Nat` (`List.{0} Nat`).
fn list_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List", vec![lvl0()]), [nat()])
}
/// `@List.nil Nat`.
fn nil_nat() -> Expr {
    Expr::apps(Expr::const_str_levels("List.nil", vec![lvl0()]), [nat()])
}
/// `@List.cons Nat h t`.
fn cons_nat(h: Expr, t: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("List.cons", vec![lvl0()]),
        [nat(), h, t],
    )
}
/// `@Eq.{1} (List Nat) l r` (`List Nat : Type 0 = Sort 1`).
fn eq_list(l: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![lvl1()]),
        [list_nat(), l, r],
    )
}
/// `List.append a b`.
fn append(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("List.append"), [a, b])
}

/// Environment with Nat, Eq, List (so `List.rec` exists), the classical
/// bootstrap the SMT bridge expects, and a reducible
/// `List.append : List Nat → List Nat → List Nat` recursing on its first
/// argument (`[] ++ ys = ys`, `(h::t) ++ ys = h :: (t ++ ys)`).
fn list_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_list().expect("init_list");
    env.init_classical().expect("init_classical");
    register_append(&mut env);
    env
}

/// `List.append := fun xs ys => @List.rec.{1,0} Nat (fun _ => List Nat) ys
/// (fun h t ih => List.cons Nat h ih) xs`.
fn register_append(env: &mut Environment) {
    let list_nat = list_nat();
    let ty = Expr::pi(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::pi(BinderInfo::Default, list_nat.clone(), list_nat.clone()),
    );

    let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), list_nat.clone());
    // fun (h : Nat) (t : List Nat) (ih : List Nat) => List.cons Nat h ih
    let cons_body = cons_nat(Expr::bvar(2), Expr::bvar(0));
    let cons_case = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(
            BinderInfo::Default,
            list_nat.clone(),
            Expr::lam(BinderInfo::Default, list_nat.clone(), cons_body),
        ),
    );
    // @List.rec.{1,0} Nat motive ys cons_case xs   (xs = BVar1, ys = BVar0)
    let body = Expr::apps(
        Expr::const_str_levels("List.rec", vec![lvl1(), lvl0()]),
        [nat(), motive, Expr::bvar(0), cons_case, Expr::bvar(1)],
    );
    let value = Expr::lam(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::lam(BinderInfo::Default, list_nat, body),
    );

    env.add_decl(Declaration::Definition {
        name: Name::from_string("List.append"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .expect("register List.append");
}

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

/// Assert the proof term's application head is the named recursor constant
/// (a genuine induction proof, not a `sorry`/axiom).
fn assert_head_const(term: &Expr, expected: &str, what: &str) {
    match term.get_app_fn().kind() {
        ExprKind::Const(name, _) => assert_eq!(
            name.to_string(),
            expected,
            "[{what}] proof head should be {expected}, got {name}"
        ),
        other => panic!("[{what}] proof head is not a constant: {other:?}"),
    }
}

/// Sanity: the hand-built `List.append` actually computes (`[] ++ [] = []`).
#[test]
fn test_append_definition_reduces() {
    let env = list_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&append(nil_nat(), nil_nat()), &nil_nat()),
        "append [] [] should reduce to []"
    );
}

/// `∀ (l : List Nat), l ++ [] = l` — REQUIRES induction (`List.append` recurses
/// on its first argument, so `l ++ []` is stuck for a free `l`; reflexivity and
/// EUF cannot close it). The lane assembles a genuine `List.rec` application
/// (correct parameter `Nat` + levels `{0,0}`) that KERNEL-CHECKS.
#[test]
fn test_induction_list_append_nil_kernel_checks() {
    let env = list_env();
    let goal = Expr::pi(
        BinderInfo::Default,
        list_nat(),
        eq_list(append(Expr::bvar(0), nil_nat()), Expr::bvar(0)),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, Duration::from_secs(30))
        .expect("∀ l, l ++ [] = l should be provable by induction");

    assert_head_const(result.proof_term(), "List.rec", "l++[]=l");
    assert_kernel_checks(&env, result.proof_term(), &goal, "l++[]=l");
}

/// The full `auto_prove` pipeline (router-driven) routes the `∀ (l:List Nat)`
/// goal to the induction lane and returns a kernel-checking `List.rec` proof.
#[test]
fn test_auto_prove_routes_list_to_induction() {
    let env = list_env();
    let goal = Expr::pi(
        BinderInfo::Default,
        list_nat(),
        eq_list(append(Expr::bvar(0), nil_nat()), Expr::bvar(0)),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .auto_prove(&env, &goal, Duration::from_secs(30), None)
        .expect("auto_prove should solve ∀ l, l ++ [] = l via the induction lane");

    assert_head_const(result.proof_term(), "List.rec", "auto_prove l++[]=l");
    assert_kernel_checks(&env, result.proof_term(), &goal, "auto_prove l++[]=l");
}

/// Regression: `Nat` induction still works through the generalized lane —
/// `∀ (n : Nat), 0 + n = n` assembles a genuine `Nat.rec` proof.
#[test]
fn test_induction_nat_still_works_after_generalization() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    env.init_classical().expect("init_classical");

    let nat_eq =
        |l: Expr, r: Expr| Expr::apps(Expr::const_str_levels("Eq", vec![lvl1()]), [nat(), l, r]);
    let nat_add = |a: Expr, b: Expr| Expr::apps(Expr::const_str("Nat.add"), [a, b]);
    let goal = Expr::pi(
        BinderInfo::Default,
        nat(),
        nat_eq(
            nat_add(Expr::const_str("Nat.zero"), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    );

    let engine = AutomationEngine::new();
    let result = engine
        .prove_by_induction(&env, &goal, Duration::from_secs(30))
        .expect("∀ n, 0 + n = n should be provable by induction");
    assert_head_const(result.proof_term(), "Nat.rec", "0+n=n");
    assert_kernel_checks(&env, result.proof_term(), &goal, "0+n=n");
}

/// The lane declines a goal whose `∀` domain is not a registered index-free
/// inductive (here: a non-forall equality goal).
#[test]
fn test_induction_declines_non_inductive_goal() {
    let env = list_env();
    let goal = eq_list(nil_nat(), nil_nat());
    let engine = AutomationEngine::new();
    assert!(
        engine
            .prove_by_induction(&env, &goal, Duration::from_secs(5))
            .is_none(),
        "induction lane should decline a non-forall goal"
    );
}
