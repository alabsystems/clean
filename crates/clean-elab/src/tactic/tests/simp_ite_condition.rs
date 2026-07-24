// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ite-condition congruence regressions (`ite_congruence_gap`).
//!
//! When simp rewrites the *condition* of an `@ite α c inst t e` to `True` /
//! `False`, it must collapse the `ite` to the taken branch via the kernel-checked
//! `if_pos` / `if_neg` lemmas — keeping the ORIGINAL symbolic `Decidable`
//! instance on the equation LHS so the rebuilt term is well-typed. The previous
//! generic App-congruence rewrote only the condition argument and left the
//! sibling `inst : Decidable c` stale, producing an ill-typed `congrArg`
//! equation the kernel rejected with a `TypeMismatch` at the `inst` position.
//!
//! Soundness boundary: TRUE goals close; FALSE goals (which collapse to an
//! unprovable `⊢ False`) must remain open. Both directions are asserted here.

use super::*;
use clean_kernel::Level;

/// Build `@ite.{1} Prop (Eq Nat n n) (Nat.decEq n n) <then> <else>`.
///
/// `n` is a free Nat variable (axiom `n : Nat`), so the condition `Eq Nat n n`
/// is symbolic — its `Decidable` instance `Nat.decEq n n` cannot ι-reduce on its
/// own. This is exactly the dependent-instance shape that triggered the bug.
fn mk_ite_self_eq(then_b: Expr, else_b: Expr) -> Expr {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    // c := @Eq.{1} Nat n n
    let cond = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat.clone(), n.clone(), n.clone()],
    );
    // inst := Nat.decEq n n : Decidable (Eq Nat n n)
    let inst = Expr::apps(
        Expr::const_(Name::from_string("Nat.decEq"), vec![]),
        [n.clone(), n],
    );
    // @ite.{1} Prop c inst then else
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [Expr::prop(), cond, inst, then_b, else_b],
    )
}

fn nat_var_env() -> Environment {
    let mut env = Environment::with_prelude();
    // free variable n : Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Nat"), vec![]),
    })
    .unwrap();
    env
}

/// `if n = n then True else False := by simp` — was a `TypeMismatch`, must now
/// close with a kernel-valid proof (no axioms, no sorry).
#[test]
fn test_simp_ite_true_condition_closes() {
    let env = nat_var_env();
    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    let goal = mk_ite_self_eq(true_c, false_c);

    let mut state = ProofState::new(env, goal.clone());
    let result = simp_default(&mut state);
    assert!(
        result.is_ok(),
        "simp should close `if n = n then True else False`, got {result:?}"
    );
    assert!(state.is_complete(), "goal must be fully closed after simp");

    // The extracted proof must type-check against the ORIGINAL goal in the kernel
    // (close_goal + add_decl equivalent): this is the soundness backstop.
    let proof = state
        .instantiated_proof()
        .expect("simp must produce an extractable proof term");
    let tc = TypeChecker::new(state.env());
    let checked = tc.check_type(&proof, &goal);
    assert!(
        checked.is_ok(),
        "the if_pos-collapse proof must kernel-check against `if n = n then True else False`, got {checked:?}"
    );

    // No trusted-axiom fallback was used to manufacture the proof.
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ite-condition collapse must not record trusted axiom usage"
    );
}

/// `if (0 : Nat) = 0 then True else False := by simp` — ground condition variant.
/// Tractable: the condition still simps to `True`, collapse fires.
#[test]
fn test_simp_ite_true_ground_condition_closes() {
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let cond = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat, zero.clone(), zero.clone()],
    );
    let inst = Expr::apps(
        Expr::const_(Name::from_string("Nat.decEq"), vec![]),
        [zero.clone(), zero],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            Expr::prop(),
            cond,
            inst,
            Expr::const_(Name::from_string("True"), vec![]),
            Expr::const_(Name::from_string("False"), vec![]),
        ],
    );

    let mut state = ProofState::new(env, goal.clone());
    let result = simp_default(&mut state);
    assert!(
        result.is_ok() && state.is_complete(),
        "simp should close `if (0:Nat) = 0 then True else False`, got {result:?}, complete={}",
        state.is_complete()
    );
    let proof = state.instantiated_proof().expect("proof term");
    let tc = TypeChecker::new(state.env());
    let checked = tc.check_type(&proof, &goal);
    assert!(
        checked.is_ok(),
        "ground if_pos-collapse proof must kernel-check, got {checked:?}"
    );
}

/// SOUNDNESS: `if n = n then False else True := by simp` equals `False` and is
/// NOT provable. simp collapses the ite to its THEN-branch `False` (condition is
/// `True`), leaving `⊢ False`; simp may make progress but must NOT close the
/// goal. If this test ever "passes" (goal closed), the fix is unsound.
#[test]
fn test_simp_ite_false_then_branch_stays_open() {
    let env = nat_var_env();
    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);
    // then = False, else = True  →  whole ite collapses to False (unprovable)
    let goal = mk_ite_self_eq(false_c, true_c);

    let mut state = ProofState::new(env, goal);
    let _ = simp_default(&mut state);
    assert!(
        !state.is_complete(),
        "SOUNDNESS VIOLATION: simp must NOT close `if n = n then False else True` (= False)"
    );
}

/// SOUNDNESS: `if n = 0 then True else False := by simp` — the condition
/// `n = 0` is NOT always true (n is a free variable), so it does not simp to
/// `True`/`False`, the ite is left untouched, and the goal stays open.
#[test]
fn test_simp_ite_non_reflexive_condition_stays_open() {
    let env = nat_var_env();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let cond = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat, n.clone(), zero.clone()],
    );
    let inst = Expr::apps(
        Expr::const_(Name::from_string("Nat.decEq"), vec![]),
        [n, zero],
    );
    let goal = Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            Expr::prop(),
            cond,
            inst,
            Expr::const_(Name::from_string("True"), vec![]),
            Expr::const_(Name::from_string("False"), vec![]),
        ],
    );

    let mut state = ProofState::new(env, goal);
    let _ = simp_default(&mut state);
    assert!(
        !state.is_complete(),
        "SOUNDNESS VIOLATION: simp must NOT close `if n = 0 then True else False` (n = 0 not always true)"
    );
}
