// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `refine ⟨?_, ?_⟩` — anonymous constructor with `?_`
//! synthetic-metavariable holes.
//!
//! These exercise the full parse -> elaborate -> kernel-type-check path. The
//! gap they pin: `?_` was lexed as `Error(UnexpectedChar('?'))` and recovered
//! into a bare `Hole`, so `?_` glued into `App(Hole, [Hole])` — applying the
//! `?`-hole metavariable to the `_`-hole argument. Inside the anonymous
//! constructor that surfaced as `TooManyArguments { func_type: FVar(meta) }`.
//!
//! The fix lexes `?` as a real `Question` token and parses an immediately
//! adjacent `?_`/`?name` as a single synthetic `Hole`. Each `?_` field then
//! becomes a fresh metavariable that the `refine` bridge collects into its own
//! goal — `refine ⟨?_, ?_⟩` against `p ∧ q` leaves exactly `⊢ p` and `⊢ q`.
//!
//! SOUNDNESS: every hole becomes a real goal carrying the correct field type;
//! the assembled proof term is kernel-rechecked by `add_decl`. The negative
//! tests confirm the holes are NOT silently dropped or filled with a wrong
//! term: an unfilled `∃` witness leaves goals (does not falsely close), and a
//! wrong fill for the second field is rejected.

use super::common::check_and_add_decl;
use clean_kernel::{Declaration, Environment, Expr, Name};

/// Logic environment: And, Exists, Eq, Nat, and props p/q.
fn setup_logic_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_exists().expect("init_exists");
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");

    let prop = Expr::prop();
    for name in ["p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }
    env
}

#[test]
fn test_refine_anon_ctor_two_holes_kernel_accepts() {
    // The confirmed repro: refine ⟨?_, ?_⟩ on ⊢ p ∧ q, each hole closed by
    // assumption. Previously failed with TooManyArguments on the ?-hole metavar.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem refine_pair (hp : p) (hq : q) : And p q := by refine ⟨?_, ?_⟩ <;> assumption",
    );
    assert!(
        result.is_ok(),
        "refine ⟨?_, ?_⟩ <;> assumption on `p ∧ q` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_refine_anon_ctor_three_holes_flatten_kernel_accepts() {
    // Flattening (commit 6707fdc5) + 3 holes: ⟨?_, ?_, ?_⟩ right-nests against
    // the 2-field And `a ∧ (b ∧ c)` and must leave exactly 3 goals.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem refine_triple (hp : p) (hq : q) : And p (And q q) := by refine ⟨?_, ?_, ?_⟩ <;> assumption",
    );
    assert!(
        result.is_ok(),
        "refine ⟨?_, ?_, ?_⟩ on a right-nested 3-tuple should flatten + leave 3 goals, got: {result:?}"
    );
}

#[test]
fn test_refine_anon_ctor_mixed_concrete_and_hole_kernel_accepts() {
    // Mixed: the first field is a concrete term, the second is a `?_` hole that
    // a follow-up `exact` closes. Concrete + hole must coexist in one ctor.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem refine_mixed (hp : p) (hq : q) : And p q := by\n  refine ⟨hp, ?_⟩\n  exact hq",
    );
    assert!(
        result.is_ok(),
        "refine ⟨hp, ?_⟩ then `exact hq` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_refine_exists_holes_leaves_goals_does_not_falsely_close() {
    // refine ⟨?_, ?_⟩ on ∃ n : Nat, n = 0 leaves both the witness and the proof
    // goal open. With no follow-up tactic the proof is INCOMPLETE — this must
    // be an error (unsolved goals), never a silently-accepted proof. Confirms
    // holes are not dropped / auto-closed.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem refine_exists_open : Exists (fun n : Nat => Eq n 0) := by refine ⟨?_, ?_⟩",
    );
    assert!(
        result.is_err(),
        "refine ⟨?_, ?_⟩ on ∃ with no fill must leave goals (not falsely close): {result:?}"
    );
}

#[test]
fn test_exact_concrete_exists_witness_kernel_accepts() {
    // The concrete-argument anonymous constructor still works: `exact ⟨0, rfl⟩`
    // proves ∃ n : Nat, n = 0. (Guards that the parser change did not regress
    // concrete ⟨…⟩.)
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem exact_exists : Exists (fun n : Nat => Eq n 0) := by exact ⟨0, rfl⟩",
    );
    assert!(
        result.is_ok(),
        "exact ⟨0, rfl⟩ on ∃ n, n = 0 should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_refine_holes_wrong_fill_errors_not_panics() {
    // The holes carry the correct field types: filling the SECOND hole (type q)
    // with a proof of `p` must be rejected. Over-acceptance would mean the hole
    // type was lost. Must error, never panic, never kernel-accept.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem refine_wrong_fill (hp : p) : And p q := by\n  refine ⟨?_, ?_⟩\n  exact hp\n  exact hp",
    );
    assert!(
        result.is_err(),
        "second `exact hp` fills the q-typed hole with a p-proof; must error: {result:?}"
    );
}
