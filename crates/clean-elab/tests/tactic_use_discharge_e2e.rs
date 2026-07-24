// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for the **`use` / `exists` side-goal discharge**.
//!
//! Lean/Mathlib's `use` supplies the existential witnesses and then runs a small
//! discharger (`try (with_reducible rfl); try trivial`) so the residual goal —
//! which frequently collapses to a reflexive equality or `True` after
//! substitution — does not have to be closed by hand.
//!
//! Clean's `use` (dispatched to `term_close::use_`) previously stopped after
//! `existsi` and left the trivial residual open: `theorem t : ∃ n : Nat, n = 0
//! := by use 0` failed with `UnsolvedGoals` leaving `⊢ 0 = 0`. This test locks
//! in the conservative discharger (reducible `rfl`, then a `True.intro`-style
//! no-argument constructor) that closes exactly those trivial side goals.
//!
//! A second, orthogonal fix is also exercised here: when the existential binder
//! type is *elided* (`∃ n, p n`), elaboration could leave the goal carrying an
//! unsolved universe-level metavariable (`Exists.{?u} Nat …`). `existsi` now
//! commits that level constraint (via the unifier, like `exact`) and realizes it
//! into the goal/sub-goal targets, so `use`/`exists` work on inferred-type
//! existentials too.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each positive theorem carries a real tactic proof; the test drives the SAME
//! pipeline as `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register`) and asserts, for every positive gate:
//!   * the theorem registers (the kernel re-checks the assembled term),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is empty — the discharge introduces
//!     no axioms (it is pure `Exists.intro` + `Eq.refl` / `True.intro`).
//!
//! The DECISIVE NEGATIVE gates prove the discharge fails closed: it must NOT
//! falsely close `0 = 5`, and it must NOT consume a non-trivial residual goal
//! (a conjunction, or a `p 3` goal the user closes explicitly with `exact h`).

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline for a (possibly multi-declaration) source.
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (defining `name` last as a tactic-proved theorem) and
/// assert it kernel-checks, infers a def-eq type, and its axiom closure is a
/// subset of `allowed`.
fn assert_tactic_theorem_axioms(name: &str, source: &str, allowed: &[&str]) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — kernel re-derives the proof's type, def-eq to the stated prop.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — axiom_deps closure ⊆ allowed.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    let allowed_set: BTreeSet<Name> = allowed.iter().map(|s| Name::from_string(s)).collect();
    for dep in &deps {
        assert!(
            allowed_set.contains(dep),
            "`{name}` axiom closure must be ⊆ {allowed:?}; found disallowed axiom `{dep:?}` \
             (full closure: {deps:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// GATE use-a — THE GAP: `use 0` discharges the reflexive residual `0 = 0`.
// Before the fix this failed with `UnsolvedGoals { count: 1 }` leaving `⊢ 0 = 0`.
// ---------------------------------------------------------------------------

#[test]
fn use_discharges_reflexive_equality() {
    assert_tactic_theorem_axioms(
        "use_refl_eq",
        "theorem use_refl_eq : ∃ n : Nat, n = 0 := by use 0",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE use-b — the residual is reflexive only AFTER reduction (`0 + 1 = 1`).
// The reducible `rfl` discharger reduces `0 + 1` to `1` and closes it.
// ---------------------------------------------------------------------------

#[test]
fn use_discharges_reflexive_after_reduction() {
    assert_tactic_theorem_axioms(
        "use_refl_reduce",
        "theorem use_refl_reduce : ∃ n : Nat, n + 1 = 1 := by use 0",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE use-c — nested witnesses `use 0, 0` leave `0 = 0`, closed by the
// discharge. Confirms the discharge runs once after ALL witnesses.
// ---------------------------------------------------------------------------

#[test]
fn use_nested_witnesses_discharge_equality() {
    assert_tactic_theorem_axioms(
        "use_nested",
        "theorem use_nested : ∃ x y : Nat, x = y := by use 0, 0",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE use-d — `True` residual is closed by the `True.intro`-style no-argument
// constructor branch of the discharger.
// ---------------------------------------------------------------------------

#[test]
fn use_discharges_true_residual() {
    assert_tactic_theorem_axioms(
        "use_true",
        "theorem use_true : ∃ _n : Nat, True := by use 0",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE use-e — ELIDED binder type (`∃ n, p n`): the witness step itself used to
// fail with a universe-level mismatch (`Exists.{?u}` vs `Exists.{1}`). `use 3`
// must now provide the witness, and the explicit `exact h` closes the (genuinely
// non-trivial) residual `p 3` — the discharge must NOT eat it.
// ---------------------------------------------------------------------------

#[test]
fn use_inferred_binder_type_with_explicit_proof() {
    assert_tactic_theorem_axioms(
        "use_inferred",
        "theorem use_inferred (p : Nat → Prop) (h : p 3) : ∃ n, p n := by use 3; exact h",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE use-f — the `exists` keyword (bare `existsi` path) gets the same universe
// fix: `exists 3; exact h` works on an inferred-type existential.
// ---------------------------------------------------------------------------

#[test]
fn exists_inferred_binder_type_with_explicit_proof() {
    assert_tactic_theorem_axioms(
        "exists_inferred",
        "theorem exists_inferred (p : Nat → Prop) (h : p 3) : ∃ n, p n := by exists 3; exact h",
        &[],
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 1 — the discharge must NOT falsely close a FALSE equality.
// `use 0` on `∃ n, n = 5` leaves `0 = 5`; reducible `rfl` cannot prove it, so the
// whole proof MUST fail (leaving the goal open), never fabricate a proof.
// ---------------------------------------------------------------------------

#[test]
fn use_does_not_close_false_equality() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem use_false_eq : ∃ n : Nat, n = 5 := by use 0",
    );
    assert!(
        result.is_err(),
        "use 0 leaves `0 = 5`, which rfl cannot prove; this proof MUST fail \
         (else the discharge over-accepts)"
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 2 — the discharge must NOT consume a genuinely non-trivial
// residual goal. `use 3` on `∃ n, p n` leaves `p 3`; there is a hypothesis
// `h : p 3` in context, but the conservative discharger deliberately does NOT
// run `assumption`, so `p 3` stays open. Without a following `exact h` the proof
// MUST fail with the residual still open (otherwise a later `exact h` would have
// no goal — proving the discharge did not silently eat it).
// ---------------------------------------------------------------------------

#[test]
fn use_leaves_nontrivial_residual_open() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem use_leaves_open (p : Nat → Prop) (h : p 3) : ∃ n, p n := by use 3",
    );
    assert!(
        result.is_err(),
        "use 3 must leave the non-trivial `p 3` goal OPEN (the discharge must not \
         run `assumption`); without `exact h` the proof must fail"
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 3 — the discharge must not "succeed" by SPLITTING a goal.
// `use 0` on `∃ n, n = 0 ∧ n = 0` leaves a conjunction `0 = 0 ∧ 0 = 0`; the
// no-argument-constructor branch is guarded to accept only when the goal count
// strictly DECREASES, so it must NOT fire here (that would leave the two
// conjuncts open while claiming success). The proof MUST fail.
// ---------------------------------------------------------------------------

#[test]
fn use_does_not_fake_close_conjunction() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem use_conj : ∃ n : Nat, n = 0 ∧ n = 0 := by use 0",
    );
    assert!(
        result.is_err(),
        "use 0 leaves the conjunction `0 = 0 ∧ 0 = 0`; the constructor discharge \
         must not fire (it would leave two subgoals open), so this MUST fail"
    );
}
