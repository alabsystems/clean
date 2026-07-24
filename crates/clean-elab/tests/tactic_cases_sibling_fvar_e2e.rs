// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **sibling-goal FVar numbering in `cases`**.
//!
//! `cases` (the And/structure destructure) numbered its branch field FVars from
//! the global monotonic `next_fvar` counter. When two SIBLING goals are each
//! proved by an `intro h; cases h` chain — the canonical shape being the two
//! `Iff.intro` subgoals produced by `constructor`/`split` on an `Iff` goal — the
//! first sibling advanced `next_fvar`, so the second sibling's field FVars were
//! numbered too high for the minor-premise binder depth they occupy. `close_fvars`
//! (`(n - base) < depth`) then could not bind them, leaving a residual tactic
//! FVar: `closed_proof()` returned `None` and the whole proof failed with
//! `ProofNotProduced` — *even though every goal had closed*.
//!
//! The fix numbers `cases`' field FVars from the GOAL's own context
//! (`goal_fvar_base`, one past the highest tactic FVar bound in that goal), the
//! same depth-correct base `intro` already uses (#2533). Sibling goals with
//! matching contexts then get identical field ids at identical depths, and
//! `close_fvars` binds them cleanly.
//!
//! The most visible symptom was `by tauto` failing on EVERY compound `Iff`
//! (`tauto`'s Iff branch proves each side via `intro h; cases h`), while proving
//! each implication direction individually and while `constructor <;> tauto`
//! worked. These gates lock that class shut, kernel-rechecked.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each drives the real `clean check` pipeline (`parse_file_with_tactics →
//! preprocess_decl_with_context → elaborate_decl_and_register`; patterns matter
//! for bullet/`<;>` grouping) and asserts the theorem registers (kernel
//! re-derives the assembled `Iff.intro`/`casesOn` term), its proof `infer`s a
//! def-eq type, and its axiom closure carries no `sorry`.

use std::collections::BTreeSet;

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file_with_tactics;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let patterns = builtin_tactic_patterns();
    let decls =
        parse_file_with_tactics(source, &patterns).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (last decl `name`, tactic-proved) and assert it
/// kernel-checks, infers a def-eq type, and its axiom closure ⊆ `allowed`.
fn assert_kernel_checks(name: &str, source: &str, allowed: &[&str]) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` must carry a proof value"));

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    let allowed_set: BTreeSet<Name> = allowed.iter().map(|s| Name::from_string(s)).collect();
    for dep in &deps {
        assert!(
            allowed_set.contains(dep),
            "`{name}` axiom closure must be ⊆ {allowed:?}; found `{dep:?}` (full: {deps:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// GATE 1 — the headline: `tauto` on a reflexive compound Iff. tauto splits the
// Iff into two implication siblings and proves each by `intro h; cases h` —
// exactly the sibling-fvar shape that regressed. Pre-fix: ProofNotProduced.
// ---------------------------------------------------------------------------

#[test]
fn tauto_reflexive_compound_iff() {
    assert_kernel_checks(
        "iff_and_refl",
        "theorem iff_and_refl (a b : Prop) : (a ∧ b) ↔ (a ∧ b) := by tauto",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE 2 — And-commutativity as an Iff: the two siblings destructure `h : a∧b`
// and rebuild in swapped order. Confirms the field FVars close in BOTH branches.
// ---------------------------------------------------------------------------

#[test]
fn tauto_and_comm_iff() {
    assert_kernel_checks(
        "iff_and_comm",
        "theorem iff_and_comm (a b : Prop) : (a ∧ b) ↔ (b ∧ a) := by tauto",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE 3 — the underlying primitive, without tauto: `constructor` splits the
// Iff into two sibling goals, `<;>` runs the SAME `intro h; cases h; ...` on
// each. This is the minimal reproduction of the sibling-fvar bug.
// ---------------------------------------------------------------------------

#[test]
fn constructor_then_cases_on_both_siblings() {
    assert_kernel_checks(
        "iff_manual_cases",
        "theorem iff_manual_cases (a b : Prop) : (a ∧ b) ↔ (b ∧ a) := by \
         constructor <;> (intro h; cases h; constructor <;> assumption)",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE 4 — regression: single-goal `intro h; cases h` (no siblings) still works
// (the path that was always fine — guards against the fix over-reaching).
// ---------------------------------------------------------------------------

#[test]
fn single_goal_intro_cases_still_works() {
    assert_kernel_checks(
        "and_comm_impl",
        "theorem and_comm_impl (a b : Prop) : (a ∧ b) → (b ∧ a) := by \
         intro h; cases h; constructor <;> assumption",
        &[],
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE — the fix must not make a false Iff provable: `(a ∧ b) ↔ a`
// is not a tautology, so `tauto` must still fail closed.
// ---------------------------------------------------------------------------

#[test]
fn tauto_rejects_false_iff() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem iff_bad (a b : Prop) : (a ∧ b) ↔ a := by tauto",
    );
    assert!(
        result.is_err(),
        "`(a ∧ b) ↔ a` is not a tautology; `tauto` must fail closed"
    );
}
