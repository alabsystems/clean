// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for the **named-case tactic** `case <tag> => <tac>`
//! and its binder form `case <tag> x₁ … xₙ => <tac>`.
//!
//! ## The gap
//!
//! A bare `cases n` / `induction n` (no `with`-clause) leaves the constructor
//! subgoals *tagged* (`zero`, `succ`, …). Lean's separate `case` tactic then
//! focuses the goal carrying a given tag, optionally renaming the case's
//! most-recently-introduced inaccessible hypotheses to user names, runs the
//! tactics on that goal, and REQUIRES the goal to be solved:
//!
//! ```text
//! theorem t (n : Nat) : n = n := by
//!   cases n
//!   case zero => rfl
//!   case succ k => rfl
//! ```
//!
//! Before the fix the binder form (`case succ k => …`) was unparseable — the
//! parser only accepted `case <tag> => <tac>` — so the whole proof degraded to
//! a synthetic `sorry`. The parser now accepts `caseArg := binderIdent
//! (ppSpace binderIdent)*` (Lean `Init.Notation`), and the `case` handler
//! renames the auto-generated field/IH hypotheses positionally and fails when
//! the focused case is left open.
//!
//! ## Why these are genuine proofs (not `sorry`)
//!
//! Each positive theorem drives the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`)
//! and asserts the kernel re-derives the proof's type def-eq to the stated
//! proposition, with an axiom closure that is a subset of the foundational set
//! (`cases`/`induction` introduce the constructor recursors, which are not
//! axioms — the closure here is empty).
//!
//! The DECISIVE NEGATIVES prove `case` fails closed: an unknown tag and a
//! non-closing tactic body must each ERROR (never fabricate a proof, never
//! panic).

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
// GATE case-a — THE GAP: bare `cases n` then `case zero`/`case succ k` (binder).
// Before the fix the `case succ k =>` binder form was unparseable → synthetic
// `sorry`. It must now PARSE, focus the tagged goal, and close it.
// ---------------------------------------------------------------------------

#[test]
fn case_named_cases_with_binder_closes() {
    assert_tactic_theorem_axioms(
        "case_cases_binder",
        "theorem case_cases_binder (n : Nat) : n = n := by\n  cases n\n  case zero => rfl\n  case succ k => rfl",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE case-b — the same, via `induction n`. `induction` tags its goals and
// names the IH `ih_succ_0`; `case succ k ih => rfl` renames field `k` and the
// IH `ih`. (The base proof here does not use the IH; it just confirms the
// binders parse and the goal closes.)
// ---------------------------------------------------------------------------

#[test]
fn case_named_induction_with_binders_closes() {
    assert_tactic_theorem_axioms(
        "case_induction_binder",
        "theorem case_induction_binder (n : Nat) : n = n := by\n  induction n\n  case zero => rfl\n  case succ k ih => rfl",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE case-c — Bool `cases b` with the binder-free form `case false`/`case true`.
// Confirms the plain (no-binder) named-case path still works.
// ---------------------------------------------------------------------------

#[test]
fn case_named_bool_no_binder_closes() {
    assert_tactic_theorem_axioms(
        "case_bool",
        "theorem case_bool (b : Bool) : b = b := by\n  cases b\n  case false => rfl\n  case true => rfl",
        &[],
    );
}

// ---------------------------------------------------------------------------
// GATE case-d — the EXISTING `cases n with | zero => … | succ k => …` form must
// still work (the named-case fix must not regress the with-clause path).
// ---------------------------------------------------------------------------

#[test]
fn cases_with_clause_still_closes() {
    assert_tactic_theorem_axioms(
        "case_with_clause",
        "theorem case_with_clause (n : Nat) : n = n := by\n  cases n with\n  | zero => rfl\n  | succ k => rfl",
        &[],
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 1 — an UNKNOWN case tag must ERROR (no over-accept, no panic).
// `case nonexistent => rfl` has no matching tagged goal; the proof MUST fail.
// ---------------------------------------------------------------------------

#[test]
fn case_unknown_tag_errors() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem case_bad_tag (n : Nat) : n = n := by\n  cases n\n  case nonexistent => rfl\n  case succ k => rfl",
    );
    assert!(
        result.is_err(),
        "`case nonexistent` names no tagged goal; the proof MUST fail (no over-accept)"
    );
}

// ---------------------------------------------------------------------------
// DECISIVE NEGATIVE 2 — a non-closing case body must ERROR (no over-accept, no
// panic). `case zero => skip` focuses the `zero` goal but leaves it open;
// Lean's `case` requires the focused goal solved, so the proof MUST fail.
// ---------------------------------------------------------------------------

#[test]
fn case_unclosed_body_errors() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "theorem case_no_close (n : Nat) : n = n := by\n  cases n\n  case zero => skip\n  case succ k => rfl",
    );
    assert!(
        result.is_err(),
        "`case zero => skip` leaves the `zero` goal OPEN; `case` requires closure, so this MUST fail"
    );
}
