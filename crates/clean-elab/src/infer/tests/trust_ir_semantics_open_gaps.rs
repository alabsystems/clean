// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OPEN gaps measured on trust-ir's Lean 4.8.0 semantics package, pinned as
//! REFUSALS through the production entry (`elaborate_decl_and_register`), each
//! filed in `docs/FRONTEND_CLASS_LEDGER.md`.
//!
//! (80), (81) and (83) are what the census's "Too many arguments: function
//! type `List.rec …`" (`Proofs/AggregateProps.lean`
//! `seqMapAddKList_roundTrip`, `seqMapNotList_involutive`) decomposes into
//! besides the unparsed `cases h : e` target (80 and 81 closed by round-5
//! lane B and pinned as PASS tests in `mutual_lift_cases.rs`): that message is what `cases h`
//! prints when the hypothesis it reads is stale or unreduced, a symptom, not a
//! class. Its fourth part, (82), is pinned in
//! `crates/clean-elab/src/tactic/simp/rec_equations_tests.rs`: PASS tests for
//! its recursive halves (equations synthesized for a minor carrying a redex
//! or `let`, and for a leading parameter generalized into the motive) and a
//! refusal for its open non-recursive half (`List.casesOn`). (88) is the
//! curried dependent match of `Proofs/BindingFrameProps.lean` and
//! `Proofs/AggregateProps.lean` `replicate_get?_of_lt`. (81) is CLOSED (G82,
//! ledger (152), 2026-10-16): `cases h` on a constructor equation runs Lean's
//! `unifyEqs?`; its PASS test and twins are in
//! `crates/clean-elab/src/tactic/cases_unify_eqs_tests.rs`. (80) is CLOSED
//! twice over: by round-5 lane B inside `cases_core` (R63) and on main on
//! 2026-10-21 at the `cases` tactic (R106, PASS tests with negative controls in
//! `crates/clean-elab/src/tests_mathbot_task_tactics.rs`); its old pin is the
//! PASS test below.
//!
//! Measured against the pinned Lean 4.8.0 binary, 2026-09-30: it accepts every
//! declaration pinned here as refused, except where a test says otherwise (the
//! (83) definition, which Lean rejects with a different message). Each test
//! fails the day its gap closes or changes shape: re-file the ledger entry in
//! that change and turn the pin into a PASS test with a negative control.

use super::*;

fn register(env: &mut Environment, src: &str) -> Result<(), ElabError> {
    let decl = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &decl).map(|_| ())
}

/// Refused, and not registered; returns the rendered error for the target
/// assertion.
fn refused(env: &mut Environment, name: &str, src: &str) -> String {
    let err = match register(env, src) {
        Ok(()) => panic!(
            "OPEN gap closed: `{name}` now elaborates. Re-file its \
             docs/FRONTEND_CLASS_LEDGER.md entry and turn this pin into a PASS \
             test with a negative control.\n{src}"
        ),
        Err(err) => format!("{err}"),
    };
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "a refused `{name}` must not be registered"
    );
    err
}

/// Class (80), CLOSED by round-5 lane B (`docs/DECISIONS.md` R63): `cases b`
/// reverts `h : b = true` and re-introduces it per case (`h : false = true` in
/// the `false` case), as pinned Lean 4.8.0 does, so `exact h` closes that case.
/// This was the class's open pin; at the round-6 integration it is the PASS
/// test, with the negative control below (Lean 4.8.0 refuses it: in the `true`
/// case `h : true = true` does not prove `true = false`).
#[test]
fn test_cases_dependent_hypothesis_is_specialized_class_80() {
    let mut env = Environment::with_prelude();
    register(
        &mut env,
        "theorem cases_dep_hyp (b : Bool) (h : b = true) : b = true := by
  cases b with
  | false => exact h
  | true => rfl",
    )
    .expect("pinned Lean 4.8.0 accepts it: `h` is specialized per case");
    let err = refused(
        &mut env,
        "cases_dep_hyp_twin",
        "theorem cases_dep_hyp_twin (b : Bool) (h : b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact h",
    );
    assert!(!err.is_empty(), "the twin is refused: {err}");
}

/// Class (83), DIAGNOSTIC: a `match` missing a constructor is refused, as in
/// Lean, but not as `missing cases`: the legacy lowering fills the FIRST
/// minor with the only arm's body and the partial `casesOn` fails as a type
/// mismatch.
#[test]
fn test_match_missing_constructor_reports_type_mismatch_open_class_83() {
    let mut env = Environment::with_prelude();
    let err = refused(
        &mut env,
        "missingNil",
        "def missingNil (x : List Nat) : Nat :=\n  match x with\n  | _ :: _ => 1",
    );
    assert!(
        err.contains("Type mismatch") && !err.contains("missing"),
        "the refusal is still the positional type mismatch, not `missing cases`: {err}"
    );
}

/// Class (88)'s trust-ir rows (`replicate_get?_of_lt` here; three
/// `BindingFrameProps` list lemmas) are still refused after brick B4: their
/// two matched columns put them on the matrix compiler's path, where the
/// first column's pattern variable `n` is an alias of a field, so `show
/// (List.replicate n v).get? i = …` beside `h` does not line up (class (88)'s
/// open face, `dep_column_alias_pin.lean`), and the builtin prelude's
/// `Nat.lt_of_succ_lt_succ` takes `n m` explicitly where Lean's are implicit.
/// The refusal is a type mismatch. (Until R157 it named a `Float` carrier
/// that an open instance goal took from the latest instance, which also let
/// the third arm's `show` line up; with that goal left stuck, the `show`
/// fails and the refusal reported is the first arm's.) Their next stop is G69 (the self-call
/// inside `by`). The first arm says `Nat.not_succ_le_zero`, which the
/// builtin prelude has, for trust-ir's `Nat.not_lt_zero`; pinned Lean 4.8.0
/// accepts both.
#[test]
fn test_curried_dependent_match_trust_ir_row_is_refused_open_class_88() {
    let mut env = Environment::with_prelude();
    let err = refused(
        &mut env,
        "replicate_get_of_lt",
        "theorem replicate_get_of_lt (v : Nat) :
    ∀ {n i : Nat}, i < n → (List.replicate n v).get? i = some v
  | 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, i + 1, h => by
    show (List.replicate n v).get? i = some v
    exact replicate_get_of_lt v (Nat.lt_of_succ_lt_succ h)",
    );
    assert!(
        err.contains("Type mismatch"),
        "the refusal is a type mismatch, not the column lowering: {err}"
    );
    assert!(
        !err.contains("curried dependent match"),
        "the hypothesis column is generalized now (B4): {err}"
    );
}
