// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the tactic-mode `let` binding.
//!
//! These drive the FULL surface pipeline (`elaborate_decl_and_register`), the
//! same one `clean check` uses, and assert that `let x : T := v` (and the
//! type-inferred `let x := v`) introduces a *local definition* whose value is
//! retained and **body-visible** — i.e. `x` is definitionally equal to `v` and
//! zeta-reduces during def-eq, exactly like Lean 4's `let` tactic (and unlike
//! `have`, which forgets the value).
//!
//! Root cause this guards against: the `let` tactic dispatcher previously routed
//! to `have_` (opaque), and the ProofState → ElabCtx bridge dropped
//! `LocalDecl.value`, so `x` reached subsequent term elaboration as a rigid,
//! value-less local. The assembled proof term is `let x : T := v; <rest>` and is
//! kernel-rechecked by `add_decl`, so a value that does not type-check at `T`
//! must ERROR (never over-accept, never panic).

use crate::elaborate_decl_and_register;
use clean_kernel::Environment;
use clean_parser::parse_decl;

/// Elaborate + register a single declaration through the full pipeline.
fn check_decl(src: &str) -> Result<(), crate::ElabError> {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(src).expect("declaration must parse");
    elaborate_decl_and_register(&mut env, &decl).map(|_| ())
}

#[test]
fn test_let_tactic_typed_value_exact_passes() {
    // `let x : Nat := 5; exact x` — typed let, then close the Nat goal with x.
    check_decl("def t : Nat := by let x : Nat := 5; exact x")
        .expect("typed `let` then `exact x` should close the Nat goal");
}

#[test]
fn test_let_tactic_inferred_value_exact_passes() {
    // `let x := 5; exact x` — type inferred from the value.
    check_decl("def t : Nat := by let x := 5; exact x")
        .expect("type-inferred `let` then `exact x` should close the Nat goal");
}

#[test]
fn test_let_tactic_does_not_obstruct_rfl_goal() {
    // The let-binding sits in context but does not block `rfl` on `5 = 5`.
    check_decl("theorem t : (5 : Nat) = 5 := by let x : Nat := 5; rfl")
        .expect("`let` must not obstruct `rfl` on the goal");
}

#[test]
fn test_let_tactic_value_usable_in_arithmetic() {
    // Decisive (body-visible / usable): `x + 0` must elaborate and reduce.
    check_decl("def t : Nat := by let x : Nat := 5; exact x + 0")
        .expect("the let value must be usable in `x + 0`");
}

#[test]
fn test_let_tactic_value_reduces_under_rfl_ascription() {
    // DECISIVE body-visibility: `x` (let-bound to 2) must zeta-reduce to `2`,
    // so `(rfl : x = 2)` type-checks. With an opaque `have`-style binding this
    // would only yield `x = x` and fail. Cross-checked against real Lean 4.
    check_decl("example : (2 : Nat) = 2 := by let x : Nat := 2; exact (rfl : x = 2)")
        .expect("let-bound x must be def-eq to its value 2 (body-visible)");
}

#[test]
fn test_let_tactic_wrong_rfl_value_errors_no_overaccept() {
    // NEGATIVE control: `x` reduces to `2`, NOT `3`. `(rfl : x = 3)` must be
    // REJECTED — proving the binding is a genuine definition (it reduces and
    // is checked), not an opaquely-accepted hypothesis. Real Lean 4 also rejects.
    let result = check_decl("example : (3 : Nat) = 3 := by let x : Nat := 2; exact (rfl : x = 3)");
    assert!(
        result.is_err(),
        "rfl : x = 3 must be rejected when x := 2 (no over-accept)"
    );
}

#[test]
fn test_let_tactic_value_type_mismatch_errors() {
    // NEGATIVE: the value `True.intro : True` does not have the annotated type
    // `Nat`. The kernel-checked let must ERROR (no panic, no over-accept).
    let result = check_decl("def t : Nat := by let x : Nat := True.intro; exact 5");
    assert!(
        result.is_err(),
        "let x : Nat := True.intro must error: value is not a Nat"
    );
}
