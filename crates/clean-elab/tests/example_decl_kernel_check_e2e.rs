// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock: **`example` declarations are kernel-checked.**
//!
//! ## The soundness gap this guards (Track CC discovery)
//!
//! Before the fix, the `SurfaceDecl::Example` elaboration arm elaborated the
//! type and proof term and then *discarded both* (`ElabResult::Skipped`),
//! WITHOUT running the kernel type-checker on the proof. Named `theorem`/`def`
//! declarations are sound because they flow through `add_decl`'s mandatory
//! kernel check; `example` skipped it entirely.
//!
//! The consequence was a silent FALSE GREEN: `clean check` reported `status:
//! pass` for `example` declarations whose `rfl`/`Eq.refl` proof did NOT actually
//! prove the stated proposition. For instance, all of these were accepted:
//!
//! ```text
//! example (n : Nat) : n = Nat.succ n := rfl                 -- blatantly false
//! example (b : Bool) : Bool.not b = b := rfl                -- false
//! example (b : Bool) : Bool.not (Bool.not b) = b := rfl     -- stuck Bool.rec
//! ```
//!
//! This directly undermined `clean check` as a trustworthy verifier: any
//! `example`-based "proof" was unverified. (Named declarations were unaffected
//! and remained sound.)
//!
//! ## The fix
//!
//! The `Example` arm now performs the same kernel check `add_decl` performs for
//! a Theorem — it `infer_type`s the proof term (fully kernel-checking it) and,
//! when an explicit type was given, requires the inferred type to be
//! definitionally equal to the stated type — while still discarding the result
//! (so `example` stays anonymous and namespace-neutral).
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches an observable `clean check` pass/fail on surface
//! syntax.

use clean_kernel::env::Environment;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline for a single-declaration source. Returns Ok if
/// every declaration elaborates and kernel-checks, Err(message) otherwise.
fn try_elaborate(source: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Negative controls: FALSE `example`s must now be REJECTED (no false green).
// ---------------------------------------------------------------------------

#[test]
fn example_false_nat_succ_is_rejected() {
    let err = try_elaborate("example (n : Nat) : n = Nat.succ n := rfl")
        .expect_err("example of a FALSE Nat equation must be rejected, not silently passed");
    assert!(
        err.to_lowercase().contains("example")
            || err.to_lowercase().contains("not definitionally equal")
            || err.contains("KernelCheckFailed")
            || err.to_lowercase().contains("type"),
        "rejection must come from the kernel check, got: {err}"
    );
}

#[test]
fn example_false_bool_not_self_is_rejected() {
    try_elaborate("example (b : Bool) : Bool.not b = b := rfl")
        .expect_err("example `Bool.not b = b` must be rejected");
}

#[test]
fn example_stuck_bool_rec_double_not_is_rejected() {
    try_elaborate("example (b : Bool) : Bool.not (Bool.not b) = b := rfl")
        .expect_err("example with stuck Bool.rec (`not (not b) = b`) must be rejected");
}

#[test]
fn example_stuck_nat_rec_is_rejected() {
    try_elaborate(
        "example (n : Nat) : Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.succ ih) n = n := rfl",
    )
    .expect_err("example with stuck Nat.rec identity must be rejected");
}

// ---------------------------------------------------------------------------
// Positive controls: TRUE `example`s must still be ACCEPTED (no false red).
// ---------------------------------------------------------------------------

#[test]
fn example_true_refl_is_accepted() {
    try_elaborate("example (n : Nat) : n = n := rfl")
        .expect("trivially true `example` must still pass");
}

#[test]
fn example_true_add_zero_is_accepted() {
    // Nat.add n 0 reduces to n via Nat.rec zero-case iota — a genuine rfl.
    try_elaborate("example (n : Nat) : Nat.add n 0 = n := rfl")
        .expect("`Nat.add n 0 = n` is a genuine rfl and must still pass");
}

#[test]
fn example_true_closed_literal_is_accepted() {
    try_elaborate("example : (2 : Nat) = 2 := rfl").expect("closed literal example must pass");
}

#[test]
fn example_true_bool_double_not_closed_is_accepted() {
    // Closed Bool.rec fully reduces, so this concrete `not (not true) = true` holds.
    try_elaborate("example : Bool.not (Bool.not true) = true := rfl")
        .expect("closed `not (not true) = true` must pass");
}
