// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standing soundness falsification suite for the Rust verifier.
//!
//! Each of the five soundness holes closed in
//! `docs/SOUNDNESS_FINDINGS_CLEAN_RUST_SEM_2026-07.md` had an exact unsafe
//! reproduction that the verifier previously certified as borrow-safe /
//! verified. This module pins those programs as **must-NOT-verify** through the
//! public `SourceProgram::parse(..).build_proof_bundle()` / `check_borrows()`
//! entry points: each must now surface an `NllError`, or report
//! `all_satisfied() == false` / `aliasing.passed != true`.
//!
//! The complementary correct-path guards pin that legitimately borrow-safe
//! programs are NOT rejected — the fixes catch real violations without
//! introducing false positives on safe code.

use crate::nll::NllError;
use crate::source::SourceProgram;

fn parse(src: &str) -> SourceProgram {
    SourceProgram::parse(src).expect("falsification source should parse")
}

/// Collect all NLL errors across every function in a program.
fn nll_errors(src: &str) -> Vec<NllError> {
    let results = parse(src)
        .check_borrows()
        .expect("falsification source should lower");
    results
        .into_values()
        .flat_map(|r| r.errors.into_iter())
        .collect()
}

/// True if the program is reported "verified": no NLL errors AND the proof
/// bundle's obligations are all satisfied AND the aliasing channel affirmatively
/// passed. A falsification program must make this `false`.
fn is_reported_verified(src: &str) -> bool {
    let program = parse(src);
    let no_borrow_errors = program
        .check_borrows()
        .expect("lowering should succeed")
        .values()
        .all(|r| r.errors.is_empty());
    let bundle = program
        .build_proof_bundle()
        .expect("bundle build should succeed");
    no_borrow_errors && bundle.stats.all_satisfied() && bundle.aliasing_observation.passed
}

// ---------------------------------------------------------------------------
// Hole 2 — read (`Operand::Copy`) of a `&mut`-borrowed place (rustc E0503).
// ---------------------------------------------------------------------------

#[test]
fn hole2_copy_read_of_mut_borrowed_place_is_not_verified() {
    // `let r = &mut x; let y = x; *r = 5;` — reading `x` while `&mut x` is live
    // is use-while-borrowed (stacked-borrows UB).
    let src =
        "fn main() { let mut x: i32 = 1; let r: &mut i32 = &mut x; let _y: i32 = x; *r = 5; }";
    assert!(
        nll_errors(src)
            .iter()
            .any(|e| matches!(e, NllError::UseWhileBorrowed { .. })),
        "reading a &mut-borrowed place must emit UseWhileBorrowed"
    );
    assert!(!is_reported_verified(src), "hole 2 program must not verify");
}

#[test]
fn hole2_read_under_shared_borrow_is_allowed() {
    // Correct-path guard: a shared read while only a `&` borrow is active is
    // fine and must NOT be flagged.
    let src = "fn main() { let x: i32 = 42; let r: &i32 = &x; let _y: i32 = x; let _z: i32 = *r; }";
    assert!(
        nll_errors(src).is_empty(),
        "shared read under a shared borrow must remain borrow-safe: {:?}",
        nll_errors(src)
    );
}

// ---------------------------------------------------------------------------
// Hole 3 — non-`Local` (field-projection) reference destination.
// ---------------------------------------------------------------------------

#[test]
fn hole3_field_lhs_borrow_is_tracked_and_conflicts() {
    // `h.r = &mut x` stores a `&mut x` behind a struct field (a `Place::Field`
    // destination). The loan must be tracked so the later read of `x` conflicts.
    let src = "struct Holder<'a> { r: &'a mut i32 } \
               fn main() { \
                   let mut y: i32 = 0; \
                   let mut x: i32 = 1; \
                   let mut h = Holder { r: &mut y }; \
                   h.r = &mut x; \
                   let _z: i32 = x; \
               }";
    assert!(
        !nll_errors(src).is_empty(),
        "field-LHS `&mut` borrow must be tracked and produce a conflict"
    );
    assert!(!is_reported_verified(src), "hole 3 program must not verify");
}

// ---------------------------------------------------------------------------
// Hole 4 — no-body / no-`main` program yields a vacuous aliasing "pass".
// ---------------------------------------------------------------------------

#[test]
fn hole4_no_main_program_is_not_an_affirmative_aliasing_pass() {
    // A library-style program (no `main`) executes nothing; the runtime aliasing
    // channel must be non-committal, NOT an affirmative pass.
    let src = "fn helper(p: *mut i32, q: &mut i32) { unsafe { *p = 10; } *q = 20; }";
    let bundle = parse(src)
        .build_proof_bundle()
        .expect("bundle build should succeed");
    assert!(
        !bundle.aliasing_observation.passed,
        "no-main program must not report aliasing.passed = true"
    );
    assert!(
        !bundle.aliasing_observation.ran,
        "no-main program's aliasing channel must be marked as did-not-run"
    );
    assert!(
        !bundle.stats.all_satisfied(),
        "no-main program must not report all_satisfied = true (fail-closed)"
    );
}

// ---------------------------------------------------------------------------
// Hole 5 — escaping / dangling return reference (rustc E0515).
// ---------------------------------------------------------------------------

#[test]
fn hole5_dangling_return_reference_is_not_verified() {
    let src = "fn dangle() -> &u32 { let x: u32 = 5; &x }";
    assert!(
        nll_errors(src)
            .iter()
            .any(|e| matches!(e, NllError::BorrowEscapesReferent { .. })),
        "returning a reference to a local must emit BorrowEscapesReferent"
    );
    assert!(!is_reported_verified(src), "hole 5 program must not verify");
}

#[test]
fn hole5_returning_reference_to_argument_is_allowed() {
    // Correct-path guard: returning a reference derived from an argument
    // reference (which outlives the call) is legitimate and must NOT be flagged.
    for src in [
        "fn id<'a>(x: &'a u32) -> &'a u32 { x }",
        "fn thru<'a>(x: &'a u32) -> &'a u32 { &*x }",
        // Copy of an argument reference through a local, then returned: the
        // returned reference points behind the (arg) pointer, not into the
        // local's own frame. Must NOT be flagged (a `Deref` referent).
        "fn f(x: &u32) -> &u32 { let y = x; y }",
        "fn reborrow<'a>(x: &'a mut u32) -> &'a mut u32 { &mut *x }",
    ] {
        assert!(
            !nll_errors(src)
                .iter()
                .any(|e| matches!(e, NllError::BorrowEscapesReferent { .. })),
            "returning a borrow derived from an argument must remain borrow-safe: {src}"
        );
    }
}

// ---------------------------------------------------------------------------
// Hole 1 — arithmetic overflow / division carries no obligation (latent).
// ---------------------------------------------------------------------------

#[test]
fn hole1_overflowing_arithmetic_is_not_reported_satisfied() {
    // `let z: u8 = 200 + 100;` overflows; the arithmetic obligation is emitted
    // UNKNOWN so the bundle is not reported fully satisfied.
    let src = "fn main() { let x: u8 = 200; let y: u8 = 100; let _z: u8 = x + y; }";
    let bundle = parse(src)
        .build_proof_bundle()
        .expect("bundle build should succeed");
    assert!(
        bundle.stats.arithmetic_safety > 0,
        "an arithmetic op must emit an arithmetic-safety obligation"
    );
    assert!(
        !bundle.stats.all_satisfied(),
        "unchecked overflow must not report all_satisfied = true"
    );
}

// ---------------------------------------------------------------------------
// Correct-path integration: safe programs with a `main` still verify.
// ---------------------------------------------------------------------------

#[test]
fn safe_sequential_mut_borrows_still_verify() {
    // Non-overlapping sequential `&mut` borrows are safe and must verify.
    let src = "fn main() { \
                   let mut x: i32 = 1; \
                   { let r1: &mut i32 = &mut x; *r1 = 2; } \
                   { let r2: &mut i32 = &mut x; *r2 = 3; } \
               }";
    assert!(
        nll_errors(src).is_empty(),
        "sequential non-overlapping borrows must be borrow-safe: {:?}",
        nll_errors(src)
    );
    let bundle = parse(src)
        .build_proof_bundle()
        .expect("bundle build should succeed");
    assert!(
        bundle.stats.all_satisfied(),
        "a safe program (with main, no arithmetic) must report all_satisfied"
    );
    assert!(
        bundle.aliasing_observation.passed && bundle.aliasing_observation.ran,
        "a safe program with main must report an affirmative aliasing pass"
    );
}

#[test]
fn safe_shared_read_under_shared_borrow_still_verifies() {
    let src =
        "fn main() { let x: i32 = 1; let _r1: &i32 = &x; let _r2: &i32 = &x; let _y: i32 = x; }";
    assert!(
        nll_errors(src).is_empty(),
        "multiple shared borrows + a shared read must be borrow-safe: {:?}",
        nll_errors(src)
    );
    let bundle = parse(src)
        .build_proof_bundle()
        .expect("bundle build should succeed");
    assert!(
        bundle.stats.all_satisfied(),
        "a safe shared-borrow program must report all_satisfied"
    );
}
