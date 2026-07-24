// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end NLL aliasing tests through the full source→VIR→NLL pipeline.
//!
//! These tests cover aliasing patterns (mutable deref writes, reborrow chains,
//! raw pointer casts, whole-place overwrites) that were previously only
//! exercised through the interpreter's stacked-borrows suite.
//!
//! Part of #2726 (Expr→VIR lowering path) and #701 (Stacked Borrows aliasing model).

use clean_rust_sem::{NllError, SourceProgram};

fn nll_errors(source: &str) -> Vec<(String, Vec<NllError>)> {
    let program = SourceProgram::parse(source).expect("source should parse");
    let analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    analyses
        .into_iter()
        .filter(|(_, result)| !result.errors.is_empty())
        .map(|(name, result)| (name, result.errors))
        .collect()
}

fn assert_nll_clean(source: &str, context: &str) {
    let errors = nll_errors(source);
    assert!(
        errors.is_empty(),
        "{context}: expected NLL-clean but got errors: {errors:?}"
    );
}

fn assert_has_nll_error(source: &str, fn_name: &str, context: &str) -> Vec<NllError> {
    let program = SourceProgram::parse(source).expect("source should parse");
    let analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    let result = analyses
        .get(fn_name)
        .unwrap_or_else(|| panic!("{context}: function `{fn_name}` not in NLL results"));
    assert!(
        !result.errors.is_empty(),
        "{context}: expected NLL errors in `{fn_name}` but got none"
    );
    result.errors.clone()
}

// =========================================================================
// Mutable deref write patterns
// =========================================================================

/// Mutable deref write with no competing borrows: must be accepted.
/// Exercises Expr::Assign { target: Expr::Deref(_) } through VIR lowering.
#[test]
fn test_nll_accepts_mut_deref_write_no_competing_borrow() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            *r = 2u32;
            *r
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "mut-deref-write-no-conflict");
}

/// Mutable deref write then read-back through the original: must be accepted.
/// The mutable borrow dies before the read of `x`.
#[test]
fn test_nll_accepts_mut_deref_write_then_original_read() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            *r = 2u32;
            x
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "mut-deref-write-then-original-read");
}

/// Mutable deref write while a shared borrow is live: must be rejected.
/// `r` is still live when `rm` writes through deref.
#[test]
fn test_nll_detects_mut_deref_write_while_shared_borrow_live() {
    let source = r#"
        fn bad() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let rm: &mut u32 = &mut x;
            *rm = 2u32;
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "mut-deref-write-while-shared");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "should detect conflict from &mut borrow while shared borrow lives: {errors:?}"
    );
}

// =========================================================================
// Reborrow chain patterns
// =========================================================================

/// Simple reborrow: `let s = &mut *r` with no competing uses — accepted.
/// Exercises Expr::AddrOf { expr: Expr::Deref(_) } through VIR lowering.
#[test]
fn test_nll_accepts_reborrow_chain_no_parent_use() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &mut u32 = &mut *r;
            *s = 2u32;
            *s
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "reborrow-chain-no-parent-use");
}

/// Reborrow then use parent after child dies: rustc accepts this (NLL region
/// shrinks to last use of `s`). Drop-liveness in the NLL solver means the
/// scope-end `Drop` of the reference `s` (a no-op — `&mut T` has no drop
/// glue) does not extend `s`'s live range, so the child borrow is dead
/// before `*r = 3u32`, matching rustc (issue #699).
#[test]
fn test_nll_accepts_reborrow_then_parent_write_after_child_dead() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &mut u32 = &mut *r;
            let v: u32 = *s;
            *r = 3u32;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "reborrow-then-parent-write-after-child-dead");
}

/// Shared reborrow: `let s = &*r` from `&mut r` — accepted alongside parent.
/// A shared reborrow from a mutable reference doesn't conflict with parent.
#[test]
fn test_nll_accepts_shared_reborrow_from_mut_ref() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &u32 = &*r;
            *s
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "shared-reborrow-from-mut-ref");
}

/// Parent mutable write while child reborrow is live: must be rejected.
/// `*r = 3u32` assigns through `r` while `s` (borrowing `*r`) is live.
#[test]
fn test_nll_detects_parent_write_while_reborrow_live() {
    let source = r#"
        fn bad() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let s: &mut u32 = &mut *r;
            *r = 3u32;
            *s
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "parent-write-while-reborrow-live");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            NllError::AssignWhileBorrowed { .. } | NllError::ConflictingBorrow { .. }
        )),
        "should detect conflict from parent write while child reborrow is active: {errors:?}"
    );
}

// =========================================================================
// Whole-place overwrite patterns
// =========================================================================

/// Whole-place struct overwrite while a field borrow is live: must be rejected.
/// `s = Pair { ... }` overwrites the entire struct while `r` borrows `s.x`.
#[test]
fn test_nll_detects_whole_place_overwrite_of_borrowed_field() {
    let source = r#"
        struct Pair { x: u32, y: u32 }

        fn bad() -> u32 {
            let mut s: Pair = Pair { x: 1u32, y: 2u32 };
            let r: &mut u32 = &mut s.x;
            s = Pair { x: 3u32, y: 4u32 };
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "whole-place-overwrite-borrowed-field");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::AssignWhileBorrowed { .. })),
        "should detect assign-while-borrowed from whole-place overwrite: {errors:?}"
    );
}

/// Whole-place overwrite after field borrow dies: rustc accepts this (borrow
/// region of `r` ends at `let v = *r`). With drop-liveness, the scope-end
/// `Drop` of the reference `r` (no drop glue) no longer extends the field
/// borrow through the whole-place overwrite, matching rustc.
#[test]
fn test_nll_accepts_whole_place_overwrite_after_field_borrow_dead() {
    let source = r#"
        struct Pair { x: u32, y: u32 }

        fn ok() -> u32 {
            let mut s: Pair = Pair { x: 1u32, y: 2u32 };
            let r: &mut u32 = &mut s.x;
            let v: u32 = *r;
            s = Pair { x: 3u32, y: 4u32 };
            s.x + v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "whole-place-overwrite-after-field-borrow-dead");
}

// =========================================================================
// Raw pointer cast and deref patterns
// =========================================================================

/// Shared ref to raw pointer cast then deref: accepted.
/// Exercises Expr::Cast + Expr::RawDeref through VIR lowering.
#[test]
fn test_nll_accepts_raw_ptr_from_shared_ref_cast() {
    let source = r#"
        fn ok() -> u32 {
            let x: u32 = 55u32;
            let r: &u32 = &x;
            let p: *const u32 = r as *const u32;
            unsafe { *p }
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "raw-ptr-from-shared-ref");
}

/// Mutable ref to raw pointer cast, write through raw, read back: accepted.
/// The original `&mut` borrow is still live but there's no competing borrow.
#[test]
fn test_nll_accepts_raw_mut_ptr_write_and_readback() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let p: *mut u32 = r as *mut u32;
            unsafe { *p = 99u32; }
            unsafe { *p }
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "raw-mut-ptr-write-readback");
}

// =========================================================================
// Nested deref chain patterns
// =========================================================================

/// Nested deref through double reference: accepted.
/// Exercises Place::Deref(Deref(Local)) in VIR lowering.
#[test]
fn test_nll_accepts_double_deref_read() {
    let source = r#"
        fn ok() -> u32 {
            let x: u32 = 42u32;
            let r: &u32 = &x;
            let rr: &&u32 = &r;
            **rr
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "double-deref-read");
}

/// Borrow a field through a reference, then write to a disjoint field: accepted.
/// Exercises autoderef + field projection in the NLL conflict checker.
#[test]
fn test_nll_accepts_borrow_field_through_ref_then_write_disjoint() {
    let source = r#"
        struct Pair { a: u32, b: u32 }

        fn ok() -> u32 {
            let mut p: Pair = Pair { a: 1u32, b: 2u32 };
            let r: &Pair = &p;
            let va: u32 = r.a;
            p.b = 3u32;
            va
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "borrow-field-through-ref-disjoint-write");
}
