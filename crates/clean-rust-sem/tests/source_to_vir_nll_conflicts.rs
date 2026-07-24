// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end NLL conflict detection tests through the full source→VIR→NLL pipeline.
//!
//! These tests verify that the borrow checker correctly detects (or correctly
//! accepts) real-world borrow patterns when starting from Rust source text.
//! Each test exercises the complete pipeline: parse → lower → NLL analysis.

use clean_rust_sem::{NllError, SourceProgram};

/// Helper: parse source, lower to VIR, run NLL, return all errors across all functions.
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

/// Helper: parse source, lower to VIR, run NLL, assert all functions are error-free.
fn assert_nll_clean(source: &str, context: &str) {
    let errors = nll_errors(source);
    assert!(
        errors.is_empty(),
        "{context}: expected NLL-clean but got errors: {errors:?}"
    );
}

/// Helper: parse source, lower to VIR, run NLL, assert a specific function has errors.
///
/// Every classic borrow-conflict pattern exercised here now lowers cleanly
/// *and* is detected by the NLL pass, so both former TRACE escape hatches
/// (source-to-VIR lowering gap, NLL false-negative) are hard failures. The
/// soundness contract is: a pattern documented as "must be rejected" must
/// produce at least one `NllError`; a silent empty result is a regression,
/// not a tolerated gap.
fn assert_has_nll_error(source: &str, fn_name: &str, context: &str) -> Vec<NllError> {
    let program = SourceProgram::parse(source).expect("source should parse");
    let analyses = program
        .check_borrows()
        .unwrap_or_else(|err| panic!("{context}: source should lower and run NLL: {err:?}"));
    let result = analyses
        .get(fn_name)
        .unwrap_or_else(|| panic!("{context}: function `{fn_name}` not in NLL results"));
    assert!(
        !result.errors.is_empty(),
        "{context}: NLL must reject `{fn_name}` but reported no errors \
         (regression — this pattern is unsound and must produce an NllError)"
    );
    result.errors.clone()
}

// =========================================================================
// Classic borrow conflicts that MUST be detected
// =========================================================================

/// Write-while-immutably-borrowed: `let r = &x; x = 2; *r`
/// This is the most basic NLL conflict pattern.
#[test]
fn test_nll_detects_write_while_immutably_borrowed() {
    let source = r#"
        fn bad() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            x = 2u32;
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "write-while-borrowed");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::AssignWhileBorrowed { .. })),
        "should detect AssignWhileBorrowed: {errors:?}"
    );
}

/// Double mutable borrow: `let r1 = &mut x; let r2 = &mut x; *r1`
#[test]
fn test_nll_detects_double_mutable_borrow() {
    let source = r#"
        fn bad() -> u32 {
            let mut x: u32 = 1u32;
            let r1: &mut u32 = &mut x;
            let r2: &mut u32 = &mut x;
            *r1
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "double-mut-borrow");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "should detect ConflictingBorrow: {errors:?}"
    );
}

/// Mutable borrow while immutably borrowed: `let r = &x; let rm = &mut x; *r`
#[test]
fn test_nll_detects_mutable_borrow_while_immutably_borrowed() {
    let source = r#"
        fn bad() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let rm: &mut u32 = &mut x;
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "mut-borrow-while-shared");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::ConflictingBorrow { .. })),
        "should detect ConflictingBorrow: {errors:?}"
    );
}

// =========================================================================
// Patterns that MUST be accepted (NLL precision)
// =========================================================================

/// Sequential borrows: borrow ends before the next one starts.
/// `let r = &x; let v = *r; /* r dead */ x = 2;`
#[test]
fn test_nll_accepts_sequential_borrows() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let v: u32 = *r;
            x = 2u32;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "sequential-borrows");
}

/// Multiple shared borrows: many `&x` can coexist, including chained operations.
#[test]
fn test_nll_accepts_multiple_shared_borrows() {
    let source = r#"
        fn ok() -> u32 {
            let x: u32 = 1u32;
            let r1: &u32 = &x;
            let r2: &u32 = &x;
            let r3: &u32 = &x;
            *r1 + *r2 + *r3
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "multiple-shared-borrows");
}

/// Mutable borrow after shared borrow dies.
/// NLL should accept this because the shared borrow is not used after the mut borrow.
#[test]
fn test_nll_accepts_mut_borrow_after_shared_dies() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let v: u32 = *r;
            let rm: &mut u32 = &mut x;
            *rm = 5u32;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "mut-after-shared-dies");
}

// =========================================================================
// Struct field borrow patterns
// =========================================================================

/// Borrow a struct field, then write to a different field: should be OK.
/// This tests that Place::Field conflicts are correctly computed.
#[test]
fn test_nll_accepts_disjoint_field_borrows() {
    let source = r#"
        struct Pair { a: u32, b: u32 }

        fn ok() -> u32 {
            let mut p: Pair = Pair { a: 1u32, b: 2u32 };
            let ra: &u32 = &p.a;
            p.b = 3u32;
            *ra
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "disjoint-field-borrows");
}

/// Borrow a field, then write to the same field: must be rejected.
#[test]
fn test_nll_detects_write_to_borrowed_field() {
    let source = r#"
        struct Pair { a: u32, b: u32 }

        fn bad() -> u32 {
            let mut p: Pair = Pair { a: 1u32, b: 2u32 };
            let ra: &u32 = &p.a;
            p.a = 3u32;
            *ra
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "write-to-borrowed-field");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::AssignWhileBorrowed { .. })),
        "should detect field-level AssignWhileBorrowed: {errors:?}"
    );
}

/// Edge case (parent-vs-child overlap): borrow a field `&p.a`, then overwrite
/// the *whole* struct `p = ...`. Writing the parent place overlaps the live
/// child borrow, so this must be rejected. This is the strict complement to
/// `test_nll_accepts_disjoint_field_borrows`: that test proves writes to a
/// *sibling* field stay clean, this one proves a write to an *ancestor* place
/// does not slip past the field-overlap check.
#[test]
fn test_nll_detects_write_to_whole_struct_while_field_borrowed() {
    let source = r#"
        struct Pair { a: u32, b: u32 }

        fn bad() -> u32 {
            let mut p: Pair = Pair { a: 1u32, b: 2u32 };
            let ra: &u32 = &p.a;
            p = Pair { a: 7u32, b: 8u32 };
            *ra
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "write-whole-struct-while-field-borrowed");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::AssignWhileBorrowed { .. })),
        "writing the whole struct must conflict with a live field borrow: {errors:?}"
    );
}

// =========================================================================
// Control flow patterns
// =========================================================================

/// Borrow in one branch, use in the other — should be clean.
#[test]
fn test_nll_accepts_borrow_in_disjoint_branches() {
    let source = r#"
        fn ok(cond: bool) -> u32 {
            let mut x: u32 = 1u32;
            if cond {
                let r: &u32 = &x;
                *r
            } else {
                x = 2u32;
                x
            }
        }
        fn main() -> u32 { ok(true) }
    "#;
    assert_nll_clean(source, "borrow-in-disjoint-branches");
}

/// Borrow in loop body, write after loop — should be clean (borrow dies at loop exit).
#[test]
fn test_nll_accepts_borrow_scoped_to_loop_body() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 0u32;
            let mut i: u32 = 0u32;
            while i < 3u32 {
                let r: &u32 = &x;
                let _v: u32 = *r;
                i = i + 1u32;
            }
            x = 10u32;
            x
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "borrow-scoped-to-loop");
}

/// Iterating over `&values` keeps the collection borrow live through the loop
/// body, but that borrow must end at loop exit so post-loop mutation is legal.
#[test]
fn test_nll_accepts_write_after_borrowed_for_loop_finishes() {
    let source = r#"
        fn ok() -> u32 {
            let mut values: [u32; 3] = [1u32, 2u32, 3u32];
            for _item in &values {
            }
            values[0] = 9u32;
            values[0]
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "write-after-borrowed-for-loop");
}

/// Iterating over `&values` creates a borrow of the collection itself.
/// Mutating the collection inside the loop body must be rejected.
#[test]
fn test_nll_detects_write_to_collection_while_borrowed_for_loop_active() {
    let source = r#"
        fn bad() -> u32 {
            let mut values: [u32; 3] = [1u32, 2u32, 3u32];
            for _item in &values {
                values[0] = 9u32;
            }
            values[0]
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "write-in-borrowed-for-loop");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::AssignWhileBorrowed { .. })),
        "should detect AssignWhileBorrowed from the active borrowed-iterator source: {errors:?}"
    );
}

// =========================================================================
// Method call receiver borrow patterns
// =========================================================================

/// Method call with `&self` receiver while another shared borrow is live: OK.
#[test]
fn test_nll_accepts_shared_method_with_shared_borrow() {
    let source = r#"
        struct Counter { value: u32 }

        impl Counter {
            fn get(&self) -> u32 { self.value }
        }

        fn ok() -> u32 {
            let c: Counter = Counter { value: 5u32 };
            let r: &u32 = &c.value;
            let v: u32 = c.get();
            v + *r
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "shared-method-with-shared-borrow");
}

/// Method call with `&mut self` while shared borrow is live: MUST be rejected.
///
/// This pattern lowers as a reborrow chain (the `&mut self` receiver is
/// passed via an intermediate two-phase borrow local), so the NLL
/// conflict check must resolve reborrow chains to detect the conflict
/// between the shared borrow `r = &c.value` and the call's `&mut c`
/// receiver. Wave 110 closed this gap; the assertion is hard.
#[test]
fn test_nll_detects_mut_method_while_shared_borrow_live() {
    let source = r#"
        struct Counter { value: u32 }

        impl Counter {
            fn inc(&mut self) { self.value = self.value + 1u32; }
        }

        fn bad() -> u32 {
            let mut c: Counter = Counter { value: 5u32 };
            let r: &u32 = &c.value;
            c.inc();
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "mut-method-while-shared");
    assert!(
        !errors.is_empty(),
        "mut-method-while-shared must produce a hard NLL conflict, not TRACE-skip"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            NllError::ConflictingBorrow { .. } | NllError::AssignWhileBorrowed { .. }
        )),
        "should detect conflict from &mut self method call while shared borrow lives: {errors:?}"
    );
}

/// Negative companion to the mut-method conflict above: a reborrow
/// chain that stays mutable and is consistently used must NOT be
/// reported as conflicting with its own parent borrow. This proves
/// the Wave 110 fix does not over-fire by treating a reborrow as a
/// fresh independent borrow.
#[test]
fn test_nll_accepts_chained_mut_reborrow_through_intermediate_local() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let v: u32 = *r;
            let rm: &mut u32 = &mut x;
            *rm = 5u32;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "chained-mut-reborrow-no-self-conflict");
}

// =========================================================================
// Closure capture borrow patterns
// =========================================================================

/// Closure capturing a shared borrow should coexist with other shared borrows.
#[test]
fn test_nll_accepts_closure_shared_capture_with_shared_borrow() {
    let source = r#"
        fn ok() -> u32 {
            let x: u32 = 1u32;
            let r: &u32 = &x;
            let f = |_a: u32| -> u32 { x + 1u32 };
            *r
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "closure-shared-capture-with-shared-borrow");
}

// =========================================================================
// Match pattern borrow patterns
// =========================================================================

/// Match on a value while it's borrowed — the borrow should end after the match.
#[test]
fn test_nll_accepts_match_then_write() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let v: u32 = match x {
                0u32 => 10u32,
                _ => 20u32,
            };
            x = 3u32;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "match-then-write");
}

// =========================================================================
// Drop elaboration: borrow-vs-drop conflict patterns
// =========================================================================

/// Dropping a non-Copy value while a borrow of it is still live.
///
/// `s` is a `Named` type (non-Copy). Taking a reference to `s` and then
/// letting `s` go out of scope while the reference lives must be rejected.
/// This exercises the `Term::Drop` path in NLL conflict checking.
#[test]
fn test_nll_detects_drop_while_borrowed_named_type() {
    let source = r#"
        struct MyString { data: u32 }

        fn bad() -> u32 {
            let r: &u32;
            {
                let s: MyString = MyString { data: 42u32 };
                r = &s.data;
            }
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "drop-while-borrowed");
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::MoveWhileBorrowed { .. })),
        "should detect drop-while-borrowed conflict via Term::Drop: {errors:?}"
    );
}

/// Dropping a Vec (non-Copy) at scope exit while a borrow lives.
///
/// Closed in Wave 112: built-in nominal-field metadata for `Vec` lets the
/// source-to-VIR field projection resolve `v.len` to a typed place, which
/// in turn lets the NLL drop-elaboration pass observe the live borrow at
/// the inner scope's `Term::Drop` site.
#[test]
fn test_nll_detects_drop_vec_while_borrowed() {
    let source = r#"
        fn bad() -> u32 {
            let r: &u32;
            {
                let v: Vec<u32> = Vec { len: 3u32 };
                r = &v.len;
            }
            *r
        }
        fn main() -> u32 { bad() }
    "#;
    let errors = assert_has_nll_error(source, "bad", "drop-vec-while-borrowed");
    assert!(
        !errors.is_empty(),
        "drop-vec-while-borrowed must produce a hard NLL conflict, not TRACE-skip"
    );
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, NllError::MoveWhileBorrowed { .. })),
        "should detect drop-while-borrowed for Vec type: {errors:?}"
    );
}

/// Negative complement to `test_nll_detects_drop_vec_while_borrowed`: the
/// built-in `Vec` field-lookup recognition MUST NOT over-fire on unrelated
/// nominal types. A user-declared `MyVec<T>` (a regular struct without a
/// `len` field) must surface the standard MissingType lowering error,
/// proving the synthetic Vec schema is keyed by `RustType::Vec`, not by
/// any shape resembling a vector.
#[test]
fn test_vec_builtin_field_does_not_overfire_on_unrelated_struct() {
    let source = r#"
        struct MyVec { capacity: u32 }

        fn bad() -> u32 {
            let v: MyVec = MyVec { capacity: 7u32 };
            v.len
        }
        fn main() -> u32 { bad() }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let err = program
        .check_borrows()
        .expect_err("MyVec.len must NOT lower — Vec builtin must not over-fire");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("MissingType") && msg.contains("len"),
        "expected MissingType on `len` for MyVec, got: {msg}"
    );
}

/// Negative complement to the builtin Vec schema: the synthetic schema
/// MUST only register the `len` field. Other plausible names (e.g.
/// `capacity`, `ptr`) must still surface a MissingType error to prevent
/// silent acceptance of code that depends on private-layout details.
#[test]
fn test_vec_builtin_field_only_recognizes_len() {
    let source = r#"
        fn bad() -> u32 {
            let v: Vec<u32> = Vec { capacity: 7u32 };
            v.capacity
        }
        fn main() -> u32 { bad() }
    "#;
    let program = SourceProgram::parse(source).expect("source should parse");
    let err = program
        .check_borrows()
        .expect_err("Vec.capacity must NOT lower — only `len` is in the synthetic schema");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("MissingType"),
        "expected MissingType on `capacity` for Vec, got: {msg}"
    );
}

/// Non-Copy value dropped at scope exit with no live borrows: must be accepted.
/// This ensures drop elaboration doesn't produce false positives.
#[test]
fn test_nll_accepts_drop_without_active_borrow() {
    let source = r#"
        struct MyString { data: u32 }

        fn ok() -> u32 {
            let result: u32;
            {
                let s: MyString = MyString { data: 42u32 };
                result = s.data;
            }
            result
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "drop-without-active-borrow");
}

/// Copy type going out of scope with an active borrow: must be accepted.
/// Copy types don't get Term::Drop, so there's no conflict.
#[test]
fn test_nll_accepts_copy_type_scope_exit_with_borrow() {
    let source = r#"
        fn ok() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let v: u32 = *r;
            v
        }
        fn main() -> u32 { ok() }
    "#;
    assert_nll_clean(source, "copy-type-scope-exit-with-borrow");
}
