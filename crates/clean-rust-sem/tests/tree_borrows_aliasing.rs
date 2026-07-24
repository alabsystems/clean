// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::EvalResult;
use clean_rust_sem::ownership::AliasingModel;
use clean_rust_sem::{SourceProgram, Value};

fn run_source_with_model(source: &str, model: AliasingModel, parse_msg: &str) -> EvalResult {
    let program = SourceProgram::parse(source).expect(parse_msg);
    let mut interpreter = Interpreter::new().with_aliasing_model(model);
    program.run(&mut interpreter)
}

#[test]
fn tree_borrows_relaxes_shared_ref_raw_write_pattern() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &u32 = &x;
            let p: *mut u32 = r as *mut u32;
            unsafe { *p = 2u32; }
            unsafe { *p }
        }
    "#;

    let stacked = run_source_with_model(
        source,
        AliasingModel::StackedBorrows,
        "shared-ref raw write should parse",
    );
    assert!(
        matches!(stacked, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "stacked borrows should reject the shared-ref raw-write pattern, got {stacked:?}"
    );

    let tree = run_source_with_model(
        source,
        AliasingModel::TreeBorrows,
        "shared-ref raw write should parse",
    );
    assert_eq!(
        tree.value(),
        Some(Value::u32(2)),
        "tree borrows should allow the relaxed shared-ref/raw-pointer pattern"
    );
}

#[test]
fn tree_borrows_keeps_multiple_raw_children_live() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let p1: *mut u32 = r as *mut u32;
            let p2: *mut u32 = r as *mut u32;
            unsafe {
                *p1 = 7u32;
                *p2
            }
        }
    "#;

    let stacked = run_source_with_model(
        source,
        AliasingModel::StackedBorrows,
        "multiple raw pointers from &mut should parse",
    );
    assert!(
        matches!(stacked, EvalResult::Error(ref msg) if msg.contains("borrow error") || msg.contains("stacked borrows")),
        "stacked borrows should invalidate the earlier raw child, got {stacked:?}"
    );

    let tree = run_source_with_model(
        source,
        AliasingModel::TreeBorrows,
        "multiple raw pointers from &mut should parse",
    );
    // Tree Borrows keeps sibling raw pointers derived from the same mutable
    // parent mutually live: a write through `p1` must NOT invalidate `p2`, so
    // reading through `p2` afterwards observes the written value. This is the
    // relaxed-permissions rule for raw children of the same mut parent.
    assert_eq!(
        tree.value(),
        Some(Value::u32(7)),
        "tree borrows should keep sibling raw pointers live"
    );
}

/// Negative companion: Tree Borrows only relaxes sibling *raw* pointers. A
/// reborrowed shared reference (`&u32`) taken from the same parent after a raw
/// pointer is created must still be invalidated by a write through the raw
/// pointer — reading through the stale shared reference afterwards is rejected.
/// This proves the relaxation is keyed on the `SharedReadWrite` (raw) sibling
/// permission, not applied to every aliasing tag.
#[test]
fn tree_borrows_write_through_raw_still_invalidates_shared_ref_child() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let p: *mut u32 = &mut x as *mut u32;
            let r: &u32 = &x;
            unsafe { *p = 7u32; }
            *r
        }
    "#;

    let tree = run_source_with_model(
        source,
        AliasingModel::TreeBorrows,
        "raw-then-shared pattern should parse",
    );
    assert!(
        matches!(tree, EvalResult::Error(ref msg) if msg.contains("borrow") || msg.contains("stacked borrows")),
        "tree borrows must still reject reading a shared reference invalidated by a raw write, got {tree:?}"
    );
}

/// Negative companion: even under Tree Borrows, a write through the original
/// exclusive `&mut` (a `Unique` capability) asserts exclusivity and pops every
/// derived raw child. A raw pointer created beforehand must be invalidated, so
/// reading through it after the parent write is rejected. The sibling-raw
/// relaxation must not leak into writes performed through a `Unique` writer.
#[test]
fn tree_borrows_unique_parent_write_invalidates_raw_child() {
    let source = r#"
        fn main() -> u32 {
            let mut x: u32 = 1u32;
            let r: &mut u32 = &mut x;
            let p: *mut u32 = r as *mut u32;
            *r = 5u32;
            unsafe { *p }
        }
    "#;

    let tree = run_source_with_model(
        source,
        AliasingModel::TreeBorrows,
        "unique-parent-write pattern should parse",
    );
    assert!(
        matches!(tree, EvalResult::Error(ref msg) if msg.contains("borrow") || msg.contains("stacked borrows")),
        "tree borrows must still invalidate a raw child after an exclusive &mut write, got {tree:?}"
    );
}
