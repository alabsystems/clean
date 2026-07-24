// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_ensure_base_is_stable() {
    let mut state = StackedBorrows::new();
    let first = state.ensure_base("alloc0");
    let second = state.ensure_base("alloc0");
    assert_eq!(first, second);
    assert_eq!(state.stack(&"alloc0").expect("missing stack").len(), 1);
}

#[test]
fn test_shared_read_only_tag_cannot_write() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let shared = state
        .retag(&"alloc0", root, BorrowPermission::SharedReadOnly, None)
        .expect("retag should succeed");
    state
        .access(&"alloc0", shared, AccessKind::Read)
        .expect("shared tag should read");
    let result = state.access(&"alloc0", shared, AccessKind::Write);
    assert!(matches!(
        result,
        Err(StackedBorrowsError::IncompatibleAccess {
            tag, access: AccessKind::Write, ..
        }) if tag == shared
    ));
}

#[test]
fn test_write_pops_incompatible_tags_above_writer() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let shared = state
        .retag(&"alloc0", root, BorrowPermission::SharedReadOnly, None)
        .expect("shared retag should succeed");
    let raw = state
        .retag(&"alloc0", shared, BorrowPermission::SharedReadWrite, None)
        .expect("raw retag should succeed");
    state
        .access(&"alloc0", root, AccessKind::Write)
        .expect("root write should pop conflicting tags");
    let live = state.stack(&"alloc0").expect("missing stack");
    assert_eq!(live.len(), 1);
    assert_eq!(live[0].tag, root);
    assert!(!state.contains_tag(&"alloc0", shared));
    assert!(!state.contains_tag(&"alloc0", raw));
}

#[test]
fn test_protector_blocks_invalidating_write() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let protector = state.new_protector();
    let shared = state
        .retag(
            &"alloc0",
            root,
            BorrowPermission::SharedReadOnly,
            Some(protector),
        )
        .expect("protected retag should succeed");
    let result = state.access(&"alloc0", root, AccessKind::Write);
    assert!(matches!(
        result,
        Err(StackedBorrowsError::ProtectedConflict {
            blocked_by, access: AccessKind::Write, ..
        }) if blocked_by == shared
    ));
}

#[test]
fn test_releasing_protector_unblocks_write() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let protector = state.new_protector();
    state
        .retag(
            &"alloc0",
            root,
            BorrowPermission::SharedReadOnly,
            Some(protector),
        )
        .expect("protected retag should succeed");
    state.release_protector(protector);
    state
        .access(&"alloc0", root, AccessKind::Write)
        .expect("releasing the protector should unblock the write");
}

#[test]
fn test_unique_retag_pops_entries_above_parent() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let shared = state
        .retag(&"alloc0", root, BorrowPermission::SharedReadOnly, None)
        .expect("shared retag should succeed");
    let unique = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag from root should succeed");
    assert!(!state.contains_tag(&"alloc0", shared));
    assert!(state.contains_tag(&"alloc0", unique));
    let live = state.stack(&"alloc0").expect("missing stack");
    assert_eq!(live.len(), 2);
}

#[test]
fn test_unique_retag_blocked_by_protected_entry() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let protector = state.new_protector();
    let protected = state
        .retag(
            &"alloc0",
            root,
            BorrowPermission::SharedReadOnly,
            Some(protector),
        )
        .expect("protected retag should succeed");
    let result = state.retag(&"alloc0", root, BorrowPermission::Unique, None);
    assert!(matches!(
        result,
        Err(StackedBorrowsError::ProtectedConflict { blocked_by, .. })
            if blocked_by == protected
    ));
}

#[test]
fn test_read_through_lower_tag_disables_unique_above() {
    // A read through a lower tag transitions Unique entries above
    // it to Disabled rather than popping them outright.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let unique = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag should succeed");
    // Stack: [root(Unique), unique(Unique)]

    // Read through root — unique is above and Unique, so it should be disabled.
    state
        .access(&"alloc0", root, AccessKind::Read)
        .expect("read through root should succeed");

    // The entry for unique should still exist but be Disabled.
    assert!(
        state.contains_tag(&"alloc0", unique),
        "disabled tag should persist on the stack"
    );
    let stack = state.stack(&"alloc0").expect("missing stack");
    let unique_entry = stack.iter().find(|e| e.tag == unique).expect("tag present");
    assert_eq!(
        unique_entry.permission,
        BorrowPermission::Disabled,
        "read should have transitioned Unique to Disabled"
    );
}

#[test]
fn test_disabled_tag_cannot_read() {
    // Once a tag is Disabled, both reads and writes through it fail.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let unique = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag should succeed");

    // Disable the unique tag via a read through root.
    state
        .access(&"alloc0", root, AccessKind::Read)
        .expect("read through root should succeed");

    // Read through the now-Disabled tag should fail.
    let result = state.access(&"alloc0", unique, AccessKind::Read);
    assert!(
        matches!(result, Err(StackedBorrowsError::IncompatibleAccess { tag, access: AccessKind::Read, .. }) if tag == unique),
        "read through Disabled tag should fail, got {result:?}"
    );
}

#[test]
fn test_disabled_tag_cannot_write() {
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let unique = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag should succeed");

    // Disable via read through root.
    state
        .access(&"alloc0", root, AccessKind::Read)
        .expect("read through root should succeed");

    let result = state.access(&"alloc0", unique, AccessKind::Write);
    assert!(
        matches!(result, Err(StackedBorrowsError::IncompatibleAccess { tag, access: AccessKind::Write, .. }) if tag == unique),
        "write through Disabled tag should fail, got {result:?}"
    );
}

#[test]
fn test_tree_borrows_write_through_raw_keeps_sibling_raw_live() {
    // Two raw children of one mutable parent are siblings. Under Tree Borrows
    // a write through the lower raw pointer must keep the upper raw sibling
    // live, so it can still be accessed afterwards.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let parent = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("mut parent retag should succeed");
    let raw1 = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("first raw retag should succeed");
    let raw2 = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("second raw retag should succeed");
    // Stack: [root(U), parent(U), raw1(SRW), raw2(SRW)]

    state
        .access_with_model(
            &"alloc0",
            raw1,
            AccessKind::Write,
            AliasingDiscipline::TreeBorrows,
        )
        .expect("write through raw1 should succeed");

    assert!(
        state.contains_tag(&"alloc0", raw2),
        "tree borrows must keep the sibling raw pointer live across the write"
    );
    state
        .access_with_model(
            &"alloc0",
            raw2,
            AccessKind::Read,
            AliasingDiscipline::TreeBorrows,
        )
        .expect("read through the still-live sibling raw pointer should succeed");
}

#[test]
fn test_stacked_borrows_write_through_raw_pops_sibling_raw() {
    // Same shape as the Tree Borrows case, but under Stacked Borrows the write
    // through the lower raw pointer pops the sibling raw above it.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let parent = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("mut parent retag should succeed");
    let raw1 = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("first raw retag should succeed");
    let raw2 = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("second raw retag should succeed");

    state
        .access_with_model(
            &"alloc0",
            raw1,
            AccessKind::Write,
            AliasingDiscipline::StackedBorrows,
        )
        .expect("write through raw1 should succeed");

    assert!(
        !state.contains_tag(&"alloc0", raw2),
        "stacked borrows must pop the sibling raw pointer on a write through raw1"
    );
}

#[test]
fn test_tree_borrows_write_through_raw_still_pops_shared_ref_sibling() {
    // The Tree Borrows relaxation is narrow: a write through a raw pointer
    // must still invalidate a sibling SharedReadOnly reference above it.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let parent = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("mut parent retag should succeed");
    let raw = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("raw retag should succeed");
    let shared = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadOnly, None)
        .expect("shared retag should succeed");
    // Stack: [root(U), parent(U), raw(SRW), shared(SRO)]

    state
        .access_with_model(
            &"alloc0",
            raw,
            AccessKind::Write,
            AliasingDiscipline::TreeBorrows,
        )
        .expect("write through raw should succeed");

    assert!(
        !state.contains_tag(&"alloc0", shared),
        "tree borrows must still pop a sibling shared reference on a raw write"
    );
}

#[test]
fn test_tree_borrows_unique_writer_still_pops_raw_sibling() {
    // The relaxation only applies when the writer is itself a raw pointer. A
    // write through the exclusive Unique parent must still pop raw children,
    // even under Tree Borrows.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let parent = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("mut parent retag should succeed");
    let raw = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("raw retag should succeed");

    state
        .access_with_model(
            &"alloc0",
            parent,
            AccessKind::Write,
            AliasingDiscipline::TreeBorrows,
        )
        .expect("write through the unique parent should succeed");

    assert!(
        !state.contains_tag(&"alloc0", raw),
        "a unique write must pop raw children even under tree borrows"
    );
}

#[test]
fn test_tree_borrows_write_through_raw_respects_protected_shared_ref() {
    // Protected entries still block invalidation under Tree Borrows: a write
    // through a raw pointer that would invalidate a protected shared sibling
    // must be rejected, not silently relaxed.
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let parent = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("mut parent retag should succeed");
    let raw = state
        .retag(&"alloc0", parent, BorrowPermission::SharedReadWrite, None)
        .expect("raw retag should succeed");
    let protector = state.new_protector();
    let protected = state
        .retag(
            &"alloc0",
            parent,
            BorrowPermission::SharedReadOnly,
            Some(protector),
        )
        .expect("protected shared retag should succeed");

    let result = state.access_with_model(
        &"alloc0",
        raw,
        AccessKind::Write,
        AliasingDiscipline::TreeBorrows,
    );
    assert!(
        matches!(
            result,
            Err(StackedBorrowsError::ProtectedConflict { blocked_by, .. }) if blocked_by == protected
        ),
        "raw write must be blocked by a protected shared sibling, got {result:?}"
    );
}

#[test]
fn test_write_through_lower_tag_pops_disabled_entries() {
    // A write through a lower tag should pop Disabled entries above
    // (they don't conflict with writes, but this verifies cleanup).
    let mut state = StackedBorrows::new();
    let root = state.ensure_base("alloc0");
    let unique = state
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag should succeed");

    // Disable via read.
    state
        .access(&"alloc0", root, AccessKind::Read)
        .expect("read should succeed");
    assert_eq!(
        state.stack(&"alloc0").unwrap().len(),
        2,
        "disabled entry should still be on stack"
    );

    // Write through root — Disabled does not conflict with writes,
    // so the Disabled entry survives.
    state
        .access(&"alloc0", root, AccessKind::Write)
        .expect("root write should succeed");
    assert!(
        state.contains_tag(&"alloc0", unique),
        "Disabled entry survives writes (does not conflict)"
    );
}
