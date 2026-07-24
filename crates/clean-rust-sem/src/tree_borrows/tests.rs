// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_ensure_base_exposes_per_allocation_state() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");

    let state = borrows.state(&"alloc0").expect("missing tree state");
    assert_eq!(state.root_tag(), root);
    assert_eq!(state.permission(root), Some(Permission::Active));
}

#[test]
fn test_reserved_tag_activates_on_write() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");
    let reserved = borrows
        .reserve(&"alloc0", root, None)
        .expect("reserve should succeed");

    assert_eq!(
        borrows.permission(&"alloc0", reserved),
        Some(Permission::Reserved)
    );
    borrows
        .access(&"alloc0", reserved, AccessKind::Read)
        .expect("reserved tag should allow reads");
    assert_eq!(
        borrows.permission(&"alloc0", reserved),
        Some(Permission::Reserved)
    );

    borrows
        .access(&"alloc0", reserved, AccessKind::Write)
        .expect("reserved write should activate");
    assert_eq!(
        borrows.permission(&"alloc0", reserved),
        Some(Permission::Active)
    );
}

#[test]
fn test_write_disables_off_path_sibling_subtree() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");
    let left = borrows
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("left retag should succeed");
    let right = borrows
        .retag(&"alloc0", root, BorrowPermission::SharedReadWrite, None)
        .expect("right retag should succeed");
    let right_child = borrows
        .retag(&"alloc0", right, BorrowPermission::SharedReadOnly, None)
        .expect("right child retag should succeed");

    borrows
        .access(&"alloc0", left, AccessKind::Write)
        .expect("left write should succeed");

    assert_eq!(
        borrows.permission(&"alloc0", root),
        Some(Permission::Frozen)
    );
    assert_eq!(
        borrows.permission(&"alloc0", left),
        Some(Permission::Active)
    );
    assert_eq!(
        borrows.permission(&"alloc0", right),
        Some(Permission::Disabled)
    );
    assert_eq!(
        borrows.permission(&"alloc0", right_child),
        Some(Permission::Disabled)
    );

    let err = borrows.access(&"alloc0", right, AccessKind::Read);
    assert!(matches!(
        err,
        Err(TreeBorrowsError::IncompatibleAccess {
            tag,
            access: AccessKind::Read,
            ..
        }) if tag == right
    ));
}

#[test]
fn test_foreign_read_freezes_without_disabling() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");
    let unique = borrows
        .retag(&"alloc0", root, BorrowPermission::Unique, None)
        .expect("unique retag should succeed");

    borrows
        .access(&"alloc0", root, AccessKind::Read)
        .expect("root read should succeed");

    assert_eq!(
        borrows.permission(&"alloc0", unique),
        Some(Permission::Frozen)
    );
    borrows
        .access(&"alloc0", unique, AccessKind::Read)
        .expect("frozen tag should still read");

    let err = borrows.access(&"alloc0", unique, AccessKind::Write);
    assert!(matches!(
        err,
        Err(TreeBorrowsError::IncompatibleAccess {
            tag,
            access: AccessKind::Write,
            ..
        }) if tag == unique
    ));
}

#[test]
fn test_foreign_read_is_more_permissive_for_protected_nodes() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");
    let protector = borrows.new_protector();
    let protected = borrows
        .retag(&"alloc0", root, BorrowPermission::Unique, Some(protector))
        .expect("protected retag should succeed");
    let reader = borrows
        .retag(&"alloc0", root, BorrowPermission::SharedReadWrite, None)
        .expect("reader retag should succeed");

    borrows
        .access(&"alloc0", reader, AccessKind::Read)
        .expect("foreign read should not trip the protector");

    assert_eq!(
        borrows.permission(&"alloc0", protected),
        Some(Permission::Frozen)
    );
}

#[test]
fn test_protected_foreign_write_is_rejected_atomically() {
    let mut borrows = TreeBorrows::new();
    let root = borrows.ensure_base("alloc0");
    let protector = borrows.new_protector();
    let protected = borrows
        .retag(&"alloc0", root, BorrowPermission::Unique, Some(protector))
        .expect("protected retag should succeed");
    let writer = borrows
        .reserve(&"alloc0", root, None)
        .expect("reserve should succeed");

    let err = borrows.access(&"alloc0", writer, AccessKind::Write);
    assert!(matches!(
        err,
        Err(TreeBorrowsError::ProtectedConflict {
            blocked_by,
            access: AccessKind::Write,
            ..
        }) if blocked_by == protected
    ));

    assert_eq!(
        borrows.permission(&"alloc0", root),
        Some(Permission::Active)
    );
    assert_eq!(
        borrows.permission(&"alloc0", protected),
        Some(Permission::Active)
    );
    assert_eq!(
        borrows.permission(&"alloc0", writer),
        Some(Permission::Reserved)
    );
}
