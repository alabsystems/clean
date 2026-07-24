// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::stacked_borrows::AccessKind;

#[test]
fn test_place_construction() {
    let local = Place::local(0);
    let field = local.clone().field("x");
    let deref = local.clone().deref();

    assert!(matches!(local, Place::Local(0)));
    assert!(matches!(field, Place::Field { .. }));
    assert!(matches!(deref, Place::Deref(_)));
}

#[test]
fn test_place_prefix() {
    let base = Place::local(0);
    let field = base.clone().field("x");
    let nested = field.clone().field("y");
    let deref = base.clone().deref();
    let deref_field = deref.clone().field("value");

    assert!(base.is_prefix_of(&base));
    assert!(base.is_prefix_of(&field));
    assert!(base.is_prefix_of(&nested));
    assert!(field.is_prefix_of(&nested));
    assert!(deref.is_prefix_of(&deref_field));

    assert!(!field.is_prefix_of(&base));
    assert!(!nested.is_prefix_of(&base));
    assert!(!base.is_prefix_of(&deref));
    assert!(!deref.is_prefix_of(&base));
}

#[test]
fn test_place_conflicts_stop_at_deref_boundary() {
    let base = Place::local(0);
    let field = base.clone().field("x");
    let deref = base.clone().deref();
    let deref_field = deref.clone().field("value");

    assert!(base.conflicts_with(&field));
    assert!(deref.conflicts_with(&deref_field));
    assert!(!base.conflicts_with(&deref));
    assert!(!field.conflicts_with(&deref_field));
}

#[test]
fn test_ownership_state() {
    let place = Place::local(0);
    let mut state = OwnershipState::new();

    state.mark_owned(place.clone());
    assert!(state.is_owned(&place));
    assert!(!state.is_moved(&place));

    state.mark_moved(place.clone());
    assert!(!state.is_owned(&place));
    assert!(state.is_moved(&place));
}

#[test]
fn test_borrow_checking() {
    let checker = BorrowChecker::new();
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());

    assert!(checker
        .check_borrow(&state, &place, Mutability::Shared, &lifetime)
        .is_ok());
    assert!(checker
        .check_borrow(&state, &place, Mutability::Mutable, &lifetime)
        .is_ok());

    state
        .add_borrow(place.clone(), Mutability::Mutable, lifetime.clone())
        .expect("mutable borrow should produce a tag");

    assert!(checker
        .check_borrow(&state, &place, Mutability::Mutable, &lifetime)
        .is_err());
    assert!(checker
        .check_borrow(&state, &place, Mutability::Shared, &lifetime)
        .is_err());
}

#[test]
fn test_multiple_shared_borrows() {
    let checker = BorrowChecker::new();
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());

    state
        .add_borrow(place.clone(), Mutability::Shared, lifetime.clone())
        .expect("shared borrow should produce a tag");

    assert!(checker
        .check_borrow(&state, &place, Mutability::Shared, &lifetime)
        .is_ok());
}

#[test]
fn test_move_while_borrowed() {
    let checker = BorrowChecker::new();
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());
    state
        .add_borrow(place.clone(), Mutability::Shared, lifetime)
        .expect("shared borrow should produce a tag");

    let result = checker.check_move(&state, &place);
    assert!(matches!(result, Err(BorrowError::MoveWhileBorrowed { .. })));
}

#[test]
fn test_use_after_move() {
    let checker = BorrowChecker::new();
    let place = Place::local(0);

    let mut state = OwnershipState::new();
    state.mark_moved(place.clone());

    let result = checker.check_use(&state, &place);
    assert!(matches!(result, Err(BorrowError::UseAfterMove { .. })));
}

#[test]
fn test_end_borrow() {
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());
    state
        .add_borrow(place.clone(), Mutability::Mutable, lifetime.clone())
        .expect("mutable borrow should produce a tag");

    assert!(state.is_borrowed(&place));

    state.end_borrows(&lifetime);

    assert!(state.is_owned(&place));
    assert!(!state.is_borrowed(&place));
}

#[test]
fn test_move_analysis() {
    let mut analysis = MoveAnalysis::new();

    let base = Place::local(0);
    let field_x = base.clone().field("x");
    let field_y = base.clone().field("y");

    analysis.record_move(&field_x);

    assert!(analysis.is_moved(&field_x));
    assert!(!analysis.is_moved(&field_y));
    assert!(analysis.is_partially_moved(&base));

    let moved = analysis
        .moved_fields(&base)
        .expect("base should be partial");
    assert!(moved.contains("x"));
    assert!(!moved.contains("y"));
}

#[test]
fn test_stacked_borrows_tags_reset_when_borrow_ends() {
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());
    let root = state
        .root_tag(&place)
        .expect("owned place should have a root");

    let shared = state
        .add_borrow(place.clone(), Mutability::Shared, lifetime.clone())
        .expect("shared borrow should retag the place");

    assert_ne!(root, shared);
    assert_eq!(state.borrow_tag(&place), Some(shared));
    state
        .access_place(&place, shared, AccessKind::Read)
        .expect("shared borrow should allow reads");
    assert!(matches!(
        state.access_place(&place, shared, AccessKind::Write),
        Err(BorrowError::AliasingInvalidAccess { tag, .. }) if tag == shared
    ));

    state.end_borrows(&lifetime);
    assert_eq!(state.borrow_tag(&place), Some(root));
}

#[test]
fn test_stacked_borrows_protector_blocks_conflicting_root_write() {
    let place = Place::local(0);
    let lifetime = Lifetime::Named("a".to_string());

    let mut state = OwnershipState::new();
    state.mark_owned(place.clone());
    let root = state
        .root_tag(&place)
        .expect("owned place should have a root");
    let protector = state.new_protector();
    let shared = state
        .add_borrow_with_protector(place.clone(), Mutability::Shared, lifetime, Some(protector))
        .expect("protected borrow should retag the place");

    let err = state.access_place(&place, root, AccessKind::Write);
    assert!(matches!(
        err,
        Err(BorrowError::AliasingProtected { blocked_by, .. }) if blocked_by == shared
    ));

    state.release_protector(protector);
    state
        .access_place(&place, root, AccessKind::Write)
        .expect("root write should succeed once the protector is gone");
}

#[test]
fn test_whole_place_write_invalidates_descendant_field_borrow() {
    let root_place = Place::local(0);
    let field_place = root_place.clone().field("x");

    let mut state = OwnershipState::new();
    state.mark_owned(root_place.clone());

    let field_tag = state
        .retag_place(&field_place, BorrowPermission::Unique, None)
        .expect("field retag should succeed");

    let root_tag = state.current_or_root_tag(&root_place);
    state
        .access_whole_place(&root_place, root_tag, AccessKind::Write)
        .expect("whole-place write should succeed");

    let field_root = state
        .root_tag(&field_place)
        .expect("field place should have a root");
    assert_eq!(
        state.borrow_tag(&field_place),
        Some(field_root),
        "whole-place write should reset the descendant current tag to its root"
    );

    let err = state.access_place(&field_place, field_tag, AccessKind::Read);
    assert!(
        matches!(err, Err(BorrowError::AliasingUnknownTag { tag, .. }) if tag == field_tag),
        "whole-place write should retire the stale descendant tag, got {err:?}"
    );

    state
        .access_place(&field_place, field_root, AccessKind::Write)
        .expect("owner writes through the reset descendant root should still succeed");
}
