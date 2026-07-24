// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — Reducibility ordering and should_unfold matrix.
//!
//! `Reducibility::compare` controls delta reduction ordering in def_eq.
//! `Reducibility::should_unfold` determines which definitions unfold at
//! each transparency level. Previously had zero direct test coverage.

use clean_kernel::{Reducibility, TransparencyMode};
use std::cmp::Ordering;

// ===== should_unfold matrix (4 reducibility × 4 transparency) =====

#[test]
fn test_should_unfold_reducible_always() {
    let red = Reducibility::Reducible;
    assert!(red.should_unfold(TransparencyMode::Reducible));
    assert!(red.should_unfold(TransparencyMode::Instances));
    assert!(red.should_unfold(TransparencyMode::Default));
    assert!(red.should_unfold(TransparencyMode::All));
}

#[test]
fn test_should_unfold_regular_not_in_reducible_mode() {
    let reg = Reducibility::Regular(0);
    assert!(!reg.should_unfold(TransparencyMode::Reducible));
    assert!(reg.should_unfold(TransparencyMode::Instances));
    assert!(reg.should_unfold(TransparencyMode::Default));
    assert!(reg.should_unfold(TransparencyMode::All));
}

#[test]
fn test_should_unfold_irreducible_only_all() {
    let irr = Reducibility::Irreducible;
    assert!(!irr.should_unfold(TransparencyMode::Reducible));
    assert!(!irr.should_unfold(TransparencyMode::Instances));
    assert!(!irr.should_unfold(TransparencyMode::Default));
    assert!(irr.should_unfold(TransparencyMode::All));
}

#[test]
fn test_should_unfold_opaque_never() {
    let opq = Reducibility::Opaque;
    assert!(!opq.should_unfold(TransparencyMode::Reducible));
    assert!(!opq.should_unfold(TransparencyMode::Instances));
    assert!(!opq.should_unfold(TransparencyMode::Default));
    assert!(!opq.should_unfold(TransparencyMode::All));
}

// ===== compare ordering =====

#[test]
fn test_compare_reducible_before_regular() {
    assert_eq!(
        Reducibility::Reducible.compare(&Reducibility::Regular(0)),
        Ordering::Less
    );
    assert_eq!(
        Reducibility::Regular(0).compare(&Reducibility::Reducible),
        Ordering::Greater
    );
}

#[test]
fn test_compare_regular_height_ordering() {
    let low = Reducibility::Regular(0);
    let high = Reducibility::Regular(10);
    assert_eq!(high.compare(&low), Ordering::Less);
    assert_eq!(low.compare(&high), Ordering::Greater);
}

#[test]
fn test_compare_same_kind_equal() {
    assert_eq!(
        Reducibility::Reducible.compare(&Reducibility::Reducible),
        Ordering::Equal
    );
    assert_eq!(
        Reducibility::Irreducible.compare(&Reducibility::Irreducible),
        Ordering::Equal
    );
    assert_eq!(
        Reducibility::Opaque.compare(&Reducibility::Opaque),
        Ordering::Equal
    );
    assert_eq!(
        Reducibility::Regular(5).compare(&Reducibility::Regular(5)),
        Ordering::Equal
    );
}

#[test]
fn test_compare_full_ordering_chain() {
    let red = Reducibility::Reducible;
    let reg = Reducibility::Regular(0);
    let irr = Reducibility::Irreducible;
    let opq = Reducibility::Opaque;

    assert_eq!(red.compare(&reg), Ordering::Less);
    assert_eq!(reg.compare(&irr), Ordering::Less);
    assert_eq!(irr.compare(&opq), Ordering::Less);
    assert_eq!(red.compare(&opq), Ordering::Less);
}

// ===== helpers =====

#[test]
fn test_height_returns_zero_for_non_regular() {
    assert_eq!(Reducibility::Reducible.height(), 0);
    assert_eq!(Reducibility::Irreducible.height(), 0);
    assert_eq!(Reducibility::Opaque.height(), 0);
}

#[test]
fn test_height_returns_value_for_regular() {
    assert_eq!(Reducibility::Regular(0).height(), 0);
    assert_eq!(Reducibility::Regular(42).height(), 42);
}

#[test]
fn test_is_regular() {
    assert!(Reducibility::Regular(0).is_regular());
    assert!(Reducibility::Regular(100).is_regular());
    assert!(!Reducibility::Reducible.is_regular());
    assert!(!Reducibility::Irreducible.is_regular());
    assert!(!Reducibility::Opaque.is_regular());
}

#[test]
fn test_semireducible_alias() {
    assert_eq!(Reducibility::SEMIREDUCIBLE, Reducibility::Regular(0));
}
