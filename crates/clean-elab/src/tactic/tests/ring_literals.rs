// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `ring_literals::nonnegative_ring_const_value`.
//!
//! Part of #2601: The ring literal recognizer is the entry point for constant
//! folding in the ring normalizer. These tests verify each recognition path
//! directly rather than relying on full tactic-level integration tests.

use crate::tactic::ring_literals::nonnegative_ring_const_value;
use clean_kernel::Expr;

// ---------------------------------------------------------------------------
// Nat paths
// ---------------------------------------------------------------------------

#[test]
fn test_nat_zero_const() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), Some(0));
}

#[test]
fn test_nat_one_const() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("Nat.one"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), Some(1));
}

#[test]
fn test_nat_numeric_one_const_alias() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("1"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), Some(1));
}

#[test]
fn test_nat_literal_small() {
    let e = Expr::nat_lit(42);
    assert_eq!(nonnegative_ring_const_value(&e), Some(42));
}

#[test]
fn test_nat_literal_zero() {
    let e = Expr::nat_lit(0);
    assert_eq!(nonnegative_ring_const_value(&e), Some(0));
}

#[test]
fn test_nat_succ_zero() {
    // Nat.succ Nat.zero = 1
    let zero = Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]);
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
        zero,
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(1));
}

#[test]
fn test_nat_succ_succ_zero() {
    // Nat.succ (Nat.succ Nat.zero) = 2
    let zero = Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]);
    let succ = |arg| {
        Expr::app(
            Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
            arg,
        )
    };
    let e = succ(succ(zero));
    assert_eq!(nonnegative_ring_const_value(&e), Some(2));
}

#[test]
fn test_nat_succ_literal() {
    // Nat.succ (Lit 5) = 6
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(5),
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(6));
}

// ---------------------------------------------------------------------------
// Int paths
// ---------------------------------------------------------------------------

#[test]
fn test_int_zero_const() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("Int.zero"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), Some(0));
}

#[test]
fn test_int_one_const() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("Int.one"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), Some(1));
}

#[test]
fn test_int_of_nat_zero() {
    // Int.ofNat Nat.zero = 0
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Int.ofNat"), vec![]),
        Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(0));
}

#[test]
fn test_int_of_nat_succ_zero() {
    // Int.ofNat (Nat.succ Nat.zero) = 1
    let inner = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
        Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]),
    );
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Int.ofNat"), vec![]),
        inner,
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(1));
}

#[test]
fn test_int_of_nat_literal() {
    // Int.ofNat (Lit 100) = 100
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(100),
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(100));
}

// ---------------------------------------------------------------------------
// Overflow boundary (checked_add returns None at u64::MAX)
// ---------------------------------------------------------------------------

#[test]
fn test_nat_succ_overflow_returns_none() {
    // Nat.succ (Lit u64::MAX) overflows checked_add → None
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(u64::MAX),
    );
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_nat_succ_near_max_succeeds() {
    // Nat.succ (Lit u64::MAX - 1) = u64::MAX — just under overflow
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(u64::MAX - 1),
    );
    assert_eq!(nonnegative_ring_const_value(&e), Some(u64::MAX));
}

// ---------------------------------------------------------------------------
// Negative / unrecognized paths (must return None)
// ---------------------------------------------------------------------------

#[test]
fn test_unrecognized_const_returns_none() {
    let e = Expr::const_(clean_kernel::name::Name::from_string("Foo.bar"), vec![]);
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_bvar_returns_none() {
    let e = Expr::bvar(0);
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_prop_returns_none() {
    let e = Expr::prop();
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_int_of_nat_non_nat_arg_returns_none() {
    // Int.ofNat applied to a non-Nat expression
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("Int.ofNat"), vec![]),
        Expr::const_(clean_kernel::name::Name::from_string("Foo"), vec![]),
    );
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_non_succ_app_returns_none() {
    // SomeFunc Nat.zero — not Nat.succ
    let e = Expr::app(
        Expr::const_(clean_kernel::name::Name::from_string("SomeFunc"), vec![]),
        Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]),
    );
    assert_eq!(nonnegative_ring_const_value(&e), None);
}

#[test]
fn test_string_literal_returns_none() {
    let e = Expr::str_lit("hello");
    assert_eq!(nonnegative_ring_const_value(&e), None);
}
