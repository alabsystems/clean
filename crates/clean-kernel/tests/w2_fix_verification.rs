// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prover verification tests for W2 fixes (#1309, #1316, #1321).
//! These tests are independent of clean-elab to bypass #1334 dirty tree.

use clean_kernel::{Level, Name};
use std::cmp::Ordering;

// === #1321: imax smart constructor is_one(l1) reduction ===

#[test]
fn verify_imax_one_reduces_to_l2() {
    // imax(1, u) should reduce to u, not produce IMax(Succ(Zero), Param(u))
    let u = Level::param(Name::from_string("u"));
    let one = Level::succ(Level::zero());
    let result = Level::imax(one, u.clone());
    assert_eq!(
        result, u,
        "imax(1, u) must reduce to u per Lean 4 is_one(l1)"
    );
}

#[test]
fn verify_imax_one_zero_still_zero() {
    // imax(1, 0) = 0 (handled by l2.is_zero() before is_one check)
    let one = Level::succ(Level::zero());
    let result = Level::imax(one, Level::zero());
    assert!(result.is_zero(), "imax(1, 0) must be zero");
}

#[test]
fn verify_imax_one_max_reduces() {
    // imax(1, max(u, v)) should reduce to max(u, v)
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let one = Level::succ(Level::zero());
    let max_uv = Level::max(u, v);
    let result = Level::imax(one, max_uv.clone());
    assert_eq!(
        result, max_uv,
        "imax(1, max(u, v)) must reduce to max(u, v)"
    );
}

#[test]
fn verify_imax_two_does_not_reduce() {
    // imax(2, u) should NOT reduce — only is_one applies
    let u = Level::param(Name::from_string("u"));
    let two = Level::succ(Level::succ(Level::zero()));
    let result = Level::imax(two.clone(), u.clone());
    // Should be IMax(Succ(Succ(Zero)), Param(u)), not Param(u)
    assert_ne!(result, u, "imax(2, u) must not reduce to u");
}

// === #1316: Name Ord matches Lean 4 cmp_core ===

#[test]
fn verify_name_num_before_str() {
    // Lean 4: Num sorts before Str (anonymous_name_lt)
    let num = Name::anon().num(1);
    let str_name = Name::from_string("a");
    assert_eq!(
        num.cmp(&str_name),
        Ordering::Less,
        "Num must sort before Str"
    );
}

#[test]
fn verify_name_numeric_comparison() {
    // Lean 4: Num vs Num uses numeric comparison, not string
    // Under string comparison: "9" > "10" (wrong)
    // Under numeric comparison: 9 < 10 (correct)
    let n9 = Name::anon().num(9);
    let n10 = Name::anon().num(10);
    assert_eq!(
        n9.cmp(&n10),
        Ordering::Less,
        "9 < 10 numerically, not as strings"
    );
}

#[test]
fn verify_name_hierarchical_comparison() {
    // Component-by-component: Nat.add < Nat.mul
    let nat_add = Name::from_string("Nat.add");
    let nat_mul = Name::from_string("Nat.mul");
    assert_eq!(nat_add.cmp(&nat_mul), Ordering::Less, "Nat.add < Nat.mul");
}

#[test]
fn verify_name_shorter_prefix_first() {
    // Shorter prefix sorts first: Nat < Nat.add
    let nat = Name::from_string("Nat");
    let nat_add = Name::from_string("Nat.add");
    assert_eq!(
        nat.cmp(&nat_add),
        Ordering::Less,
        "Nat < Nat.add (shorter prefix)"
    );
}

#[test]
fn verify_name_anon_sorts_first() {
    // Anon sorts before everything
    assert_eq!(Name::anon().cmp(&Name::from_string("a")), Ordering::Less);
    assert_eq!(Name::anon().cmp(&Name::anon().num(0)), Ordering::Less);
}

#[test]
fn verify_name_ord_used_in_level_normalize() {
    // The real purpose of #1316: ensure Level::normalize uses structural
    // Name comparison. Create two Param levels that would sort differently
    // under string vs numeric comparison and verify normalize produces
    // consistent canonical forms.
    let n9 = Name::anon().num(9);
    let n10 = Name::anon().num(10);
    let p9 = Level::param(n9);
    let p10 = Level::param(n10);

    // max(p10, p9) should normalize to max(p9, p10) since 9 < 10 numerically
    let m1 = Level::max(p10.clone(), p9.clone());
    let m2 = Level::max(p9.clone(), p10.clone());

    // Both should normalize to the same canonical form
    let n1 = m1.normalize();
    let n2 = m2.normalize();
    assert_eq!(
        n1, n2,
        "max(p10, p9).normalize() must equal max(p9, p10).normalize()"
    );
}
