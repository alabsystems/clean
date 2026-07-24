// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BigNat::Big code paths.
//!
//! This module tests multi-limb BigNat handling in:
//! - `nat_lit_to_constructor()` multi-limb subtraction with borrow
//! - `BigNat::from_limbs()` normalization logic
//! - `BigNat::Big` Display formatting

use super::*;
use crate::expr::{BigNat, BinderInfo, Literal};

// =============================================================================
// BigNat::from_limbs normalization tests
// =============================================================================

#[test]
fn test_bignat_from_limbs_empty() {
    // Empty vec should produce Small(0)
    let n = BigNat::from_limbs(vec![]);
    assert_eq!(n, BigNat::Small(0));
}

#[test]
fn test_bignat_from_limbs_single() {
    // Single limb should produce Small
    let n = BigNat::from_limbs(vec![42]);
    assert_eq!(n, BigNat::Small(42));
}

#[test]
fn test_bignat_from_limbs_single_max() {
    // Single limb at u64::MAX should produce Small
    let n = BigNat::from_limbs(vec![u64::MAX]);
    assert_eq!(n, BigNat::Small(u64::MAX));
}

#[test]
fn test_bignat_from_limbs_two_limbs() {
    // [0, 1] represents 2^64 (little-endian)
    let n = BigNat::from_limbs(vec![0, 1]);
    assert!(matches!(n, BigNat::Big(_)));
    if let BigNat::Big(limbs) = n {
        assert_eq!(limbs, vec![0, 1]);
    }
}

#[test]
fn test_bignat_from_limbs_normalization_trailing_zeros() {
    // [42, 0, 0] should normalize to Small(42)
    let n = BigNat::from_limbs(vec![42, 0, 0]);
    assert_eq!(n, BigNat::Small(42));
}

#[test]
fn test_bignat_from_limbs_normalization_mixed() {
    // [1, 2, 0, 0] should normalize to [1, 2]
    let n = BigNat::from_limbs(vec![1, 2, 0, 0]);
    assert!(matches!(n, BigNat::Big(_)));
    if let BigNat::Big(limbs) = n {
        assert_eq!(limbs, vec![1, 2]);
    }
}

#[test]
fn test_bignat_from_limbs_all_zeros() {
    // [0, 0, 0] should normalize to Small(0)
    let n = BigNat::from_limbs(vec![0, 0, 0]);
    assert_eq!(n, BigNat::Small(0));
}

// =============================================================================
// BigNat::Big Display formatting tests
// =============================================================================

#[test]
fn test_bignat_display_small() {
    let n = BigNat::Small(42);
    assert_eq!(format!("{}", n), "42");
}

// =============================================================================
// BigNat::from_radix_str — arbitrary-precision literal folding (B27)
// =============================================================================

#[test]
fn test_from_radix_str_small_decimal() {
    assert_eq!(BigNat::from_radix_str("0", 10), Some(BigNat::Small(0)));
    assert_eq!(BigNat::from_radix_str("42", 10), Some(BigNat::Small(42)));
    assert_eq!(
        BigNat::from_radix_str("18446744073709551615", 10),
        Some(BigNat::Small(u64::MAX))
    );
}

#[test]
fn test_from_radix_str_two_pow_64_every_base() {
    let two_pow_64 = BigNat::from_limbs(vec![0, 1]);
    // decimal, hex, octal, binary — all fold to the exact same multi-limb value.
    assert_eq!(
        BigNat::from_radix_str("18446744073709551616", 10),
        Some(two_pow_64.clone())
    );
    assert_eq!(
        BigNat::from_radix_str("10000000000000000", 16),
        Some(two_pow_64.clone())
    );
    assert_eq!(
        BigNat::from_radix_str("2000000000000000000000", 8),
        Some(two_pow_64.clone())
    );
    let binary = format!("1{}", "0".repeat(64));
    assert_eq!(BigNat::from_radix_str(&binary, 2), Some(two_pow_64));
}

#[test]
fn test_from_radix_str_ignores_underscores() {
    assert_eq!(
        BigNat::from_radix_str("1_0000_0000_0000_0000", 16),
        Some(BigNat::from_limbs(vec![0, 1]))
    );
    assert_eq!(
        BigNat::from_radix_str("1_000", 10),
        Some(BigNat::Small(1000))
    );
}

#[test]
fn test_from_radix_str_rejects_empty_and_invalid() {
    assert_eq!(BigNat::from_radix_str("", 10), None);
    assert_eq!(BigNat::from_radix_str("_", 10), None);
    // 'g' is not a hex digit.
    assert_eq!(BigNat::from_radix_str("1g", 16), None);
    // '2' is not a binary digit.
    assert_eq!(BigNat::from_radix_str("102", 2), None);
}

#[test]
fn test_from_radix_str_hex_case_insensitive() {
    assert_eq!(BigNat::from_radix_str("FF", 16), Some(BigNat::Small(255)));
    assert_eq!(BigNat::from_radix_str("ff", 16), Some(BigNat::Small(255)));
}

#[test]
fn test_bignat_display_big_two_pow_64() {
    // 2^64 = [0, 1] in little-endian
    let n = BigNat::Big(vec![0, 1]);
    // Display should show hex: 0x0000000000000001 0000000000000000
    let s = format!("{}", n);
    assert!(s.starts_with("0x"));
    // Should be high limb first (big-endian in output)
    assert_eq!(s, "0x00000000000000010000000000000000");
}

#[test]
fn test_bignat_display_big_custom() {
    // [0xDEADBEEF, 0xCAFEBABE] represents a large number
    let n = BigNat::Big(vec![0xDEADBEEF, 0xCAFEBABE]);
    let s = format!("{}", n);
    assert!(s.starts_with("0x"));
    // High limb (0xCAFEBABE) first, then low limb (0xDEADBEEF)
    assert_eq!(s, "0x00000000cafebabe00000000deadbeef");
}

// =============================================================================
// BigNat::to_u64 tests
// =============================================================================

#[test]
fn test_bignat_to_u64_small() {
    assert_eq!(BigNat::Small(42).to_u64(), Some(42));
    assert_eq!(BigNat::Small(0).to_u64(), Some(0));
    assert_eq!(BigNat::Small(u64::MAX).to_u64(), Some(u64::MAX));
}

#[test]
fn test_bignat_to_u64_big_returns_none() {
    let n = BigNat::Big(vec![0, 1]); // 2^64, too large for u64
    assert_eq!(n.to_u64(), None);
}

// =============================================================================
// BigNat::limbs tests
// =============================================================================

#[test]
fn test_bignat_limbs_small() {
    let n = BigNat::Small(42);
    assert_eq!(n.limbs(), &[42]);
}

#[test]
fn test_bignat_limbs_big() {
    let n = BigNat::Big(vec![1, 2, 3]);
    assert_eq!(n.limbs(), &[1, 2, 3]);
}

// =============================================================================
// nat_lit_to_constructor BigNat::Big tests
// =============================================================================

#[test]
fn test_nat_lit_to_constructor_big_two_pow_64() {
    // Test that nat_lit_to_constructor works with 2^64 via iota reduction.
    // 2^64 = [0, 1], so 2^64 - 1 = [MAX, 0] = [MAX] = Small(MAX)
    //
    // Note: whnf on a bare literal does NOT convert to constructor form.
    // The conversion only happens during iota reduction (when Nat.rec is applied).
    //
    // We use a motive that immediately returns, so we only test ONE step of reduction
    // (not 2^64 steps!). The succ_case returns a constant, so we verify that:
    // 1. The BigNat::Big literal was recognized as a non-zero value
    // 2. nat_lit_to_constructor was called and produced Nat.succ(pred)
    // 3. The succ branch was taken (not the zero branch)
    let mut env = Environment::new();
    env.init_nat().unwrap(); // Register Nat type and Nat.rec recursor
    let tc = TypeChecker::new(&env);

    // Create Nat literal for 2^64
    let big_nat = BigNat::Big(vec![0, 1]);
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(big_nat.clone())));

    // Build Nat.rec application: Nat.rec motive zero_case succ_case big_nat
    // motive : Nat → Nat (constant function returning Nat)
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat_type.clone(), nat_type.clone());

    // zero_case returns a marker value (42) so we can tell if it was taken
    let zero_case = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));

    // succ_case ignores both arguments and returns a different marker (99)
    // This avoids recursion - we just check that the succ branch is taken
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(99)))),
        ),
    );

    // Nat.rec at universe level 1 (since motive returns Type 0)
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Apply: Nat.rec motive zero_case succ_case nat_lit
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
        nat_lit,
    );

    // WHNF should trigger iota reduction, which calls nat_lit_to_constructor
    let result = tc.whnf(&app);

    // The result should be 99 (from succ_case), NOT 42 (from zero_case)
    // This proves nat_lit_to_constructor recognized BigNat::Big([0,1]) as non-zero
    assert_eq!(
        result,
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(99)))),
        "Nat.rec on BigNat::Big should take succ branch (expected 99). Got: {:?}",
        result
    );
}

#[test]
fn test_nat_lit_to_constructor_big_with_borrow() {
    // Test subtraction with borrow across limb boundary via iota reduction.
    // 2^64 + 1 = [1, 1], so (2^64 + 1) - 1 = [0, 1] = 2^64
    //
    // We verify the borrow propagation by using a succ_case that captures
    // the predecessor value and returns it as part of a recognizable pattern.
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);

    let big_nat = BigNat::Big(vec![1, 1]); // 2^64 + 1
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(big_nat.clone())));

    // Build Nat.rec application similar to test above
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat_type.clone(), nat_type.clone());

    // zero_case: marker 42
    let zero_case = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));

    // succ_case: return the predecessor n (first arg), ignoring IH
    // This lets us see what nat_lit_to_constructor computed as the predecessor
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::bvar(1), // Return n (the predecessor)
        ),
    );

    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
        nat_lit,
    );

    let result = tc.whnf(&app);

    // The result should be the predecessor: 2^64 + 1 - 1 = 2^64 = [0, 1]
    // nat_lit_to_constructor should have computed [1, 1] - 1 = [0, 1] with borrow
    assert_eq!(
        result,
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1])))),
        "nat_lit_to_constructor should compute [1,1] - 1 = [0,1] with borrow. Got: {:?}",
        result
    );
}

#[test]
fn test_nat_lit_to_constructor_big_subtraction_normalizes() {
    // Test that subtraction preserves multi-limb values via iota reduction.
    // [1, 0, 1] - 1 = [0, 0, 1] (stays Big with 3 limbs)
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);

    // Value: 2^128 + 1 = [1, 0, 1]
    let big_nat = BigNat::Big(vec![1, 0, 1]);
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(big_nat.clone())));

    // Build Nat.rec application that returns the predecessor
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat_type.clone(), nat_type.clone());
    let zero_case = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::bvar(1), // Return n (the predecessor)
        ),
    );

    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
        nat_lit,
    );

    let result = tc.whnf(&app);

    // Predecessor of [1, 0, 1] is [0, 0, 1]
    assert_eq!(
        result,
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 0, 1])))),
        "nat_lit_to_constructor should compute [1,0,1] - 1 = [0,0,1]. Got: {:?}",
        result
    );
}

#[test]
fn test_nat_lit_to_constructor_big_boundary_subtraction() {
    // Test boundary via iota reduction: [0, 1] - 1 = [MAX, 0] which normalizes to Small(MAX)
    // This tests that trailing zero limbs are properly removed during normalization.
    let mut env = Environment::new();
    env.init_nat().unwrap();
    let tc = TypeChecker::new(&env);

    let big_nat = BigNat::Big(vec![0, 1]); // 2^64
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(big_nat.clone())));

    // Build Nat.rec application that returns the predecessor
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat_type.clone(), nat_type.clone());
    let zero_case = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat_type.clone(),
            Expr::bvar(1), // Return n (the predecessor)
        ),
    );

    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(nat_rec, motive), zero_case), succ_case),
        nat_lit,
    );

    let result = tc.whnf(&app);

    // 2^64 - 1 = u64::MAX, should normalize to Small(MAX)
    // [0, 1] - 1 = [MAX, 0] → normalized to Small(MAX)
    assert_eq!(
        result,
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(u64::MAX)))),
        "nat_lit_to_constructor should normalize [0,1] - 1 = Small(MAX). Got: {:?}",
        result
    );
}

// =============================================================================
// Type inference with BigNat::Big
// =============================================================================

#[test]
fn test_infer_type_bignat_big() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Create a BigNat::Big literal (2^64)
    let big_nat = BigNat::Big(vec![0, 1]);
    let expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(big_nat)));

    // Should infer type Nat
    let ty = tc.infer_type(&expr).unwrap();
    assert_eq!(ty, Expr::const_(Name::from_string("Nat"), vec![]));
}

// =============================================================================
// Definitional equality with BigNat::Big
// =============================================================================

#[test]
fn test_def_eq_bignat_big_same() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let n1 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));
    let n2 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));

    assert!(tc.is_def_eq(&n1, &n2), "Same BigNat::Big should be def_eq");
}

#[test]
fn test_def_eq_bignat_big_different() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let n1 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1])))); // 2^64
    let n2 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![1, 1])))); // 2^64 + 1

    assert!(
        !tc.is_def_eq(&n1, &n2),
        "Different BigNat::Big should not be def_eq"
    );
}

#[test]
fn test_def_eq_bignat_big_vs_small() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // These represent different values, should not be equal
    let big = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1])))); // 2^64
    let small = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));

    assert!(
        !tc.is_def_eq(&big, &small),
        "BigNat::Big and BigNat::Small should not be def_eq"
    );
}

// =============================================================================
// is_def_eq_offset / is_nat_succ_expr with BigNat::Big
// =============================================================================

/// Test that is_def_eq_offset correctly handles two equal BigNat::Big literals
/// through successor peeling via is_nat_succ_expr.
///
/// is_nat_succ_expr has its own BigNat subtraction logic (lines 528-548 of
/// reduction.rs) that is duplicated from nat_lit_to_constructor (lines 892-910).
/// This test exercises is_nat_succ_expr indirectly through is_def_eq to verify
/// the BigNat path works end-to-end through the def_eq successor peeling.
///
/// Regression guard for Risk R6: duplicated BigNat predecessor logic between
/// is_nat_succ_expr and nat_lit_to_constructor.
#[test]
fn test_def_eq_offset_bignat_big_equal() {
    // Two identical BigNat::Big literals should be def_eq.
    // is_def_eq_offset is called early in is_def_eq for Nat-typed expressions
    // and uses is_nat_succ_expr to peel successors from both sides.
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 + 1 represented as BigNat::Big([1, 1])
    let n1 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![1, 1]))));
    let n2 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![1, 1]))));

    assert!(
        tc.is_def_eq(&n1, &n2),
        "Equal BigNat::Big([1,1]) should be def_eq via offset peeling"
    );
}

/// Test is_nat_succ_expr BigNat boundary: 2^64 and 2^64 should be equal.
/// This is the critical boundary where BigNat::Big([0, 1]) must subtract to
/// BigNat::Small(u64::MAX), testing the normalization path in is_nat_succ_expr.
#[test]
fn test_def_eq_offset_bignat_boundary_two_pow_64() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 = BigNat::Big([0, 1])
    // is_nat_succ_expr should compute predecessor = BigNat::Small(u64::MAX)
    let a = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));
    let b = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));

    assert!(
        tc.is_def_eq(&a, &b),
        "BigNat::Big([0,1]) == BigNat::Big([0,1]) should hold via successor peeling"
    );
}

/// Test that two different BigNat::Big values are NOT def_eq.
/// This verifies is_nat_succ_expr peeling produces different predecessors.
#[test]
fn test_def_eq_offset_bignat_big_different() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 vs 2^64 + 1
    let a = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));
    let b = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![1, 1]))));

    assert!(
        !tc.is_def_eq(&a, &b),
        "BigNat::Big([0,1]) != BigNat::Big([1,1])"
    );
}

/// Test that BigNat::Big successor peeling crosses the Big/Small boundary correctly.
/// BigNat::Big([0, 1]) (= 2^64) peeled once = BigNat::Small(u64::MAX).
/// BigNat::Small(u64::MAX) peeled once = BigNat::Small(u64::MAX - 1).
/// So is_def_eq(BigNat::Big([0,1]), Nat.succ(BigNat::Small(u64::MAX))) should hold
/// through one round of successor peeling.
#[test]
fn test_def_eq_offset_bignat_big_vs_succ_small_max() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 2^64 as BigNat::Big
    let big = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(vec![0, 1]))));

    // Nat.succ(u64::MAX) — explicit successor application
    let succ_max = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(u64::MAX)))),
    );

    // Both represent 2^64.
    // is_nat_succ_expr(BigNat::Big([0,1])) = BigNat::Small(u64::MAX) (via subtraction)
    // is_nat_succ_expr(Nat.succ(u64::MAX)) = SmallNat(u64::MAX) (via App match)
    // Then recursion compares SmallNat(u64::MAX) vs SmallNat(u64::MAX) → equal
    assert!(
        tc.is_def_eq(&big, &succ_max),
        "BigNat::Big([0,1]) should equal Nat.succ(u64::MAX) via offset peeling"
    );
}
