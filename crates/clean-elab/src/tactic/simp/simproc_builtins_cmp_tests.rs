// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the Prop-level literal comparison reducer (G41). The
//! end-to-end rows (real `simp` calls, kernel-checked) live in
//! `tactic/tests/simp_lean48_fidelity.rs`.

use super::*;
use crate::tactic::nat_le_bridge::tree_size;
use clean_kernel::expr::{ExprKind, Literal};

fn nat_cmp(head: &str, inst: &str, a: u64, b: u64) -> Expr {
    Expr::apps(
        konst(head),
        [
            konst("Nat"),
            konst(inst),
            Expr::nat_lit(a),
            Expr::nat_lit(b),
        ],
    )
}

fn result_name(r: &SimpResult) -> String {
    const_name(&r.expr).unwrap_or_default()
}

#[test]
fn test_literal_cmp_nat_true_and_false_verdicts_match_the_order() {
    let gt = nat_outcome(
        &nat_cmp("GT.gt", "instLTNat", 1024, 0),
        true,
        &Expr::nat_lit(0),
        &Expr::nat_lit(1024),
    )
    .expect("1024 > 0 decides");
    assert_eq!(result_name(&gt), "True");
    let bad = nat_outcome(
        &nat_cmp("GT.gt", "instLTNat", 0, 1024),
        true,
        &Expr::nat_lit(1024),
        &Expr::nat_lit(0),
    )
    .expect("0 > 1024 decides");
    assert_eq!(result_name(&bad), "False");
    // `n < n` is False, `n ≤ n` is True: the strict offset is applied once.
    let lt_self = nat_outcome(
        &nat_cmp("LT.lt", "instLTNat", 7, 7),
        true,
        &Expr::nat_lit(7),
        &Expr::nat_lit(7),
    )
    .expect("7 < 7 decides");
    assert_eq!(result_name(&lt_self), "False");
    let le_self = nat_outcome(
        &nat_cmp("LE.le", "instLENat", 7, 7),
        false,
        &Expr::nat_lit(7),
        &Expr::nat_lit(7),
    )
    .expect("7 ≤ 7 decides");
    assert_eq!(result_name(&le_self), "True");
}

/// Round 1's lesson: no unary proofs. A 2^32-sized gap must not grow the term.
#[test]
fn test_literal_cmp_nat_proof_is_constant_size_at_two_pow_32() {
    let big = 1u64 << 32;
    let small = nat_outcome(
        &nat_cmp("LT.lt", "instLTNat", 0, 1),
        true,
        &Expr::nat_lit(0),
        &Expr::nat_lit(1),
    )
    .expect("0 < 1 decides");
    let huge = nat_outcome(
        &nat_cmp("LT.lt", "instLTNat", 0, big),
        true,
        &Expr::nat_lit(0),
        &Expr::nat_lit(big),
    )
    .expect("0 < 2^32 decides");
    let refuted = nat_outcome(
        &nat_cmp("LE.le", "instLENat", big, 0),
        false,
        &Expr::nat_lit(big),
        &Expr::nat_lit(0),
    )
    .expect("2^32 ≤ 0 decides");
    let size =
        |r: &SimpResult| tree_size(r.proof.as_ref().expect("a Prop rewrite carries a proof"));
    assert_eq!(
        size(&small),
        size(&huge),
        "the true proof must not depend on the gap"
    );
    assert!(
        size(&refuted) < 200,
        "the refutation is constant-size: {}",
        size(&refuted)
    );
}

#[test]
fn test_literal_cmp_needs_numerals_and_the_canonical_instance() {
    let fvar_like = Expr::const_(Name::from_string("someNat"), vec![]);
    assert!(nat_outcome(&fvar_like, true, &fvar_like, &Expr::nat_lit(3)).is_none());
    assert!(!canonical_instance("Nat", true, &konst("myWeirdLT")));
    assert!(canonical_instance("Nat", true, &konst("instLTNat")));
    assert!(!canonical_instance("Nat", false, &konst("instLTNat")));
    assert!(canonical_instance("Int", true, &konst("Int.instLTInt")));
    assert!(!canonical_instance("Float", true, &konst("instLTFloat")));
}

#[test]
fn test_literal_cmp_int_numeral_shapes() {
    let ofnat = |n: u64| Expr::app(konst("Int.ofNat"), Expr::nat_lit(n));
    let val = |e: &Expr| int_numeral(e).and_then(|v| v.to_i128());
    assert_eq!(val(&ofnat(5)), Some(5));
    let neg = Expr::apps(
        konst("Neg.neg"),
        [konst("Int"), konst("instNegInt"), ofnat(3)],
    );
    assert_eq!(val(&neg), Some(-3));
    let neg_neg = Expr::apps(konst("Neg.neg"), [konst("Int"), konst("instNegInt"), neg]);
    assert_eq!(val(&neg_neg), None, "`-(-3)` is not a numeral");
    assert_eq!(
        val(&Expr::app(konst("Int.negSucc"), Expr::nat_lit(0))),
        Some(-1)
    );
}

fn big_lit(limbs: Vec<u64>) -> Expr {
    Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(limbs))))
}

/// Numerals at and above `2^64` decide like any other (Lean 4.8.0 accepts
/// `(18446744073709551616 : Nat) > 3 := by simp` and `¬ ((2^64 - 1 : Nat) <
/// 2^32) := by simp`; review r4t d5e/e5), and `u64::MAX < k` no longer
/// overflows the strict offset.
#[test]
fn test_literal_cmp_nat_beyond_u64() {
    let two_64 = big_lit(vec![0, 1]);
    let gt = nat_outcome(
        &Expr::apps(
            konst("GT.gt"),
            [
                konst("Nat"),
                konst("instLTNat"),
                two_64.clone(),
                Expr::nat_lit(3),
            ],
        ),
        true,
        &Expr::nat_lit(3),
        &two_64,
    )
    .expect("2^64 > 3 decides");
    assert_eq!(result_name(&gt), "True");
    let max = Expr::nat_lit(u64::MAX);
    let lt = nat_outcome(
        &nat_cmp("LT.lt", "instLTNat", u64::MAX, 1 << 32),
        true,
        &max,
        &Expr::nat_lit(1 << 32),
    )
    .expect("(2^64 - 1) < 2^32 decides");
    assert_eq!(result_name(&lt), "False");
    let self_lt = nat_outcome(
        &nat_cmp("LT.lt", "instLTNat", u64::MAX, u64::MAX),
        true,
        &max,
        &max,
    )
    .expect("u64::MAX < u64::MAX decides without overflow");
    assert_eq!(result_name(&self_lt), "False");
}

/// A numeral is read only at its canonical `OfNat` instance (review r4t q1:
/// `instance weird : OfNat Nat 5 := ⟨7⟩`).
#[test]
fn test_literal_cmp_reads_numerals_only_at_the_canonical_ofnat_instance() {
    let ofnat =
        |inst: Expr| Expr::apps(konst("OfNat.ofNat"), [konst("Nat"), Expr::nat_lit(5), inst]);
    let canonical = ofnat(Expr::app(konst("instOfNatNat"), Expr::nat_lit(5)));
    assert_eq!(nat_numeral(&canonical), Some(BigNat::from(5)));
    assert_eq!(nat_numeral(&ofnat(konst("weird"))), None);
    let wrong_lit = ofnat(Expr::app(konst("instOfNatNat"), Expr::nat_lit(7)));
    assert_eq!(nat_numeral(&wrong_lit), None);
    let int_ofnat =
        |inst: Expr| Expr::apps(konst("OfNat.ofNat"), [konst("Int"), Expr::nat_lit(5), inst]);
    let lean_int = int_ofnat(Expr::app(konst("instOfNat"), Expr::nat_lit(5)));
    assert_eq!(int_numeral(&lean_int).and_then(|v| v.to_i128()), Some(5));
    assert!(int_numeral(&int_ofnat(konst("weirdInt"))).is_none());
}

/// Only the pairs in `allowed` decide: `simp only [Nat.reduceGT]` reads
/// `>` over `Nat` and nothing else, as pinned Lean 4.8.0 does (`(5 : Nat) >
/// 3` by `simp only [Nat.reduceLT]` is "simp made no progress").
#[test]
fn test_literal_cmp_honours_the_named_simprocs() {
    let gt_bit = literal_cmp_simproc(&Name::from_string("Nat.reduceGT")).expect("implemented");
    let lt_bit = literal_cmp_simproc(&Name::from_string("Nat.reduceLT")).expect("implemented");
    assert_ne!(gt_bit, lt_bit);
    assert!(literal_cmp_simproc(&Name::from_string("Nat.reduceLeDiff")).is_none());
    assert!(literal_cmp_simproc(&Name::from_string("Int.reduceGE")).is_some());
    assert_eq!(Cmp::Gt.bit("Nat"), Some(gt_bit));
    assert_eq!(Cmp::Lt.bit("Nat"), Some(lt_bit));
    assert!(Cmp::Gt.bit("Float").is_none());
}
