// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Level canonicalization == spec, and `is_geq` matches the lattice.

use clean_ck0::Level;
use proptest::prelude::*;

#[test]
fn test_imax_right_zero_collapses_to_zero() {
    // imax(_, 0) = 0 (Prop-elimination), at construction.
    let l = Level::imax(Level::param(0), Level::zero());
    assert_eq!(l, Level::zero());
    assert!(l.is_zero());
}

#[test]
fn test_imax_nonzero_right_becomes_max() {
    // imax(u0, succ 0) = max(u0, 1) — right operand provably nonzero.
    let l = Level::imax(Level::param(0), Level::nat(1));
    let expected = Level::max(Level::param(0), Level::nat(1));
    assert_eq!(l, expected);
}

#[test]
fn test_max_is_sorted_and_deduped() {
    // max(u1, u0) and max(u0, u1) canonicalize equal; max(u0,u0)=u0.
    let a = Level::max(Level::param(1), Level::param(0));
    let b = Level::max(Level::param(0), Level::param(1));
    assert_eq!(a, b, "Max operands canonicalize order-insensitively");
    let dup = Level::max(Level::param(0), Level::param(0));
    assert_eq!(dup, Level::param(0), "duplicate Max operands collapse");
}

#[test]
fn test_max_explicit_subsumed_by_offset() {
    // max(1, succ(u0)) keeps both (u0 may be 0); max(0, u0) = u0.
    let z = Level::max(Level::zero(), Level::param(0));
    assert_eq!(z, Level::param(0), "max(0, u) = u");
}

#[test]
fn test_is_geq_reflexive_and_zero_minimum() {
    let u = Level::param(0);
    assert!(Level::is_geq(&u, &u));
    assert!(Level::is_geq(&u, &Level::zero()), "everything >= 0");
    assert!(Level::is_geq(&Level::succ(u.clone()), &u), "succ u >= u");
    assert!(!Level::is_geq(&Level::zero(), &Level::nat(1)), "0 not >= 1");
}

#[test]
fn test_succ_distributes_over_max() {
    // succ(max(u0,u1)) canonicalizes to max(succ u0, succ u1).
    let inner = Level::max(Level::param(0), Level::param(1));
    let s = Level::succ(inner).normalize();
    let expected = Level::max(Level::succ(Level::param(0)), Level::succ(Level::param(1)));
    assert_eq!(s, expected);
}

fn arb_level() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::zero()),
        (0u32..4).prop_map(Level::param),
        (0u32..5).prop_map(Level::nat),
    ];
    leaf.prop_recursive(4, 32, 4, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Level::max(a, b)),
            (inner.clone(), inner).prop_map(|(a, b)| Level::imax(a, b)),
        ]
    })
}

proptest! {
    #[test]
    fn prop_normalize_idempotent(l in arb_level()) {
        // Smart constructors already canonicalize, so normalize is a no-op fixpoint.
        let n1 = l.normalize();
        let n2 = n1.normalize();
        prop_assert_eq!(n1, n2);
    }

    #[test]
    fn prop_canonical_eq_is_structural(l in arb_level()) {
        // A level built two different ways but equal canonical form must be ==.
        let again = l.normalize();
        prop_assert_eq!(l, again);
    }

    #[test]
    fn prop_is_geq_reflexive(l in arb_level()) {
        prop_assert!(Level::is_geq(&l, &l));
    }

    #[test]
    fn prop_succ_geq_base(l in arb_level()) {
        prop_assert!(Level::is_geq(&Level::succ(l.clone()), &l));
    }

    #[test]
    fn prop_zero_is_minimum(l in arb_level()) {
        prop_assert!(Level::is_geq(&l, &Level::zero()));
    }
}
