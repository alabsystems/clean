// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property tests for the arbitrary-precision `ExternalRational`.
//!
//! `ExternalRational` is now backed by `num_rational::BigRational` (a `Copy`
//! handle into a thread-local interning arena), so there is no longer an `i64`
//! `num`/`den` field pair, no public `gcd_*` helper, and arithmetic is exact and
//! *infallible* (no overflow path). These strategies therefore exercise
//! bignum-range magnitudes — values far beyond `i64`/`i128` — constructed via
//! the string parser, and assert value-level algebra rather than field shapes.

use super::*;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Zero};
use proptest::prelude::*;

/// Build an `ExternalRational` from a (numerator, denominator) `BigInt` pair by
/// rendering the canonical `"n/d"` string and parsing it back through the same
/// grammar the fixtures use. Panics on a zero denominator (callers never pass
/// one); this is test-only.
fn rat_from_bigints(num: &BigInt, den: &BigInt) -> ExternalRational {
    let s = format!("{num}/{den}");
    parse_rational_str_for_test(&s).expect("bignum n/d string should parse")
}

/// Strategy for arbitrary-precision signed numerators that overflow i64/i128.
/// We assemble magnitudes up to ~256 bits from a random little-endian byte
/// vector, then apply a random sign.
fn big_num() -> impl Strategy<Value = BigInt> {
    (prop::collection::vec(any::<u8>(), 1..=32), any::<bool>()).prop_map(|(bytes, neg)| {
        let mag = BigInt::from_bytes_le(Sign::Plus, &bytes);
        if neg {
            -mag
        } else {
            mag
        }
    })
}

/// Strategy for arbitrary-precision *non-zero* denominators (bignum range).
fn big_nonzero_den() -> impl Strategy<Value = BigInt> {
    (prop::collection::vec(any::<u8>(), 1..=32), any::<bool>()).prop_map(|(bytes, neg)| {
        let mut mag = BigInt::from_bytes_le(Sign::Plus, &bytes);
        if mag.is_zero() {
            mag = BigInt::one();
        }
        if neg {
            -mag
        } else {
            mag
        }
    })
}

/// Strategy for arbitrary-precision rationals (numerator and denominator both
/// bignum-range). The denominator is always non-zero.
fn big_rational() -> impl Strategy<Value = ExternalRational> {
    (big_num(), big_nonzero_den()).prop_map(|(n, d)| rat_from_bigints(&n, &d))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    // ----------------------------------------------------------------
    // Construction and Normalization
    // ----------------------------------------------------------------

    // After construction the value is sign-normalized and reduced. We can no
    // longer inspect `den > 0` directly (no fields), so we check that the
    // canonical string form never carries a negative or zero denominator: a
    // reduced `BigRational` renders either as an integer "n" or as "n/d" with
    // d a positive integer > 1.
    #[test]
    fn new_normalizes_to_canonical_string(num in big_num(), den in big_nonzero_den()) {
        let r = rat_from_bigints(&num, &den);
        let s = r.to_compact_string();
        match s.split_once('/') {
            None => {
                // Pure integer form: must be a valid signed integer literal.
                prop_assert!(s.parse::<BigInt>().is_ok(), "integer form must parse: {s}");
            }
            Some((_, d)) => {
                let d: BigInt = d.parse().expect("denominator must parse");
                prop_assert!(d > BigInt::one(), "denominator must be a positive integer > 1, got {d}");
            }
        }
    }

    // A reduced rational round-trips through its own canonical string form:
    // parsing `to_compact_string()` yields an equal value.
    #[test]
    fn canonical_string_roundtrips(num in big_num(), den in big_nonzero_den()) {
        let r = rat_from_bigints(&num, &den);
        let reparsed = parse_rational_str_for_test(&r.to_compact_string())
            .expect("canonical form should reparse");
        prop_assert_eq!(reparsed, r, "to_compact_string should round-trip");
    }

    #[test]
    fn zero_denominator_rejected(num in big_num()) {
        // The string parser rejects "n/0" as a schema error.
        let result = parse_rational_str_for_test(&format!("{num}/0"));
        prop_assert!(result.is_err(), "zero denominator should be rejected");
    }

    // ----------------------------------------------------------------
    // Arithmetic Properties (exact, infallible)
    // ----------------------------------------------------------------

    #[test]
    fn add_commutative(a in big_rational(), b in big_rational()) {
        // Bignum arithmetic never overflows, so both directions always succeed
        // and must be exactly equal.
        let ab = a.add(b).expect("exact add never fails");
        let ba = b.add(a).expect("exact add never fails");
        prop_assert_eq!(ab, ba, "add should be commutative");
    }

    #[test]
    fn add_associative(a in big_rational(), b in big_rational(), c in big_rational()) {
        let left = a.add(b).and_then(|ab| ab.add(c)).expect("exact add never fails");
        let right = b.add(c).and_then(|bc| a.add(bc)).expect("exact add never fails");
        prop_assert_eq!(left, right, "add should be associative");
    }

    #[test]
    fn mul_commutative(a in big_rational(), b in big_rational()) {
        let ab = a.mul(b).expect("exact mul never fails");
        let ba = b.mul(a).expect("exact mul never fails");
        prop_assert_eq!(ab, ba, "mul should be commutative");
    }

    #[test]
    fn mul_distributes_over_add(a in big_rational(), b in big_rational(), c in big_rational()) {
        // a * (b + c) == a*b + a*c, exactly.
        let lhs = b.add(c).and_then(|bc| a.mul(bc)).expect("exact arithmetic never fails");
        let ab = a.mul(b).expect("exact mul never fails");
        let ac = a.mul(c).expect("exact mul never fails");
        let rhs = ab.add(ac).expect("exact add never fails");
        prop_assert_eq!(lhs, rhs, "mul should distribute over add");
    }

    #[test]
    fn mul_identity(a in big_rational()) {
        let result = a.mul(ExternalRational::ONE).expect("exact mul never fails");
        prop_assert_eq!(result, a, "mul by 1 should be identity");
    }

    #[test]
    fn add_identity(a in big_rational()) {
        let result = a.add(ExternalRational::ZERO).expect("exact add never fails");
        prop_assert_eq!(result, a, "add 0 should be identity");
    }

    #[test]
    fn neg_involution(a in big_rational()) {
        // No i64::MIN edge case under bignum: neg is always exact.
        let neg_neg_a = a.neg().neg();
        prop_assert_eq!(neg_neg_a, a, "neg(neg(a)) should equal a");
    }

    #[test]
    fn add_neg_is_zero(a in big_rational()) {
        let result = a.add(a.neg()).expect("exact add never fails");
        prop_assert!(result.is_zero(), "a + (-a) should be zero");
    }

    #[test]
    fn sub_as_add_neg(a in big_rational(), b in big_rational()) {
        // a - b should equal a + (-b), exactly.
        let sub = a.sub(b).expect("exact sub never fails");
        let add_neg = a.add(b.neg()).expect("exact add never fails");
        prop_assert_eq!(sub, add_neg, "a-b should equal a+(-b)");
    }

    // ----------------------------------------------------------------
    // Ordering Properties
    // ----------------------------------------------------------------

    #[test]
    fn cmp_reflexive(a in big_rational()) {
        prop_assert_eq!(a.cmp(&a), std::cmp::Ordering::Equal, "a should equal itself");
    }

    #[test]
    fn cmp_antisymmetric(a in big_rational(), b in big_rational()) {
        let ab = a.cmp(&b);
        let ba = b.cmp(&a);
        prop_assert_eq!(ab, ba.reverse(), "cmp should be antisymmetric");
    }

    #[test]
    fn cmp_transitive(a in big_rational(), b in big_rational(), c in big_rational()) {
        if a.cmp(&b) != std::cmp::Ordering::Greater && b.cmp(&c) != std::cmp::Ordering::Greater {
            prop_assert!(a.cmp(&c) != std::cmp::Ordering::Greater, "cmp should be transitive");
        }
    }

    // ----------------------------------------------------------------
    // Edge Cases
    // ----------------------------------------------------------------

    #[test]
    fn neg_negates_sign(a in big_rational()) {
        let n = a.neg();
        if a.is_zero() {
            prop_assert!(n.is_zero(), "neg of zero is zero");
        } else if a.is_positive() {
            prop_assert!(n.is_negative(), "neg of positive is negative");
        } else {
            prop_assert!(n.is_positive(), "neg of negative is positive");
        }
    }

    #[test]
    fn from_int_is_integer(n in any::<i64>()) {
        // from_int yields an integer-valued rational: its canonical form has no
        // denominator separator and equals the decimal of n.
        let r = ExternalRational::from_int(n);
        prop_assert_eq!(r.to_compact_string(), n.to_string());
    }

    #[test]
    fn from_big_int_is_integer(n in big_num()) {
        // Integer-valued bignum rationals render as the bare integer string.
        let r = rat_from_bigints(&n, &BigInt::one());
        prop_assert_eq!(r.to_compact_string(), n.to_string());
    }

    #[test]
    fn is_zero_correct(num in big_num(), den in big_nonzero_den()) {
        let r = rat_from_bigints(&num, &den);
        prop_assert_eq!(r.is_zero(), num.is_zero(), "is_zero should match num == 0");
    }

    #[test]
    fn sign_functions_correct(num in big_num(), den in big_nonzero_den()) {
        let r = rat_from_bigints(&num, &den);
        // Exactly one of is_zero / is_positive / is_negative holds.
        let flags = [r.is_zero(), r.is_positive(), r.is_negative()];
        let count = flags.iter().filter(|&&b| b).count();
        prop_assert_eq!(count, 1, "exactly one sign predicate must hold");
        // The sign matches num*den's sign (den's sign folds into num's after
        // normalization), so positivity iff num and den share a sign and num != 0.
        if !num.is_zero() {
            let same_sign = num.sign() == den.sign();
            prop_assert_eq!(r.is_positive(), same_sign, "positive iff num,den same sign");
            prop_assert_eq!(r.is_negative(), !same_sign, "negative iff num,den differ in sign");
        }
    }
}
