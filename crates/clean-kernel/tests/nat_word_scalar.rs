// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary source-behavior checks for the factored word leaves.
//! These establish no Rust proof or compiler-bound byte alignment.

use clean_kernel::expr::{nat_word_div, nat_word_mod};
use clean_kernel::BigNat;
use num_bigint::BigUint;

#[test]
fn scalar_literals_keep_division_and_remainder_distinct() {
    for (a, b, quotient, remainder) in [
        (0, 1, 0, 0),
        (1, 1, 1, 0),
        (5, 2, 2, 1),
        (7, 2, 3, 1),
        (u64::MAX, 1, u64::MAX, 0),
        (u64::MAX, 2, 0x7fff_ffff_ffff_ffff, 1),
        (u64::MAX, u64::MAX, 1, 0),
        (u64::MAX, u64::MAX - 1, 1, 1),
        (u64::MAX - 1, u64::MAX, 0, u64::MAX - 1),
        (1 << 63, 3, 0x2aaa_aaaa_aaaa_aaaa, 2),
    ] {
        assert_eq!(nat_word_div(a, b), quotient, "division of {a} by {b}");
        assert_eq!(nat_word_mod(a, b), remainder, "remainder of {a} by {b}");
    }
}

#[test]
fn scalar_boundaries_and_production_wrappers_match_independent_biguint() {
    let numerators = [
        0,
        1,
        2,
        3,
        5,
        7,
        1 << 31,
        (1 << 32) - 1,
        1 << 32,
        (1 << 63) - 1,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    let divisors = [
        1,
        2,
        3,
        7,
        1 << 31,
        1 << 32,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ];
    for a in numerators {
        for b in divisors {
            let n = BigUint::from(a);
            let d = BigUint::from(b);
            let quotient = &n / &d;
            let remainder = &n % &d;
            let q = nat_word_div(a, b);
            let r = nat_word_mod(a, b);
            assert_eq!(BigUint::from(q), quotient, "division of {a} by {b}");
            assert_eq!(BigUint::from(r), remainder, "remainder of {a} by {b}");
            assert_eq!(BigUint::from(q) * &d + BigUint::from(r), n);
            assert!(BigUint::from(r) < d);
            let value = BigNat::Small(a);
            let divisor = BigNat::Small(b);
            assert_eq!(value.checked_div_big(&divisor), BigNat::Small(q));
            assert_eq!(value.checked_mod_big(&divisor), BigNat::Small(r));
        }
    }
}

#[test]
fn production_zero_wrappers_keep_nat_results() {
    for value in [
        BigNat::Small(0),
        BigNat::Small(5),
        BigNat::Small(u64::MAX),
        BigNat::from_limbs(vec![0, 1]),
        BigNat::from_limbs(vec![u64::MAX, 7]),
    ] {
        for zero in [
            BigNat::Small(0),
            BigNat::Big(vec![]),
            BigNat::Big(vec![0, 0]),
        ] {
            assert_eq!(value.checked_div_big(&zero), BigNat::Small(0));
            assert_eq!(value.checked_mod_big(&zero), value);
        }
    }
}
