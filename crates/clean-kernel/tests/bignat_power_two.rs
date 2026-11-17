// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent arithmetic-oracle controls for the existing Nat primitive.
//! These tests are not a proof of the kernel or its compiled implementation.

use clean_kernel::BigNat;
use num_bigint::BigUint;

fn reference(value: &BigNat) -> BigUint {
    BigUint::new(
        value
            .limbs()
            .iter()
            .flat_map(|word| [*word as u32, (*word >> 32) as u32])
            .collect(),
    )
}

fn native(value: &BigUint) -> BigNat {
    BigNat::from_limbs(value.to_u64_digits())
}

fn compare(value: &BigNat, divisor: &BigNat) {
    let (n, d) = (reference(value), reference(divisor));
    let q = value.checked_div_big(divisor);
    let r = value.checked_mod_big(divisor);
    assert_eq!(
        q,
        native(&(&n / &d)),
        "quotient, input limbs={}, divisor={divisor:?}",
        value.limbs().len()
    );
    assert_eq!(
        r,
        native(&(&n % &d)),
        "remainder, input limbs={}, divisor={divisor:?}",
        value.limbs().len()
    );
    assert!(reference(&r) < d);
    assert_eq!(reference(&q) * d + reference(&r), n);
}

#[test]
fn every_single_limb_power_of_two_matches_independent_arithmetic() {
    let mut values = vec![
        BigNat::Small(0),
        BigNat::Small(1),
        BigNat::Small(u64::MAX),
        BigNat::from_limbs(vec![0, 1]),
        BigNat::from_limbs(vec![u64::MAX, u64::MAX]),
        BigNat::from_limbs(vec![0, 0, 1]),
    ];
    // Includes the limb scale of an ORIGINAL 16KiB Formula byte literal.
    // Deterministic mixed limbs exercise carries, zero words and high bits.
    for count in [3, 17, 255, 2060] {
        values.push(BigNat::from_limbs(
            (0..count)
                .map(|i| {
                    (i as u64)
                        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                        .rotate_left((i % 64) as u32)
                        ^ 0xa5a5_0000_ffff_5a5a
                })
                .collect(),
        ));
    }
    for shift in 0..64 {
        let divisor = BigNat::Small(1u64 << shift);
        for value in &values {
            compare(value, &divisor);
        }
    }
}

#[test]
fn zero_and_fallback_divisors_keep_their_existing_meaning() {
    for value in [
        BigNat::Small(0),
        BigNat::Small(42),
        BigNat::from_limbs(vec![0, u64::MAX, 7]),
    ] {
        assert_eq!(value.checked_div_big(&BigNat::Small(0)), BigNat::Small(0));
        assert_eq!(value.checked_mod_big(&BigNat::Small(0)), value);
        for divisor in [
            BigNat::Small(3),
            BigNat::Small(7),
            BigNat::Small((1u64 << 63) + 1),
            BigNat::Small(u64::MAX),
            BigNat::from_limbs(vec![0, 1]),
            BigNat::from_limbs(vec![1, 1]),
        ] {
            compare(&value, &divisor);
        }
    }
}
