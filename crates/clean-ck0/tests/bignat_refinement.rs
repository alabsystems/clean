// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! BigNat fast-path refinement: every op must agree with the pure `BigUint`
//! semantics (design §4.3 Incident #2 / §11-R5). The fast side starts from
//! `u64` operands (exercising the small-value optimisation); the pure side is
//! computed directly on `BigUint` and wrapped via `from_biguint` (never touching
//! the fast path). For large operands we scale up so the fast path's overflow
//! fallback is exercised too.

use clean_ck0::BigNat;
use num_bigint::BigUint;
use num_traits::Zero;
use proptest::prelude::*;

fn big_u() -> impl Strategy<Value = BigUint> {
    // Mix of small (fits u64) and large (forces the exact path / fast-path
    // overflow fallback) values.
    prop_oneof![
        any::<u64>().prop_map(BigUint::from),
        (any::<u64>(), any::<u64>())
            .prop_map(|(hi, lo)| (BigUint::from(hi) << 64u32) + BigUint::from(lo)),
    ]
}

proptest! {
    #[test]
    fn refine_add(a in big_u(), b in big_u()) {
        let fast = BigNat::from_biguint(a.clone()).add(&BigNat::from_biguint(b.clone()));
        let pure = BigNat::from_biguint(a + b);
        prop_assert_eq!(fast, pure);
    }

    #[test]
    fn refine_mul(a in big_u(), b in big_u()) {
        let fast = BigNat::from_biguint(a.clone()).mul(&BigNat::from_biguint(b.clone()));
        let pure = BigNat::from_biguint(a * b);
        prop_assert_eq!(fast, pure);
    }

    #[test]
    fn refine_sub(a in big_u(), b in big_u()) {
        // Truncated (Nat) subtraction.
        let pure_val = if a >= b { &a - &b } else { BigUint::zero() };
        let fast = BigNat::from_biguint(a).sub(&BigNat::from_biguint(b));
        prop_assert_eq!(fast, BigNat::from_biguint(pure_val));
    }

    #[test]
    fn refine_div(a in big_u(), b in big_u()) {
        // Lean Nat.div: n / 0 = 0.
        let pure_val = if b.is_zero() { BigUint::zero() } else { &a / &b };
        let fast = BigNat::from_biguint(a).div(&BigNat::from_biguint(b));
        prop_assert_eq!(fast, BigNat::from_biguint(pure_val));
    }

    #[test]
    fn refine_mod(a in big_u(), b in big_u()) {
        // Lean Nat.mod: n % 0 = n.
        let pure_val = if b.is_zero() { a.clone() } else { &a % &b };
        let fast = BigNat::from_biguint(a).rem(&BigNat::from_biguint(b));
        prop_assert_eq!(fast, BigNat::from_biguint(pure_val));
    }

    #[test]
    fn refine_dec_eq(a in big_u(), b in big_u()) {
        let fast = BigNat::from_biguint(a.clone()).dec_eq(&BigNat::from_biguint(b.clone()));
        prop_assert_eq!(fast, a == b);
    }

    #[test]
    fn refine_dec_le(a in big_u(), b in big_u()) {
        let fast = BigNat::from_biguint(a.clone()).dec_le(&BigNat::from_biguint(b.clone()));
        prop_assert_eq!(fast, a <= b);
    }

    #[test]
    fn refine_pow(a in any::<u32>(), e in 0u32..12) {
        let fast = BigNat::from_u64(u64::from(a)).pow(&BigNat::from_u64(u64::from(e)));
        let pure = BigNat::from_biguint(BigUint::from(a).pow(e));
        prop_assert_eq!(fast, pure);
    }
}
