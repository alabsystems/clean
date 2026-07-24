// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arbitrary-precision natural numbers — the **only** numeric value type in the
//! seed, and the **only** module permitted fixed-width arithmetic / `as` casts.
//!
//! Soundness story (design §3.2, §4.3 Incident #2, §11-R5):
//!
//! * The pure semantics is the limb vector carried by [`num_bigint::BigUint`]
//!   (arbitrary precision; no overflow). All exported ops (`add/mul/sub/div/mod/
//!   dec_eq/dec_le/pow`) are *defined* by that pure path.
//! * A **small-value fast path** is permitted purely as a representation
//!   optimisation: when both operands fit in a `u64`, the op is done in `u64`
//!   with `checked_*` (so it can never wrap silently — on overflow we fall back
//!   to the pure `BigUint` path). Each such site is annotated `// AUDIT:`. A
//!   *semantic* shortcut is forbidden; the fast path must be observationally
//!   identical to the pure path, which the proptest
//!   `fast(a) ⊕ fast(b) == fast(a ⊕ b)` (`tests/bignat_refinement.rs`) checks.
//! * This is the one module where the crate-level `deny(clippy::cast_*)` and
//!   `deny(clippy::arithmetic_side_effects)` are locally relaxed at audited
//!   sites; everything is `checked_*`, so "arithmetic" here cannot produce a
//!   wrong value, only fall back to the exact path.

// AUDIT: this is the single module the seed's numeric policy designates for
// arithmetic (design §3.2 / policy.rs). The `+ - * / %` operators below act on
// `BigUint` (arbitrary precision — they cannot overflow), and every fixed-width
// (`u64`) op is `checked_*` with an exact `BigUint` fallback. The crate-level
// `deny(clippy::arithmetic_side_effects)` targets *fixed-width* overflow risk,
// which this module structurally does not have; we relax it here, module-wide,
// precisely because this is the audited exception. Each `u64` fast-path site
// additionally carries an inline `// AUDIT:` note.
#![allow(clippy::arithmetic_side_effects)]

use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::cmp::Ordering;

/// An arbitrary-precision natural number.
///
/// Field-private: the invariant is simply "holds a valid `BigUint`", but keeping
/// it private means the small-value fast path is an *implementation* detail that
/// callers cannot observe or corrupt.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BigNat(BigUint);

/// Errors from partial `BigNat` operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum BigNatError {
    /// Division or modulo by zero.
    #[error("bignat: division by zero")]
    DivByZero,
}

impl BigNat {
    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        BigNat(BigUint::zero())
    }

    /// One.
    #[must_use]
    pub fn one() -> Self {
        BigNat(BigUint::one())
    }

    /// Build from a `u64` literal.
    #[must_use]
    pub fn from_u64(n: u64) -> Self {
        BigNat(BigUint::from(n))
    }

    /// Build directly from an arbitrary-precision `BigUint` — the *pure*
    /// representation. Exposed so the refinement harness can construct the exact
    /// reference value independent of the small-value fast path.
    #[must_use]
    pub fn from_biguint(n: BigUint) -> Self {
        BigNat(n)
    }

    /// True iff zero.
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// The small-value fast-path witness: `Some(v)` iff this value fits in `u64`.
    ///
    /// Used internally by the fast paths and by the refinement test. Exposed so
    /// the refinement harness can drive `fast` directly.
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        // num-bigint provides a checked, no-`as` conversion. Policy-clean.
        u64::try_from(&self.0).ok()
    }

    /// `self + rhs`.
    #[must_use]
    pub fn add(&self, rhs: &BigNat) -> BigNat {
        if let (Some(a), Some(b)) = (self.as_u64(), rhs.as_u64()) {
            // AUDIT: small-value fast path. `checked_add` cannot wrap; on
            // overflow we fall through to the exact BigUint path. Refinement:
            // tests/bignat_refinement.rs asserts equality with the pure path.
            if let Some(s) = a.checked_add(b) {
                return BigNat::from_u64(s);
            }
        }
        BigNat(&self.0 + &rhs.0)
    }

    /// `self * rhs`.
    #[must_use]
    pub fn mul(&self, rhs: &BigNat) -> BigNat {
        if let (Some(a), Some(b)) = (self.as_u64(), rhs.as_u64()) {
            // AUDIT: small-value fast path; `checked_mul` falls back on overflow.
            if let Some(p) = a.checked_mul(b) {
                return BigNat::from_u64(p);
            }
        }
        BigNat(&self.0 * &rhs.0)
    }

    /// Truncated subtraction `self - rhs`, saturating at zero (Lean `Nat.sub`).
    #[must_use]
    pub fn sub(&self, rhs: &BigNat) -> BigNat {
        if self.0 <= rhs.0 {
            return BigNat::zero();
        }
        if let (Some(a), Some(b)) = (self.as_u64(), rhs.as_u64()) {
            // AUDIT: a > b is guaranteed here (a.0 > b.0 above), so
            // `checked_sub` is `Some`; kept `checked_*` to honour the
            // no-wrapping-arithmetic policy syntactically.
            if let Some(d) = a.checked_sub(b) {
                return BigNat::from_u64(d);
            }
        }
        BigNat(&self.0 - &rhs.0)
    }

    /// Truncated division `self / rhs` (Lean `Nat.div`: `n / 0 = 0`).
    #[must_use]
    pub fn div(&self, rhs: &BigNat) -> BigNat {
        if rhs.0.is_zero() {
            return BigNat::zero();
        }
        BigNat(&self.0 / &rhs.0)
    }

    /// Checked division; `Err(DivByZero)` instead of the Lean `n/0=0` convention.
    /// Provided for callers that want the partiality surfaced.
    pub fn checked_div(&self, rhs: &BigNat) -> Result<BigNat, BigNatError> {
        if rhs.0.is_zero() {
            return Err(BigNatError::DivByZero);
        }
        Ok(BigNat(&self.0 / &rhs.0))
    }

    /// Remainder `self % rhs` (Lean `Nat.mod`: `n % 0 = n`).
    #[must_use]
    pub fn rem(&self, rhs: &BigNat) -> BigNat {
        if rhs.0.is_zero() {
            return self.clone();
        }
        BigNat(&self.0 % &rhs.0)
    }

    /// Checked remainder; `Err(DivByZero)` instead of the Lean `n%0=n` convention.
    pub fn checked_rem(&self, rhs: &BigNat) -> Result<BigNat, BigNatError> {
        if rhs.0.is_zero() {
            return Err(BigNatError::DivByZero);
        }
        Ok(BigNat(&self.0 % &rhs.0))
    }

    /// Decidable equality.
    #[must_use]
    pub fn dec_eq(&self, rhs: &BigNat) -> bool {
        if let (Some(a), Some(b)) = (self.as_u64(), rhs.as_u64()) {
            // AUDIT: comparison only, no arithmetic; fast path is exact.
            return a == b;
        }
        self.0 == rhs.0
    }

    /// Decidable `self <= rhs`.
    #[must_use]
    pub fn dec_le(&self, rhs: &BigNat) -> bool {
        if let (Some(a), Some(b)) = (self.as_u64(), rhs.as_u64()) {
            // AUDIT: comparison only, no arithmetic; fast path is exact.
            return a <= b;
        }
        self.0 <= rhs.0
    }

    /// Total ordering (also available via the derived [`Ord`] impl).
    #[must_use]
    pub fn compare(&self, rhs: &BigNat) -> Ordering {
        self.0.cmp(&rhs.0)
    }

    /// `self ^ exp`.
    #[must_use]
    pub fn pow(&self, exp: &BigNat) -> BigNat {
        // num-bigint's `pow` takes a `u32` exponent; for arbitrary-precision
        // exponents we iterate by squaring over the exact path. Exponents that
        // large are not reachable in practice, but we stay total and exact.
        if let Ok(e) = u32::try_from(&exp.0) {
            return BigNat(self.0.pow(e));
        }
        // Fallback: square-and-multiply over BigUint (exact, no fixed width).
        let mut result = BigUint::one();
        let mut base = self.0.clone();
        let mut e = exp.0.clone();
        let two = BigUint::from(2u32);
        while !e.is_zero() {
            if (&e % &two).is_one() {
                result = &result * &base;
            }
            e /= &two;
            if !e.is_zero() {
                base = &base * &base;
            }
        }
        BigNat(result)
    }

    /// Borrow the underlying `BigUint` (read-only; the pure semantics).
    #[must_use]
    pub fn as_biguint(&self) -> &BigUint {
        &self.0
    }
}

impl std::fmt::Display for BigNat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_div_mod_conventions() {
        // Lean: n / 0 = 0, n % 0 = n.
        let n = BigNat::from_u64(7);
        assert_eq!(n.div(&BigNat::zero()), BigNat::zero());
        assert_eq!(n.rem(&BigNat::zero()), n);
        assert_eq!(n.checked_div(&BigNat::zero()), Err(BigNatError::DivByZero));
        assert_eq!(n.checked_rem(&BigNat::zero()), Err(BigNatError::DivByZero));
    }

    #[test]
    fn test_truncated_sub() {
        assert_eq!(
            BigNat::from_u64(3).sub(&BigNat::from_u64(5)),
            BigNat::zero()
        );
        assert_eq!(
            BigNat::from_u64(5).sub(&BigNat::from_u64(3)),
            BigNat::from_u64(2)
        );
    }

    #[test]
    fn test_overflow_fast_path_falls_back_exact() {
        // u64::MAX + 1 cannot use the u64 fast path; it must fall back exact.
        let big = BigNat::from_u64(u64::MAX).add(&BigNat::one());
        let pure = BigNat::from_biguint(BigUint::from(u64::MAX) + BigUint::one());
        assert_eq!(big, pure);
        assert!(big.as_u64().is_none(), "result exceeds u64");
    }

    #[test]
    fn test_compare_and_dec() {
        assert_eq!(
            BigNat::from_u64(1).compare(&BigNat::from_u64(2)),
            Ordering::Less
        );
        assert!(BigNat::from_u64(2).dec_le(&BigNat::from_u64(2)));
        assert!(BigNat::from_u64(2).dec_eq(&BigNat::from_u64(2)));
        assert!(!BigNat::from_u64(3).dec_le(&BigNat::from_u64(2)));
    }

    #[test]
    fn test_pow_basic() {
        assert_eq!(
            BigNat::from_u64(2).pow(&BigNat::from_u64(10)),
            BigNat::from_u64(1024)
        );
        assert_eq!(BigNat::from_u64(5).pow(&BigNat::zero()), BigNat::one());
    }
}

#[cfg(kani)]
mod kani_harnesses {
    //! Bounded refinement harnesses (design §8 tier 1). Compiled out of normal
    //! builds; `fast(a) ⊕ fast(b) == fast(a ⊕ b)` for each op. Skeletons only at
    //! M0; the full bignat Kani leg is fleshed out alongside M5.
    use super::*;

    #[kani::proof]
    fn refine_add() {
        let a: u64 = kani::any();
        let b: u64 = kani::any();
        let big = BigNat::from_u64(a).add(&BigNat::from_u64(b));
        let pure = BigNat(BigUint::from(a) + BigUint::from(b));
        assert!(big == pure);
    }

    #[kani::proof]
    fn refine_mul() {
        let a: u64 = kani::any();
        let b: u64 = kani::any();
        let big = BigNat::from_u64(a).mul(&BigNat::from_u64(b));
        let pure = BigNat(BigUint::from(a) * BigUint::from(b));
        assert!(big == pure);
    }
}
