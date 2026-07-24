// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended BigNat arithmetic operations: div, mod, pow, bitwise, shift.
//!
//! Part of #3248: Enables native reducers to operate on Nat values exceeding u64.
//! All operations are bounded to prevent unbounded allocation (max 1024 bits / 16 limbs).

use super::types::BigNat;

/// Compute the bit length of a BigNat (position of highest set bit + 1).
fn bignat_bit_length(n: &BigNat) -> usize {
    let limbs = n.limbs();
    for i in (0..limbs.len()).rev() {
        if limbs[i] != 0 {
            return i * 64 + (64 - limbs[i].leading_zeros() as usize);
        }
    }
    0
}

impl BigNat {
    /// Multi-limb division: self / other.
    ///
    /// Returns `(quotient, remainder)`. Returns `None` if other is zero.
    /// Uses shift-subtract long division on 64-bit limbs.
    pub fn checked_div_rem_big(&self, other: &BigNat) -> Option<(BigNat, BigNat)> {
        if other.is_zero() {
            return None;
        }
        // Fast path: both fit in u64
        if let (BigNat::Small(a), BigNat::Small(b)) = (self, other) {
            return Some((BigNat::Small(a / b), BigNat::Small(a % b)));
        }
        // If dividend < divisor, quotient is 0, remainder is dividend
        if self < other {
            return Some((BigNat::Small(0), self.clone()));
        }
        // Use shift-subtract long division
        let mut remainder = self.clone();
        let mut quotient_limbs = vec![0u64; self.limbs().len()];

        // Find the highest bit of the divisor
        let divisor_bits = bignat_bit_length(other);
        let dividend_bits = bignat_bit_length(&remainder);

        // Process from highest bit down
        let mut shift = dividend_bits.saturating_sub(divisor_bits);
        loop {
            let shifted_divisor = other.checked_shl_big(shift);
            if remainder >= shifted_divisor {
                remainder = remainder.saturating_sub_big(&shifted_divisor);
                // Set the bit in quotient
                let limb_idx = shift / 64;
                let bit_idx = shift % 64;
                if limb_idx < quotient_limbs.len() {
                    quotient_limbs[limb_idx] |= 1u64 << bit_idx;
                }
            }
            if shift == 0 {
                break;
            }
            shift -= 1;
        }

        Some((BigNat::from_limbs(quotient_limbs), remainder))
    }

    /// Multi-limb division: self / other.
    ///
    /// Returns 0 when other is zero (Lean 4 semantics).
    pub fn checked_div_big(&self, other: &BigNat) -> BigNat {
        match self.checked_div_rem_big(other) {
            Some((q, _)) => q,
            None => BigNat::Small(0), // div by zero => 0
        }
    }

    /// Multi-limb modulo: self % other.
    ///
    /// Returns self when other is zero (Lean 4 semantics).
    pub fn checked_mod_big(&self, other: &BigNat) -> BigNat {
        match self.checked_div_rem_big(other) {
            Some((_, r)) => r,
            None => self.clone(), // mod by zero => self
        }
    }

    /// Bitwise AND of two BigNats.
    pub fn bitand_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let min_len = a.len().min(b.len());
        let mut result = Vec::with_capacity(min_len);
        for i in 0..min_len {
            result.push(a[i] & b[i]);
        }
        // Higher limbs ANDed with implicit zeros are zero
        BigNat::from_limbs(result)
    }

    /// Bitwise OR of two BigNats.
    pub fn bitor_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = a.len().max(b.len());
        let mut result = Vec::with_capacity(max_len);
        for i in 0..max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            result.push(av | bv);
        }
        BigNat::from_limbs(result)
    }

    /// Bitwise XOR of two BigNats.
    pub fn bitxor_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = a.len().max(b.len());
        let mut result = Vec::with_capacity(max_len);
        for i in 0..max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            result.push(av ^ bv);
        }
        BigNat::from_limbs(result)
    }

    /// Left shift by `shift` bits.
    pub fn checked_shl_big(&self, shift: usize) -> BigNat {
        if self.is_zero() {
            return BigNat::Small(0);
        }
        let limb_shift = shift / 64;
        let bit_shift = shift % 64;
        let a = self.limbs();
        let new_len = a.len() + limb_shift + 1;
        let mut result = vec![0u64; new_len];
        let mut carry = 0u64;
        for i in 0..a.len() {
            if bit_shift == 0 {
                result[i + limb_shift] = a[i];
            } else {
                result[i + limb_shift] |= (a[i] << bit_shift) | carry;
                carry = a[i] >> (64 - bit_shift);
            }
        }
        if carry > 0 {
            result[a.len() + limb_shift] = carry;
        }
        BigNat::from_limbs(result)
    }

    /// Right shift by `shift` bits.
    pub fn shr_big(&self, shift: usize) -> BigNat {
        let limb_shift = shift / 64;
        let bit_shift = shift % 64;
        let a = self.limbs();
        if limb_shift >= a.len() {
            return BigNat::Small(0);
        }
        let new_len = a.len() - limb_shift;
        let mut result = Vec::with_capacity(new_len);
        for i in 0..new_len {
            let src_idx = i + limb_shift;
            if bit_shift == 0 {
                result.push(a[src_idx]);
            } else {
                let lo = a[src_idx] >> bit_shift;
                let hi = if src_idx + 1 < a.len() {
                    a[src_idx + 1] << (64 - bit_shift)
                } else {
                    0
                };
                result.push(lo | hi);
            }
        }
        BigNat::from_limbs(result)
    }

    /// Euclidean GCD of two BigNats: gcd(self, other).
    ///
    /// Uses the standard Euclidean algorithm via multi-limb modulo.
    /// gcd(0, b) = b, gcd(a, 0) = a, gcd(0, 0) = 0 — matching Lean's
    /// `Nat.gcd` (which terminates because the remainder strictly
    /// decreases). Never allocates beyond the inputs.
    pub fn gcd_big(&self, other: &BigNat) -> BigNat {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.checked_mod_big(&b);
            a = b;
            b = r;
        }
        a
    }

    /// Multi-limb exponentiation: self^exp.
    ///
    /// Returns None if the result would exceed 1024 bits (16 limbs)
    /// to bound allocation. Also returns None for large exponents
    /// to prevent excessive computation.
    pub fn checked_pow_big(&self, exp: &BigNat) -> Option<BigNat> {
        // 0^0 = 1, x^0 = 1
        if exp.is_zero() {
            return Some(BigNat::Small(1));
        }
        // 0^n = 0 for n > 0
        if self.is_zero() {
            return Some(BigNat::Small(0));
        }
        // 1^n = 1
        if *self == BigNat::Small(1) {
            return Some(BigNat::Small(1));
        }
        // Cap exponent at u32::MAX to prevent infinite loops
        let exp_u64 = exp.to_u64()?;
        let exp_u32 = u32::try_from(exp_u64).ok()?;
        // For base > 1, exp > 1023 guarantees >1024 bits
        if exp_u32 > 1023 {
            return None;
        }
        // Binary exponentiation
        let mut result = BigNat::Small(1);
        let mut base = self.clone();
        let mut e = exp_u32;
        while e > 0 {
            if e & 1 == 1 {
                result = result.checked_mul_big(&base)?;
            }
            e >>= 1;
            if e > 0 {
                base = base.checked_mul_big(&base)?;
            }
        }
        Some(result)
    }
}
