// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational number type for external certificates — **arbitrary precision**.
//!
//! The shipping Clean verifier stores `ExternalRational` as an `i64`
//! numerator/denominator pair with `i128` intermediate arithmetic and explicit
//! overflow detection. That is sufficient for the small/decimal fixtures, but
//! certificates emitted for *real* benchmark deep networks (ACAS-Xu: 6 ReLU
//! hidden layers; CROWN multipliers whose reduced numerators reach ~18k bits)
//! carry rationals that do not fit `i64`/`i128`.
//!
//! This scratch verifier therefore backs `ExternalRational` by
//! [`num_rational::BigRational`]. The verification logic in `verify.rs` is kept
//! **byte-for-byte identical**; only this type changes. To preserve the `Copy`
//! API that `verify.rs` relies on (`*coeff`, `*multiplier`, `self.constant`),
//! `ExternalRational` is a `Copy` **handle** into a thread-local interning arena
//! of canonicalised `BigRational` values. Interning deduplicates equal values so
//! handle equality coincides with value equality (`PartialEq`/`Eq`/`Hash` derive
//! correctly). All arithmetic is exact bignum; the `i64` overflow path is gone,
//! so `add`/`sub`/`mul` never fail and `parse_rational_str` accepts arbitrarily
//! large `"n/d"` numerators and denominators.

use super::error::ExternalCertError;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use serde::de::Error as _;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::fmt;
use std::ops::Neg;
use std::sync::{LazyLock, RwLock};

// ---------------------------------------------------------------------------
// Interning arena. Slot 0 = 0/1, slot 1 = 1/1 (so ZERO/ONE are const handles).
//
// The arena is a **process-global** `LazyLock<RwLock<Arena>>` rather than a
// `thread_local!`. `ExternalRational` is a `Copy` u32 handle, and certificate
// verification interns rationals at deserialize time on one thread but uses
// them on rayon worker threads in the batch path (see
// `clean-server::handlers::external_cert`). A thread-local arena makes a handle
// minted on the deserialize thread index out of bounds on a worker thread. A
// shared arena keeps every handle valid on any thread.
//
// Trade-offs vs. the thread-local design: each `intern`/`with_val` takes a
// read/write lock (reads are cheap shared locks; interning takes the write
// lock). The arena also accumulates for the lifetime of the process and is
// never cleared — acceptable for certificate verification, which is bounded
// per request, but it is a deliberate, unbounded-over-process-lifetime store.
// ---------------------------------------------------------------------------
struct Arena {
    values: Vec<BigRational>,
    dedup: HashMap<BigRational, u32>,
}

static ARENA: LazyLock<RwLock<Arena>> = LazyLock::new(|| {
    let zero = BigRational::zero();
    let one = BigRational::one();
    let mut dedup = HashMap::new();
    dedup.insert(zero.clone(), 0u32);
    dedup.insert(one.clone(), 1u32);
    RwLock::new(Arena {
        values: vec![zero, one],
        dedup,
    })
});

fn intern(v: BigRational) -> u32 {
    {
        // Fast path: value already interned — only needs a shared read lock.
        let a = ARENA.read().expect("rational arena lock poisoned");
        if let Some(&id) = a.dedup.get(&v) {
            return id;
        }
    }
    let mut a = ARENA.write().expect("rational arena lock poisoned");
    // Re-check under the write lock: another thread may have interned `v`
    // between dropping the read lock and acquiring the write lock.
    if let Some(&id) = a.dedup.get(&v) {
        return id;
    }
    let id = u32::try_from(a.values.len()).expect("rational arena exhausted");
    a.dedup.insert(v.clone(), id);
    a.values.push(v);
    id
}

fn with_val<R>(id: u32, f: impl FnOnce(&BigRational) -> R) -> R {
    let a = ARENA.read().expect("rational arena lock poisoned");
    f(&a.values[id as usize])
}

fn val(id: u32) -> BigRational {
    with_val(id, Clone::clone)
}

/// Rational number used in external certificates (arbitrary precision, stored as
/// a `Copy` handle into a thread-local interning arena).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternalRational {
    id: u32,
}

impl ExternalRational {
    pub const ZERO: ExternalRational = ExternalRational { id: 0 };
    pub const ONE: ExternalRational = ExternalRational { id: 1 };

    pub fn new(num: i64, den: i64) -> Result<Self, ExternalCertError> {
        if den == 0 {
            return Err(ExternalCertError::invalid_schema(
                "rational denominator cannot be zero".to_string(),
            ));
        }
        let r = BigRational::new(BigInt::from(num), BigInt::from(den));
        Ok(ExternalRational { id: intern(r) })
    }

    fn from_big(r: BigRational) -> Self {
        ExternalRational { id: intern(r) }
    }

    fn new_big(num: BigInt, den: BigInt) -> Result<Self, ExternalCertError> {
        if den.is_zero() {
            return Err(ExternalCertError::invalid_schema(
                "rational denominator cannot be zero".to_string(),
            ));
        }
        Ok(Self::from_big(BigRational::new(num, den)))
    }

    pub fn from_int(n: i64) -> Self {
        Self::from_big(BigRational::from_integer(BigInt::from(n)))
    }

    pub fn is_zero(self) -> bool {
        self.id == 0
    }

    pub fn is_positive(self) -> bool {
        with_val(self.id, BigRational::is_positive)
    }

    pub fn is_negative(self) -> bool {
        with_val(self.id, BigRational::is_negative)
    }

    /// Exact arbitrary-precision addition (infallible; `Result` kept for API).
    #[allow(clippy::should_implement_trait, clippy::unnecessary_wraps)]
    pub fn add(self, other: Self) -> Result<Self, ExternalCertError> {
        Ok(Self::from_big(val(self.id) + val(other.id)))
    }

    /// Exact arbitrary-precision subtraction (infallible; `Result` kept for API).
    #[allow(clippy::should_implement_trait, clippy::unnecessary_wraps)]
    pub fn sub(self, other: Self) -> Result<Self, ExternalCertError> {
        Ok(Self::from_big(val(self.id) - val(other.id)))
    }

    /// Exact arbitrary-precision multiplication (infallible; `Result` kept for API).
    #[allow(clippy::should_implement_trait, clippy::unnecessary_wraps)]
    pub fn mul(self, other: Self) -> Result<Self, ExternalCertError> {
        Ok(Self::from_big(val(self.id) * val(other.id)))
    }

    pub fn to_compact_string(self) -> String {
        with_val(self.id, |r| {
            if r.denom().is_one() {
                r.numer().to_string()
            } else {
                format!("{}/{}", r.numer(), r.denom())
            }
        })
    }
}

impl Neg for ExternalRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::from_big(-val(self.id))
    }
}

impl fmt::Display for ExternalRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_compact_string())
    }
}

impl PartialOrd for ExternalRational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ExternalRational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.id == other.id {
            return std::cmp::Ordering::Equal;
        }
        let a = ARENA.read().expect("rational arena lock poisoned");
        a.values[self.id as usize].cmp(&a.values[other.id as usize])
    }
}

impl Serialize for ExternalRational {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Emit the canonical full-precision string form ("n" or "n/d"), which
        // round-trips through this type's Deserialize. (The previous i64 num/den
        // object form cannot represent bignum certificates.)
        serializer.serialize_str(&self.to_compact_string())
    }
}

impl<'de> Deserialize<'de> for ExternalRational {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = serde_json::Value::deserialize(deserializer)?;
        match value {
            serde_json::Value::String(s) => parse_rational_str(&s).map_err(D::Error::custom),
            serde_json::Value::Number(n) => {
                // JSON numbers are bounded; accept i64-range integers as before.
                n.as_i64()
                    .map(ExternalRational::from_int)
                    .ok_or_else(|| D::Error::custom("rational number out of range"))
            }
            serde_json::Value::Object(mut obj) => {
                if let Some(serde_json::Value::String(kind)) = obj.get("type") {
                    if kind != "rational" {
                        return Err(D::Error::custom("invalid rational type"));
                    }
                }
                if let Some(serde_json::Value::String(value)) = obj.remove("value") {
                    return parse_rational_str(&value).map_err(D::Error::custom);
                }
                // num/den may be arbitrarily large strings (or i64-range numbers).
                let num = match obj.remove("num") {
                    Some(serde_json::Value::Number(n)) => {
                        Some(BigInt::from(n.as_i64().ok_or_else(|| {
                            D::Error::custom("rational num out of range")
                        })?))
                    }
                    Some(serde_json::Value::String(s)) => s.parse::<BigInt>().ok(),
                    Some(_) => None,
                    None => None,
                }
                .ok_or_else(|| D::Error::custom("rational num missing or invalid"))?;
                let den = match obj.remove("den") {
                    Some(serde_json::Value::Number(n)) => {
                        Some(BigInt::from(n.as_i64().ok_or_else(|| {
                            D::Error::custom("rational den out of range")
                        })?))
                    }
                    Some(serde_json::Value::String(s)) => s.parse::<BigInt>().ok(),
                    Some(_) => None,
                    None => None,
                }
                .ok_or_else(|| D::Error::custom("rational den missing or invalid"))?;
                ExternalRational::new_big(num, den).map_err(D::Error::custom)
            }
            _ => Err(D::Error::custom("invalid rational encoding")),
        }
    }
}

/// Test-only helper exposing the internal string-to-rational parser.
#[cfg(test)]
pub(super) fn parse_rational_str_for_test(s: &str) -> Result<ExternalRational, ExternalCertError> {
    parse_rational_str(s)
}

fn parse_rational_str(s: &str) -> Result<ExternalRational, ExternalCertError> {
    let trimmed = s.trim();
    if trimmed.is_empty() {
        return Err(ExternalCertError::invalid_schema(
            "rational string is empty".to_string(),
        ));
    }
    // Fraction form "num/den" — arbitrary precision.
    let parts: Vec<&str> = trimmed.split('/').collect();
    match parts.len() {
        1 => parse_integer_or_decimal(parts[0]),
        2 => {
            let num = parts[0].parse::<BigInt>().map_err(|_| {
                ExternalCertError::invalid_schema("invalid rational string".to_string())
            })?;
            let den = parts[1].parse::<BigInt>().map_err(|_| {
                ExternalCertError::invalid_schema("invalid rational string".to_string())
            })?;
            ExternalRational::new_big(num, den)
        }
        _ => Err(ExternalCertError::invalid_schema(
            "invalid rational string".to_string(),
        )),
    }
}

/// Parse an integer literal (`"42"`, `"-5"`) or a decimal literal (`"0.00001"`,
/// `"-2.979672194"`) into an `ExternalRational`. Rejects scientific notation.
/// Arbitrary precision: no fractional-digit cap and no i64 overflow.
fn parse_integer_or_decimal(s: &str) -> Result<ExternalRational, ExternalCertError> {
    if s.contains(['e', 'E']) {
        return Err(ExternalCertError::invalid_schema(
            "scientific notation not supported in rational strings; use decimal or N/D form"
                .to_string(),
        ));
    }
    if let Some((int_part, frac_part)) = s.split_once('.') {
        if frac_part.is_empty() {
            return Err(ExternalCertError::invalid_schema(
                "invalid rational string".to_string(),
            ));
        }
        if !frac_part.chars().all(|c| c.is_ascii_digit()) {
            return Err(ExternalCertError::invalid_schema(
                "invalid rational string".to_string(),
            ));
        }
        let (sign, int_digits): (i8, &str) = match int_part.as_bytes().first() {
            Some(b'-') => (-1, &int_part[1..]),
            Some(b'+') => (1, &int_part[1..]),
            _ => (1, int_part),
        };
        if !int_digits.is_empty() && !int_digits.chars().all(|c| c.is_ascii_digit()) {
            return Err(ExternalCertError::invalid_schema(
                "invalid rational string".to_string(),
            ));
        }
        let int_val: BigInt = if int_digits.is_empty() {
            BigInt::zero()
        } else {
            int_digits.parse::<BigInt>().map_err(|_| {
                ExternalCertError::invalid_schema("invalid rational string".to_string())
            })?
        };
        let frac_val: BigInt = frac_part.parse::<BigInt>().map_err(|_| {
            ExternalCertError::invalid_schema("invalid rational string".to_string())
        })?;
        let den: BigInt = BigInt::from(10).pow(frac_part.len() as u32);
        let num_mag = int_val * &den + frac_val;
        let signed_num = if sign < 0 { -num_mag } else { num_mag };
        ExternalRational::new_big(signed_num, den)
    } else {
        let num = s.parse::<BigInt>().map_err(|_| {
            ExternalCertError::invalid_schema("invalid rational string".to_string())
        })?;
        Ok(ExternalRational::from_big(BigRational::from_integer(num)))
    }
}

#[cfg(test)]
mod parse_tests {
    use super::*;

    #[test]
    fn test_parse_integer() {
        assert_eq!(parse_rational_str("0").unwrap(), ExternalRational::ZERO);
        assert_eq!(parse_rational_str("1").unwrap(), ExternalRational::ONE);
        assert_eq!(
            parse_rational_str("-42").unwrap(),
            ExternalRational::from_int(-42)
        );
    }

    #[test]
    fn test_parse_fraction() {
        assert_eq!(
            parse_rational_str("3/4").unwrap(),
            ExternalRational::new(3, 4).unwrap()
        );
        assert_eq!(
            parse_rational_str("-1/100000").unwrap(),
            ExternalRational::new(-1, 100000).unwrap()
        );
    }

    #[test]
    fn test_parse_decimal_basic() {
        assert_eq!(
            parse_rational_str("0.00001").unwrap(),
            ExternalRational::new(1, 100000).unwrap()
        );
        assert_eq!(
            parse_rational_str("0.0032").unwrap(),
            ExternalRational::new(32, 10000).unwrap()
        );
    }

    #[test]
    fn test_parse_decimal_negative() {
        assert_eq!(
            parse_rational_str("-0.00001").unwrap(),
            ExternalRational::new(-1, 100000).unwrap()
        );
        assert_eq!(
            parse_rational_str("-2.979672194").unwrap(),
            ExternalRational::new(-2_979_672_194, 1_000_000_000).unwrap()
        );
    }

    #[test]
    fn test_parse_decimal_no_integer_part() {
        assert_eq!(
            parse_rational_str(".5").unwrap(),
            ExternalRational::new(5, 10).unwrap()
        );
        assert_eq!(
            parse_rational_str("-.25").unwrap(),
            ExternalRational::new(-25, 100).unwrap()
        );
    }

    #[test]
    fn test_parse_decimal_rejects_scientific() {
        assert!(parse_rational_str("1e-5").is_err());
        assert!(parse_rational_str("1E5").is_err());
        assert!(parse_rational_str("1.5e2").is_err());
    }

    #[test]
    fn test_parse_decimal_rejects_malformed() {
        assert!(parse_rational_str("1.").is_err());
        assert!(parse_rational_str("1.2.3").is_err());
        assert!(parse_rational_str("abc").is_err());
        assert!(parse_rational_str("1.a").is_err());
    }

    #[test]
    fn test_parse_bignum_fraction_roundtrips() {
        // A 200-bit numerator that would overflow i64/i128 — must parse exactly.
        let big = BigInt::from(2u8).pow(200);
        let s = format!("{}/3", big);
        let r = parse_rational_str(&s).unwrap();
        assert_eq!(r.to_compact_string(), s);
    }
}
