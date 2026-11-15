// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `natVal` literals: decimal text to a kernel `BigNat`, sub-quadratically.
//!
//! The digit-by-digit fold (`BigNat::from_radix_str`, or Lean's
//! `String.toNat?`) multiplies an ever-longer accumulator once per digit, so a
//! literal of n digits costs O(n^2) word operations: tens of hours for the
//! 25-million-digit literal the plan's exit arm (e) names. Here the digits are
//! split in halves, each half converted recursively, and the halves joined as
//! `hi * 10^k + lo`, with the powers `10^(B * 2^j)` computed once by
//! squaring. With num-bigint's Karatsuba/Toom-3 products the cost is
//! O(M(n) log n).
//!
//! A literal longer than [`MAX_NAT_LITERAL_DIGITS`] is not converted: the
//! reader declines the export (exit 2, `NatLiteralBudget`).

use clean_kernel::expr::BigNat;
use num_bigint::BigUint;

/// The digit budget of one `natVal` literal: twice the 25-million-digit
/// literal arm (e) must parse. Above it the export is declined, never
/// truncated.
pub const MAX_NAT_LITERAL_DIGITS: usize = 50_000_000;

/// Below this many digits the schoolbook conversion is cheaper than splitting.
const BASE_DIGITS: usize = 1_024;

/// Why a `natVal` text was not converted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NatTextError {
    /// Empty, or a byte that is not an ASCII decimal digit.
    Malformed,
    /// Longer than [`MAX_NAT_LITERAL_DIGITS`].
    OverBudget {
        /// The text's length.
        digits: usize,
    },
}

/// Convert a decimal literal. Leading zeros are accepted (`String.toNat?`
/// accepts them, and they do not change the value).
pub(crate) fn parse_nat_literal(text: &str) -> Result<BigNat, NatTextError> {
    let bytes = text.as_bytes();
    if bytes.is_empty() || !bytes.iter().all(u8::is_ascii_digit) {
        return Err(NatTextError::Malformed);
    }
    if bytes.len() > MAX_NAT_LITERAL_DIGITS {
        return Err(NatTextError::OverBudget {
            digits: bytes.len(),
        });
    }
    if bytes.len() <= 19 {
        let mut value = 0u64;
        for &b in bytes {
            value = value * 10 + u64::from(b - b'0');
        }
        return Ok(BigNat::from_u64(value));
    }
    // `powers[j] = 10^(BASE_DIGITS * 2^j)`, for every split the recursion makes.
    let mut powers = vec![BigUint::from(10u32).pow(BASE_DIGITS as u32)];
    while BASE_DIGITS << powers.len() < bytes.len() {
        let last = &powers[powers.len() - 1];
        let next = last * last;
        powers.push(next);
    }
    let value = convert(bytes, &powers);
    Ok(BigNat::from_limbs(value.to_u64_digits()))
}

/// `bytes` (ASCII digits) as a number: split off the low `BASE_DIGITS * 2^j`
/// digits for the largest such count below the length.
fn convert(bytes: &[u8], powers: &[BigUint]) -> BigUint {
    if bytes.len() <= BASE_DIGITS {
        return schoolbook(bytes);
    }
    let mut j = 0usize;
    while j + 1 < powers.len() && BASE_DIGITS << (j + 1) < bytes.len() {
        j += 1;
    }
    let low_len = BASE_DIGITS << j;
    let (high, low) = bytes.split_at(bytes.len() - low_len);
    convert(high, powers) * &powers[j] + convert(low, powers)
}

/// The digit-by-digit conversion, in chunks of 19 digits (every chunk fits a
/// `u64`).
fn schoolbook(bytes: &[u8]) -> BigUint {
    let mut acc = BigUint::from(0u32);
    for chunk in bytes.chunks(19) {
        let mut word = 0u64;
        for &b in chunk {
            word = word * 10 + u64::from(b - b'0');
        }
        let scale = 10u64.pow(chunk.len() as u32);
        acc = acc * scale + word;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decimal(n: &BigNat) -> String {
        let limbs = n.limbs();
        let mut words: Vec<u32> = Vec::with_capacity(limbs.len() * 2);
        for &l in limbs {
            words.push(l as u32);
            words.push((l >> 32) as u32);
        }
        BigUint::new(words).to_str_radix(10)
    }

    #[test]
    fn test_parse_nat_literal_small_and_u64_boundary() {
        assert_eq!(parse_nat_literal("0"), Ok(BigNat::from_u64(0)));
        assert_eq!(parse_nat_literal("007"), Ok(BigNat::from_u64(7)));
        assert_eq!(
            parse_nat_literal("18446744073709551615"),
            Ok(BigNat::from_u64(u64::MAX))
        );
        let over = parse_nat_literal("18446744073709551616").expect("2^64 parses");
        assert_eq!(over.limbs(), &[0, 1]);
    }

    #[test]
    fn test_parse_nat_literal_split_path_round_trips() {
        // Long enough to take three levels of the split.
        let text: String = (0..5_000)
            .map(|i| char::from(b'0' + ((i * 7 + 3) % 10) as u8))
            .collect();
        let text = format!("9{text}");
        let parsed = parse_nat_literal(&text).expect("digits parse");
        assert_eq!(decimal(&parsed), text);
    }

    #[test]
    fn test_parse_nat_literal_refuses_non_digits_and_empty() {
        assert_eq!(parse_nat_literal(""), Err(NatTextError::Malformed));
        assert_eq!(parse_nat_literal("12a"), Err(NatTextError::Malformed));
        assert_eq!(parse_nat_literal("-1"), Err(NatTextError::Malformed));
        assert_eq!(parse_nat_literal("1_000"), Err(NatTextError::Malformed));
    }

    #[test]
    fn test_parse_nat_literal_over_budget_is_not_converted() {
        let text = "1".repeat(MAX_NAT_LITERAL_DIGITS + 1);
        assert_eq!(
            parse_nat_literal(&text),
            Err(NatTextError::OverBudget {
                digits: MAX_NAT_LITERAL_DIGITS + 1
            })
        );
    }
}
