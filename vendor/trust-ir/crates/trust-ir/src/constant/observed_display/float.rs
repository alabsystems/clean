// Copyright 2026 Andrew Yates; numeric algorithm derived from Rust project contributors.
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Finite observed binary64 Debug spelling; no opaque float formatter is called.
//!
//! Dragon shortest mode follows Burger and Dybvig, PLDI 1996, Figure 3:
//! https://www.burgerrg.com/FP-Printing-PLDI96.pdf
//! The exact reference is Trust 6986546e's core flt2dec decoder/estimator/Dragon
//! fallback and fmt/float.rs Debug layout. See docs/observed-f64-format.md.
use super::*;
use core::cmp::Ordering;
mod big;
mod dragon;
#[cfg(test)]
mod tests;
pub(super) fn write<O: ExecutionObserver>(
    value: f64,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(12, size_of::<u64>() + size_of::<f64>())?;
    let bits = value.to_bits();
    let negative = bits >> 63 != 0;
    let exponent = (bits >> 52) & 0x7ff;
    let fraction = bits & ((1u64 << 52) - 1);
    if exponent == 0x7ff && fraction != 0 {
        return work.text("NaN", out);
    }
    if negative {
        work.text("-", out)?;
    }
    if exponent == 0x7ff {
        return work.text("inf", out);
    }
    if exponent == 0 && fraction == 0 {
        return work.text("0.0", out);
    }
    let digits = dragon::shortest(bits, work)?;
    work.admit(digits.len, size_of::<&str>())?;
    let text = core::str::from_utf8(&digits.bytes[..digits.len])
        .map_err(|_| ObservedValueError::InvalidRange)?;
    // The exact ordinary f64 Debug magnitude policy, independent of rounded k.
    work.admit(4, size_of::<bool>() + size_of::<f64>())?;
    let magnitude = f64::from_bits(bits & !(1u64 << 63));
    if magnitude < 1e-4 || magnitude >= 1e16 {
        work.text(&text[..1], out)?;
        if text.len() > 1 {
            work.text(".", out)?;
            work.text(&text[1..], out)?;
        }
        work.text("e", out)?;
        work.signed(i128::from(digits.exp) - 1, out)
    } else {
        decimal(text, digits.exp, out, work)
    }
}
fn decimal<O: ExecutionObserver>(
    text: &str,
    exp: i16,
    out: &mut String,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(3, size_of::<usize>())?;
    if exp <= 0 {
        work.text("0.", out)?;
        for _ in 0..exp.unsigned_abs() {
            work.admit(1, 0)?;
            work.text("0", out)?;
        }
        work.text(text, out)
    } else {
        let exp = exp as usize;
        if exp < text.len() {
            work.text(&text[..exp], out)?;
            work.text(".", out)?;
            work.text(&text[exp..], out)
        } else {
            work.text(text, out)?;
            for _ in text.len()..exp {
                work.admit(1, 0)?;
                work.text("0", out)?;
            }
            work.text(".0", out)
        }
    }
}
