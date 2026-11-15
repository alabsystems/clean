// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonicalize decimal bit-vector literals at the trusted parsing boundary.
//!
//! The pinned Carcara parser checks `(_ bvN W)` by converting N to usize,
//! rejecting valid wide values. Rewrite this literal to exactly W binary bits,
//! reducing N modulo 2^W as SMT-LIB specifies. Both original premises and proof
//! terms undergo the same conversion; no premise or inference is introduced.
//! Comments, quoted symbols, and strings are opaque. Unsupported sizes and
//! malformed decimal literals fail closed before reaching upstream unwraps.

use super::VerifyError;
use num_bigint::BigUint;
use std::borrow::Cow;

const MAX_WIDTH: usize = 16_384;
const MAX_DIGITS: usize = 5_000;
const MAX_EXPANDED_BITS: usize = 4_000_000;

pub(super) fn normalize(input: &str) -> Result<Cow<'_, str>, VerifyError> {
    let mut cursor = 0;
    let mut copied = 0;
    let mut bits = 0usize;
    let mut output = String::new();
    while let Some((start, end)) = token(input, &mut cursor) {
        if &input[start..end] != "(" {
            continue;
        }
        let mut probe = cursor;
        if next(input, &mut probe) != Some("_") {
            continue;
        }
        let Some(value) = next(input, &mut probe).and_then(|s| s.strip_prefix("bv")) else {
            continue;
        };
        let width = next(input, &mut probe).ok_or_else(invalid)?;
        if !decimal(value)
            || value.len() > MAX_DIGITS
            || !decimal(width)
            || width.starts_with('0')
            || next(input, &mut probe) != Some(")")
        {
            return Err(invalid());
        }
        let width: usize = width.parse().map_err(|_| invalid())?;
        if width == 0 || width > MAX_WIDTH {
            return Err(invalid());
        }
        bits = bits.checked_add(width).ok_or_else(invalid)?;
        if bits > MAX_EXPANDED_BITS {
            return Err(invalid());
        }
        let value = BigUint::parse_bytes(value.as_bytes(), 10).ok_or_else(invalid)?;
        let binary = value.to_str_radix(2);
        let retained = &binary[binary.len().saturating_sub(width)..];
        output.push_str(&input[copied..start]);
        output.push_str("#b");
        for _ in retained.len()..width {
            output.push('0');
        }
        output.push_str(retained);
        copied = probe;
        cursor = probe;
    }
    if copied == 0 {
        return Ok(Cow::Borrowed(input));
    }
    output.push_str(&input[copied..]);
    Ok(Cow::Owned(output))
}

fn decimal(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn invalid() -> VerifyError {
    VerifyError::CarcaraError("invalid or over-budget decimal bit-vector literal".into())
}

fn next<'a>(input: &'a str, cursor: &mut usize) -> Option<&'a str> {
    let (start, end) = token(input, cursor)?;
    Some(&input[start..end])
}

/// Return original byte spans, including quotes, so identifiers cannot be
/// mistaken for reserved words or constants. ASCII delimiters are UTF-8 bounds.
fn token(input: &str, cursor: &mut usize) -> Option<(usize, usize)> {
    let bytes = input.as_bytes();
    // The same lexicon as the vendored Carcara lexer (fix 40 in
    // third-party/carcara/DOWNSTREAM.md): whitespace is space, tab, LF and CR,
    // and a comment ends at LF or CR. A pre-pass that read a comment past a CR
    // would disagree with Carcara about where string literals begin, and
    // rewrite `(_ bvN W)` inside what Carcara reads as a string.
    loop {
        while bytes
            .get(*cursor)
            .is_some_and(|b| matches!(b, b' ' | b'\t' | b'\n' | b'\r'))
        {
            *cursor += 1;
        }
        if bytes.get(*cursor) != Some(&b';') {
            break;
        }
        while bytes
            .get(*cursor)
            .is_some_and(|b| !matches!(b, b'\n' | b'\r'))
        {
            *cursor += 1;
        }
    }
    let first = *bytes.get(*cursor)?;
    let start = *cursor;
    *cursor += 1;
    match first {
        b'(' | b')' => {}
        b'|' | b'"' => {
            while let Some(byte) = bytes.get(*cursor) {
                *cursor += 1;
                if *byte == first {
                    if first == b'"' && bytes.get(*cursor) == Some(&b'"') {
                        *cursor += 1;
                    } else {
                        break;
                    }
                }
            }
        }
        _ => {
            while bytes
                .get(*cursor)
                .is_some_and(|byte| !byte.is_ascii_whitespace() && !b"();\"|".contains(byte))
            {
                *cursor += 1;
            }
        }
    }
    Some((start, *cursor))
}

#[cfg(test)]
mod tests;
