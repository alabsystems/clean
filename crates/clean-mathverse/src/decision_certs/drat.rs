// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DRAT certificate parser (text and binary formats).
//!
//! DRAT (Deletion Resolution Asymmetric Tautology) is the standard proof
//! certificate format for SAT solvers. The text format has one clause per line,
//! terminated by `0`. Lines prefixed with `d` are deletion steps. The binary
//! format uses varint-encoded literals with `0` as clause separator.
//!
//! Reference: Wetzler, Heule, Hunt — "DRAT-trim: Efficient Checking and
//! Trimming Using Expressive Clausal Proofs" (SAT 2014).

use super::types::{CnfFormula, DratStep, DratStepKind, SatCertFormat, SatCertificate};
use crate::decision::CertError;

// ---------------------------------------------------------------------------
// Text DRAT parser
// ---------------------------------------------------------------------------

/// Parse a DRAT certificate in text format.
///
/// # Format
///
/// Each line is either:
/// - A clause: `lit1 lit2 ... 0` (addition step)
/// - A deletion: `d lit1 lit2 ... 0`
/// - A comment: `c ...` (ignored)
///
/// Lines are whitespace-trimmed. Empty lines are skipped.
///
/// # Errors
///
/// Returns [`CertError::Format`] if a line contains non-numeric tokens
/// (other than the `d` prefix and `c` comment prefix).
pub fn parse_drat_text(input: &str) -> Result<Vec<DratStep>, CertError> {
    let mut steps = Vec::new();

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let (kind, tokens_str) = if let Some(rest) = trimmed.strip_prefix('d') {
            (DratStepKind::Delete, rest)
        } else {
            (DratStepKind::Add, trimmed)
        };

        let literals: Vec<i32> = tokens_str
            .split_whitespace()
            .map(|tok| {
                tok.parse::<i32>().map_err(|_| CertError::Format {
                    message: format!("invalid literal in DRAT text: {tok:?}"),
                })
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .take_while(|&lit| lit != 0)
            .collect();

        steps.push(DratStep {
            kind,
            clause: literals,
        });
    }

    Ok(steps)
}

/// Parse a DRAT text certificate and build a full [`SatCertificate`].
///
/// The CNF formula is reconstructed from the proof steps: any clause that
/// appears as an addition before the first deletion is treated as an original
/// clause. This is a heuristic — for accurate original formulas, parse the
/// DIMACS CNF separately.
pub fn parse_drat_text_certificate(
    input: &str,
    formula: CnfFormula,
) -> Result<SatCertificate, CertError> {
    let steps = parse_drat_text(input)?;
    Ok(SatCertificate {
        formula,
        drat_steps: steps,
        lrat_steps: Vec::new(),
        format: SatCertFormat::DratText,
        verifier_tool: None,
    })
}

// ---------------------------------------------------------------------------
// Binary DRAT parser
// ---------------------------------------------------------------------------

/// Parse a DRAT certificate in binary format.
///
/// # Binary Format
///
/// Each step starts with a marker byte:
/// - `b'a'` (0x61): addition step
/// - `b'd'` (0x64): deletion step
///
/// Followed by varint-encoded literals. Each literal `l` is encoded as:
/// - `2 * var + (if positive { 0 } else { 1 })`
///   using unsigned varint encoding (7 bits per byte, MSB = continuation).
///
/// A literal value of `0` (encoded as varint 0) terminates the clause.
///
/// # Errors
///
/// Returns [`CertError::Format`] on:
/// - Unexpected marker byte
/// - Truncated varint
/// - Varint overflow
pub fn parse_drat_binary(input: &[u8]) -> Result<Vec<DratStep>, CertError> {
    let mut steps = Vec::new();
    let mut pos = 0;

    while pos < input.len() {
        let marker = input[pos];
        pos += 1;

        let kind = match marker {
            b'a' => DratStepKind::Add,
            b'd' => DratStepKind::Delete,
            _ => {
                return Err(CertError::Format {
                    message: format!(
                        "unexpected DRAT binary marker byte {marker:#04x} at offset {}",
                        pos - 1,
                    ),
                });
            }
        };

        let mut clause = Vec::new();
        loop {
            let (encoded, new_pos) = read_varint(input, pos)?;
            pos = new_pos;

            if encoded == 0 {
                break;
            }

            // Decode: variable = encoded / 2, sign = -(encoded & 1)
            let var = (encoded >> 1) as i32;
            let lit = if encoded & 1 == 1 { -var } else { var };
            clause.push(lit);
        }

        steps.push(DratStep { kind, clause });
    }

    Ok(steps)
}

/// Parse a binary DRAT certificate and build a full [`SatCertificate`].
pub fn parse_drat_binary_certificate(
    input: &[u8],
    formula: CnfFormula,
) -> Result<SatCertificate, CertError> {
    let steps = parse_drat_binary(input)?;
    Ok(SatCertificate {
        formula,
        drat_steps: steps,
        lrat_steps: Vec::new(),
        format: SatCertFormat::DratBinary,
        verifier_tool: None,
    })
}

// ---------------------------------------------------------------------------
// DIMACS CNF parser (minimal, for test support)
// ---------------------------------------------------------------------------

/// Parse a DIMACS CNF formula from text.
///
/// The `p cnf <vars> <clauses>` header line declares the problem dimensions.
/// Each subsequent non-comment line contains space-separated literals terminated
/// by `0`. This is a minimal parser for building [`CnfFormula`] values to pair
/// with DRAT/LRAT certificates.
pub fn parse_dimacs_cnf(input: &str) -> Result<CnfFormula, CertError> {
    let mut num_vars = 0u32;
    let mut clauses = Vec::new();
    let mut current_clause = Vec::new();

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if trimmed.starts_with("p ") {
            // p cnf <vars> <clauses>
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() >= 3 {
                num_vars = parts[2].parse::<u32>().unwrap_or(0);
            }
            continue;
        }

        for tok in trimmed.split_whitespace() {
            let lit = tok.parse::<i32>().map_err(|_| CertError::Format {
                message: format!("invalid literal in DIMACS: {tok:?}"),
            })?;
            if lit == 0 {
                if !current_clause.is_empty() {
                    clauses.push(std::mem::take(&mut current_clause));
                }
            } else {
                current_clause.push(lit);
            }
        }
    }

    // Handle unterminated final clause
    if !current_clause.is_empty() {
        clauses.push(current_clause);
    }

    // If no `p` line, compute num_vars from clauses
    if num_vars == 0 {
        num_vars = CnfFormula::compute_num_vars(&clauses);
    }

    Ok(CnfFormula::new(num_vars, clauses))
}

// ---------------------------------------------------------------------------
// Varint codec
// ---------------------------------------------------------------------------

/// Read an unsigned varint from the byte slice starting at `pos`.
///
/// Returns `(value, new_pos)`. Uses 7 bits per byte with MSB as continuation.
fn read_varint(data: &[u8], mut pos: usize) -> Result<(u64, usize), CertError> {
    let mut result: u64 = 0;
    let mut shift = 0u32;

    loop {
        if pos >= data.len() {
            return Err(CertError::Format {
                message: format!("truncated varint at offset {pos}"),
            });
        }

        let byte = data[pos];
        pos += 1;

        let value = u64::from(byte & 0x7F);
        result |= value.checked_shl(shift).ok_or_else(|| CertError::Format {
            message: format!("varint overflow at offset {}", pos - 1),
        })?;

        if byte & 0x80 == 0 {
            return Ok((result, pos));
        }

        shift += 7;
        if shift >= 64 {
            return Err(CertError::Format {
                message: format!("varint too large at offset {}", pos - 1),
            });
        }
    }
}

/// Encode a u64 value as a varint into a buffer.
fn encode_varint(mut value: u64, buf: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

/// Encode a literal into the binary DRAT format.
///
/// Positive literal `v` -> `2*v`, negative literal `-v` -> `2*v + 1`.
fn encode_lit(lit: i32) -> u64 {
    let var = lit.unsigned_abs() as u64;
    if lit >= 0 {
        var << 1
    } else {
        (var << 1) | 1
    }
}

/// Encode DRAT steps into binary format (for testing round-trips).
pub(crate) fn encode_drat_binary(steps: &[DratStep]) -> Vec<u8> {
    let mut buf = Vec::new();
    for step in steps {
        let marker = match step.kind {
            DratStepKind::Add => b'a',
            DratStepKind::Delete => b'd',
        };
        buf.push(marker);
        for &lit in &step.clause {
            encode_varint(encode_lit(lit), &mut buf);
        }
        // Terminating 0
        buf.push(0);
    }
    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_drat_text_basic() {
        let input = "1 2 0\n-1 3 0\nd 1 2 0\n";
        let steps = parse_drat_text(input).expect("should parse");
        assert_eq!(steps.len(), 3);

        assert_eq!(steps[0].kind, DratStepKind::Add);
        assert_eq!(steps[0].clause, vec![1, 2]);

        assert_eq!(steps[1].kind, DratStepKind::Add);
        assert_eq!(steps[1].clause, vec![-1, 3]);

        assert_eq!(steps[2].kind, DratStepKind::Delete);
        assert_eq!(steps[2].clause, vec![1, 2]);
    }

    #[test]
    fn test_parse_drat_text_with_comments() {
        let input = "c This is a comment\n1 -2 0\nc Another comment\nd 1 0\n";
        let steps = parse_drat_text(input).expect("should parse");
        assert_eq!(steps.len(), 2);
    }

    #[test]
    fn test_parse_drat_text_empty_lines() {
        let input = "\n\n1 2 0\n\n-3 0\n\n";
        let steps = parse_drat_text(input).expect("should parse");
        assert_eq!(steps.len(), 2);
    }

    #[test]
    fn test_parse_drat_text_invalid_literal() {
        let input = "1 abc 0\n";
        let result = parse_drat_text(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_drat_binary_basic() {
        // Build binary: add(1, 2), add(-1, 3), delete(1, 2)
        let steps = vec![
            DratStep::add(vec![1, 2]),
            DratStep::add(vec![-1, 3]),
            DratStep::delete(vec![1, 2]),
        ];
        let binary = encode_drat_binary(&steps);

        let parsed = parse_drat_binary(&binary).expect("should parse");
        assert_eq!(parsed.len(), 3);

        assert_eq!(parsed[0].kind, DratStepKind::Add);
        assert_eq!(parsed[0].clause, vec![1, 2]);

        assert_eq!(parsed[1].kind, DratStepKind::Add);
        assert_eq!(parsed[1].clause, vec![-1, 3]);

        assert_eq!(parsed[2].kind, DratStepKind::Delete);
        assert_eq!(parsed[2].clause, vec![1, 2]);
    }

    #[test]
    fn test_parse_drat_binary_empty() {
        let parsed = parse_drat_binary(&[]).expect("should parse empty");
        assert!(parsed.is_empty());
    }

    #[test]
    fn test_parse_drat_binary_invalid_marker() {
        let result = parse_drat_binary(&[0xFF, 0x00]);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_drat_binary_truncated_varint() {
        // Marker 'a' followed by a continuation byte with no terminator
        let result = parse_drat_binary(&[b'a', 0x80]);
        assert!(result.is_err());
    }

    #[test]
    fn test_varint_roundtrip() {
        for &value in &[0u64, 1, 127, 128, 16383, 16384, u64::MAX >> 1] {
            let mut buf = Vec::new();
            encode_varint(value, &mut buf);
            let (decoded, _) = read_varint(&buf, 0).expect("should decode");
            assert_eq!(decoded, value, "varint roundtrip failed for {value}");
        }
    }

    #[test]
    fn test_parse_dimacs_cnf_basic() {
        let input = "\
            c Example CNF\n\
            p cnf 3 2\n\
            1 -2 0\n\
            2 3 0\n\
        ";
        let formula = parse_dimacs_cnf(input).expect("should parse");
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.num_clauses(), 2);
        assert_eq!(formula.clauses[0], vec![1, -2]);
        assert_eq!(formula.clauses[1], vec![2, 3]);
    }

    #[test]
    fn test_parse_dimacs_cnf_no_header() {
        let input = "1 -3 0\n2 0\n";
        let formula = parse_dimacs_cnf(input).expect("should parse");
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.num_clauses(), 2);
    }

    #[test]
    fn test_drat_binary_roundtrip_large_var() {
        // Test with variable numbers that require multi-byte varints
        let steps = vec![DratStep::add(vec![1000, -2000, 32767])];
        let binary = encode_drat_binary(&steps);
        let parsed = parse_drat_binary(&binary).expect("should parse");
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].clause, vec![1000, -2000, 32767]);
    }

    #[test]
    fn test_parse_drat_text_certificate() {
        let formula = CnfFormula::new(3, vec![vec![1, 2, 3], vec![-1, -2]]);
        let drat = "1 0\nd 1 2 3 0\n";
        let cert = parse_drat_text_certificate(drat, formula).expect("should parse");
        assert_eq!(cert.format, SatCertFormat::DratText);
        assert_eq!(cert.drat_steps.len(), 2);
        assert_eq!(cert.formula.num_vars, 3);
        assert!(cert.lrat_steps.is_empty());
    }
}
