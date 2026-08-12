// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Import and verify Ay DRAT proofs using the existing CDCL proof logger.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::fs;
use std::path::Path;

use thiserror::Error;

use super::cdcl::proof_logging::{
    verify_proof_log, ProofLog, ProofLogResult, ProofStep as LeanProofStep,
};
use super::cdcl::{Clause, Literal};
use super::types::Cnf;

/// Errors from importing or verifying a Ay DRAT proof.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum AyImportError {
    /// An I/O error occurred while reading the CNF or proof file.
    #[error("I/O error: {0}")]
    IoError(#[from] std::io::Error),

    /// The DRAT proof could not be parsed.
    #[error("DRAT parse error: {0}")]
    DratParseError(String),

    /// Proof verification completed but did not establish a refutation.
    #[error("verification failed: {0}")]
    VerificationFailed(String),

    /// The input CNF or proof format was malformed.
    #[error("invalid format: {0}")]
    InvalidFormat(String),

    /// The proof file contained no proof steps.
    #[error("proof is empty")]
    EmptyProof,
}

/// The detected DRAT serialization format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DratFormat {
    /// Human-readable text DRAT.
    Text,
    /// Binary DRAT with LEB128-encoded literals.
    Binary,
}

/// A single step in a Ay DRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum AyDratProofStep {
    /// Add a clause to the active clause set.
    Add(Vec<Literal>),
    /// Delete a clause from the active clause set.
    Delete(Vec<Literal>),
}

/// Parsed CNF metadata and clauses for proof replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AyDratImporter {
    /// Number of propositional variables in the source CNF.
    pub(crate) num_vars: u32,
    /// Original CNF clauses in DIMACS literal form.
    pub(crate) original_clauses: Vec<Clause>,
}

impl AyDratImporter {
    /// Create a new importer from a raw CNF formula.
    #[must_use]
    pub(crate) fn new(num_vars: u32, clauses: Vec<Clause>) -> Self {
        Self {
            num_vars,
            original_clauses: clauses,
        }
    }

    /// Parse a DIMACS CNF string into an importer.
    pub(crate) fn from_dimacs(dimacs_str: &str) -> Result<Self, AyImportError> {
        let cnf = Cnf::from_dimacs(dimacs_str)
            .map_err(|err| AyImportError::InvalidFormat(err.to_string()))?;
        Ok(Self::new(cnf.num_vars, cnf.to_dimacs_clauses()))
    }
}

/// Summary of Ay DRAT verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AyDratVerificationResult {
    /// Whether the imported proof is a valid refutation.
    pub valid: bool,
    /// Number of proof steps successfully checked.
    pub steps_checked: usize,
    /// Detected proof format.
    pub format: DratFormat,
    /// Human-readable parser and verifier diagnostics.
    pub diagnostics: Vec<String>,
}

/// Detect the DRAT format using Ay's text-vs-binary heuristic.
#[must_use]
pub(crate) fn detect_format(data: &[u8]) -> DratFormat {
    let mut index = 0;
    while index < data.len() && data[index].is_ascii_whitespace() {
        index += 1;
    }

    if index >= data.len() {
        return DratFormat::Text;
    }

    match data[index] {
        b'a' => DratFormat::Binary,
        b'd' if data.get(index + 1).is_some_and(|byte| *byte != b' ') => DratFormat::Binary,
        _ => DratFormat::Text,
    }
}

/// Parse a text-format DRAT proof.
pub(crate) fn parse_text_drat(data: &[u8]) -> Result<Vec<AyDratProofStep>, AyImportError> {
    let text = std::str::from_utf8(data)
        .map_err(|err| AyImportError::DratParseError(format!("invalid UTF-8: {err}")))?;

    let mut steps = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let (is_delete, tokens) = if let Some(rest) = trimmed.strip_prefix('d') {
            (true, rest.trim_start())
        } else {
            (false, trimmed)
        };

        let mut clause = Vec::new();
        for token in tokens.split_whitespace() {
            let literal = token.parse::<Literal>().map_err(|err| {
                AyImportError::DratParseError(format!("bad DRAT literal '{token}': {err}"))
            })?;
            if literal == 0 {
                break;
            }
            clause.push(literal);
        }

        if is_delete {
            steps.push(AyDratProofStep::Delete(clause));
        } else {
            steps.push(AyDratProofStep::Add(clause));
        }
    }

    Ok(steps)
}

/// Parse a binary-format DRAT proof.
pub(crate) fn parse_binary_drat(data: &[u8]) -> Result<Vec<AyDratProofStep>, AyImportError> {
    let mut steps = Vec::new();
    let mut pos = 0;

    while pos < data.len() {
        while pos < data.len() && data[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos >= data.len() {
            break;
        }

        let marker = data[pos];
        pos += 1;

        let is_delete = match marker {
            b'a' => false,
            b'd' => true,
            _ => {
                return Err(AyImportError::DratParseError(format!(
                    "unexpected binary DRAT marker 0x{marker:02x} at offset {}",
                    pos - 1
                )))
            }
        };

        let mut clause = Vec::new();
        loop {
            let (value, next_pos) = read_leb128(data, pos)?;
            pos = next_pos;
            if value == 0 {
                break;
            }

            let abs_lit = i32::try_from(value >> 1).map_err(|_| {
                AyImportError::DratParseError(format!(
                    "binary DRAT literal {value} exceeds i32 range"
                ))
            })?;
            if abs_lit == 0 {
                return Err(AyImportError::DratParseError(format!(
                    "invalid binary DRAT literal encoding {value}"
                )));
            }

            let literal = if value & 1 == 0 { abs_lit } else { -abs_lit };
            clause.push(literal);
        }

        if is_delete {
            steps.push(AyDratProofStep::Delete(clause));
        } else {
            steps.push(AyDratProofStep::Add(clause));
        }
    }

    Ok(steps)
}

/// Parse a DRAT proof after auto-detecting text vs binary format.
pub(crate) fn parse_drat_proof(data: &[u8]) -> Result<Vec<AyDratProofStep>, AyImportError> {
    if data.is_empty() || data.iter().all(u8::is_ascii_whitespace) {
        return Err(AyImportError::EmptyProof);
    }

    let steps = match detect_format(data) {
        DratFormat::Text => parse_text_drat(data)?,
        DratFormat::Binary => parse_binary_drat(data)?,
    };

    if steps.is_empty() {
        return Err(AyImportError::EmptyProof);
    }

    Ok(steps)
}

/// Read a single unsigned LEB128 value starting at `pos`.
pub(crate) fn read_leb128(data: &[u8], pos: usize) -> Result<(u32, usize), AyImportError> {
    let mut value = 0_u64;
    let mut shift = 0_u32;
    let mut index = pos;

    loop {
        let byte = *data.get(index).ok_or_else(|| {
            AyImportError::DratParseError(format!(
                "unexpected end of input while decoding LEB128 at offset {index}"
            ))
        })?;
        index += 1;

        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            let decoded = u32::try_from(value).map_err(|_| {
                AyImportError::DratParseError(format!("LEB128 value {value} exceeds u32 range"))
            })?;
            return Ok((decoded, index));
        }

        shift += 7;
        if shift >= 35 {
            return Err(AyImportError::DratParseError(
                "LEB128 sequence is too long".to_string(),
            ));
        }
    }
}

/// Encode a single unsigned value as LEB128.
#[must_use]
pub(crate) fn write_leb128(mut value: u32) -> Vec<u8> {
    let mut out = Vec::new();

    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            return out;
        }
    }
}

/// Encode a DIMACS literal using binary DRAT's unsigned literal mapping.
#[must_use]
pub(crate) fn encode_literal_binary(lit: Literal) -> Vec<u8> {
    let abs = lit.unsigned_abs();
    let encoded = abs
        .checked_mul(2)
        .and_then(|value| {
            if lit < 0 {
                value.checked_add(1)
            } else {
                Some(value)
            }
        })
        .expect("literal magnitude exceeds binary DRAT encoding range");

    write_leb128(encoded)
}

/// Serialize proof steps to binary DRAT format.
#[must_use]
pub(crate) fn write_binary_drat(steps: &[AyDratProofStep]) -> Vec<u8> {
    let mut out = Vec::new();

    for step in steps {
        let (marker, clause) = match step {
            AyDratProofStep::Add(clause) => (b'a', clause),
            AyDratProofStep::Delete(clause) => (b'd', clause),
        };
        out.push(marker);
        for &lit in clause {
            out.extend_from_slice(&encode_literal_binary(lit));
        }
        out.push(0);
    }

    out
}

/// Serialize proof steps to text DRAT format.
#[must_use]
pub(crate) fn write_text_drat(steps: &[AyDratProofStep]) -> Vec<u8> {
    let mut out = String::new();

    for step in steps {
        match step {
            AyDratProofStep::Add(clause) => {
                for &lit in clause {
                    out.push_str(&lit.to_string());
                    out.push(' ');
                }
                out.push('0');
                out.push('\n');
            }
            AyDratProofStep::Delete(clause) => {
                out.push_str("d ");
                for &lit in clause {
                    out.push_str(&lit.to_string());
                    out.push(' ');
                }
                out.push('0');
                out.push('\n');
            }
        }
    }

    out.into_bytes()
}

/// Convert parsed Ay DRAT steps into the existing clean proof log format.
#[must_use]
pub(crate) fn convert_to_clean_proof_log(
    importer: &AyDratImporter,
    steps: &[AyDratProofStep],
) -> ProofLog {
    let mapped_steps = steps
        .iter()
        .map(|step| match step {
            AyDratProofStep::Add(clause) => LeanProofStep::Add(clause.clone()),
            AyDratProofStep::Delete(clause) => LeanProofStep::Delete(clause.clone()),
        })
        .collect();

    ProofLog {
        steps: mapped_steps,
        original_clauses: importer.original_clauses.clone(),
    }
}

/// Verify a parsed Ay DRAT proof using clean's proof log checker.
pub(crate) fn verify_ay_drat_proof(
    importer: &AyDratImporter,
    proof_data: &[u8],
) -> Result<AyDratVerificationResult, AyImportError> {
    let format = detect_format(proof_data);
    let steps = parse_drat_proof(proof_data)?;
    let proof_log = convert_to_clean_proof_log(importer, &steps);
    let proof_result: ProofLogResult = verify_proof_log(&proof_log);

    let mut diagnostics = vec![
        format!(
            "parsed {} proof step(s) as {:?} DRAT for {} variable(s)",
            steps.len(),
            format,
            importer.num_vars
        ),
        format!(
            "loaded {} original clause(s)",
            importer.original_clauses.len()
        ),
    ];

    if proof_result.valid {
        diagnostics.push(format!(
            "verified {} proof step(s)",
            proof_result.steps_verified
        ));
    } else {
        let message = match proof_result.first_error {
            Some(index) => format!("proof step {index} failed verification"),
            None => "proof verification failed".to_string(),
        };
        diagnostics.push(AyImportError::VerificationFailed(message).to_string());
    }

    let concludes_refutation = importer.original_clauses.iter().any(Vec::is_empty)
        || steps
            .iter()
            .any(|step| matches!(step, AyDratProofStep::Add(clause) if clause.is_empty()));

    if concludes_refutation {
        diagnostics.push("proof derives the empty clause".to_string());
    } else {
        diagnostics.push(
            AyImportError::VerificationFailed("proof does not derive the empty clause".to_string())
                .to_string(),
        );
    }

    Ok(AyDratVerificationResult {
        valid: proof_result.valid && concludes_refutation,
        steps_checked: proof_result.steps_verified,
        format,
        diagnostics,
    })
}

/// Load a DIMACS CNF file and Ay DRAT proof file, then verify them together.
pub fn verify_ay_drat_file(
    cnf_path: &Path,
    proof_path: &Path,
) -> Result<AyDratVerificationResult, AyImportError> {
    let cnf_data = fs::read_to_string(cnf_path)?;
    let importer = AyDratImporter::from_dimacs(&cnf_data)?;
    let proof_data = fs::read(proof_path)?;
    verify_ay_drat_proof(&importer, &proof_data)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn encode_leb128(mut value: u32) -> Vec<u8> {
        let mut out = Vec::new();
        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if value == 0 {
                return out;
            }
        }
    }

    fn sample_roundtrip_steps() -> Vec<AyDratProofStep> {
        vec![
            AyDratProofStep::Add(vec![1, -2, 3]),
            AyDratProofStep::Delete(vec![1, -2]),
            AyDratProofStep::Add(vec![]),
        ]
    }

    fn xor_two_unsat_importer() -> AyDratImporter {
        AyDratImporter::new(2, vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]])
    }

    fn xor_two_unsat_steps_with_deletions() -> Vec<AyDratProofStep> {
        vec![
            AyDratProofStep::Add(vec![1]),
            AyDratProofStep::Delete(vec![1, 2]),
            AyDratProofStep::Add(vec![-1]),
            AyDratProofStep::Delete(vec![-1, 2]),
            AyDratProofStep::Add(vec![]),
        ]
    }

    #[test]
    fn test_detect_format_text() {
        assert_eq!(detect_format(b"1 2 0\n"), DratFormat::Text);
    }

    #[test]
    fn test_detect_format_binary() {
        assert_eq!(detect_format(&[0x61, 0x02, 0x00]), DratFormat::Binary);
    }

    #[test]
    fn test_parse_text_drat_simple() {
        let steps = parse_text_drat(b"1 2 0\nd 1 2 0\n0\n").expect("parse");
        assert_eq!(
            steps,
            vec![
                AyDratProofStep::Add(vec![1, 2]),
                AyDratProofStep::Delete(vec![1, 2]),
                AyDratProofStep::Add(vec![]),
            ]
        );
    }

    #[test]
    fn test_parse_binary_drat_simple() {
        let steps = parse_binary_drat(&[b'a', 0x02, 0x00]).expect("parse");
        assert_eq!(steps, vec![AyDratProofStep::Add(vec![1])]);
    }

    #[test]
    fn test_leb128_decode() {
        assert_eq!(read_leb128(&[0x00], 0).expect("decode"), (0, 1));
        assert_eq!(read_leb128(&[0x7f], 0).expect("decode"), (127, 1));
        assert_eq!(read_leb128(&[0x80, 0x01], 0).expect("decode"), (128, 2));
        assert_eq!(
            read_leb128(&encode_leb128(300), 0).expect("decode"),
            (300, 2)
        );
    }

    #[test]
    fn test_convert_to_clean() {
        let importer = AyDratImporter::new(2, vec![vec![1, -2]]);
        let steps = vec![
            AyDratProofStep::Add(vec![2]),
            AyDratProofStep::Delete(vec![1, -2]),
        ];

        let proof_log = convert_to_clean_proof_log(&importer, &steps);
        assert_eq!(proof_log.original_clauses, vec![vec![1, -2]]);
        assert_eq!(
            proof_log.steps,
            vec![
                LeanProofStep::Add(vec![2]),
                LeanProofStep::Delete(vec![1, -2]),
            ]
        );
    }

    #[test]
    fn test_verify_trivial_unsat() {
        let importer = AyDratImporter::new(1, vec![vec![1], vec![-1]]);
        let result = verify_ay_drat_proof(&importer, b"0\n").expect("verify");
        assert!(result.valid);
        assert_eq!(result.steps_checked, 1);
        assert_eq!(result.format, DratFormat::Text);
    }

    #[test]
    fn test_verify_simple_rup() {
        let importer = AyDratImporter::new(2, vec![vec![1], vec![-1, 2], vec![-2]]);
        let result = verify_ay_drat_proof(&importer, b"2 0\n0\n").expect("verify");
        assert!(result.valid);
        assert_eq!(result.steps_checked, 2);
    }

    #[test]
    fn test_empty_proof_fails() {
        let importer = AyDratImporter::new(1, vec![vec![1]]);
        let error = verify_ay_drat_proof(&importer, b"").expect_err("empty proof");
        assert!(matches!(error, AyImportError::EmptyProof));
    }

    #[test]
    fn test_from_dimacs() {
        let importer = AyDratImporter::from_dimacs("c example\np cnf 2 2\n1 -2 0\n2 0\n")
            .expect("parse DIMACS");

        assert_eq!(importer.num_vars, 2);
        assert_eq!(importer.original_clauses, vec![vec![1, -2], vec![2]]);
    }

    #[test]
    fn test_leb128_roundtrip() {
        for value in [0, 1, 2, 63, 64, 127, 128, 255, 256, 16_384, u32::MAX] {
            let encoded = write_leb128(value);
            let (decoded, next_pos) = read_leb128(&encoded, 0).expect("decode");
            assert_eq!(decoded, value);
            assert_eq!(next_pos, encoded.len());
            assert_eq!(encoded, encode_leb128(value));
        }
    }

    #[test]
    fn test_encode_literal_positive() {
        assert_eq!(encode_literal_binary(1), vec![0x02]);
        assert_eq!(encode_literal_binary(5), vec![0x0a]);
    }

    #[test]
    fn test_encode_literal_negative() {
        assert_eq!(encode_literal_binary(-1), vec![0x03]);
        assert_eq!(encode_literal_binary(-5), vec![0x0b]);
    }

    #[test]
    fn test_binary_drat_roundtrip() {
        let steps = sample_roundtrip_steps();
        let encoded = write_binary_drat(&steps);
        let parsed = parse_binary_drat(&encoded).expect("parse");
        assert_eq!(parsed, steps);
    }

    #[test]
    fn test_text_drat_roundtrip() {
        let steps = sample_roundtrip_steps();
        let encoded = write_text_drat(&steps);
        let parsed = parse_text_drat(&encoded).expect("parse");
        assert_eq!(parsed, steps);
    }

    #[test]
    fn test_binary_to_text_cross_format() {
        let steps = sample_roundtrip_steps();
        let binary = write_binary_drat(&steps);
        let parsed_binary = parse_binary_drat(&binary).expect("parse binary");
        let text = write_text_drat(&parsed_binary);
        let parsed_text = parse_text_drat(&text).expect("parse text");
        assert_eq!(parsed_text, steps);
    }

    #[test]
    fn test_text_to_binary_cross_format() {
        let steps = sample_roundtrip_steps();
        let text = write_text_drat(&steps);
        let parsed_text = parse_text_drat(&text).expect("parse text");
        let binary = write_binary_drat(&parsed_text);
        let parsed_binary = parse_binary_drat(&binary).expect("parse binary");
        assert_eq!(parsed_binary, steps);
    }

    #[test]
    fn test_binary_drat_with_deletions_end_to_end() {
        let importer = xor_two_unsat_importer();
        let steps = xor_two_unsat_steps_with_deletions();
        let proof = write_binary_drat(&steps);

        let result = verify_ay_drat_proof(&importer, &proof).expect("verify");

        assert!(result.valid);
        assert_eq!(result.steps_checked, steps.len());
        assert_eq!(result.format, DratFormat::Binary);
    }

    #[test]
    fn test_binary_drat_multi_literal_clause() {
        let steps = vec![AyDratProofStep::Add(vec![1, -2, 3, -4])];
        let encoded = write_binary_drat(&steps);
        let parsed = parse_binary_drat(&encoded).expect("parse");
        assert_eq!(parsed, steps);
    }

    #[test]
    fn test_binary_drat_large_variable() {
        let steps = vec![AyDratProofStep::Add(vec![130])];
        let encoded = write_binary_drat(&steps);
        assert_eq!(encoded, vec![b'a', 0x84, 0x02, 0x00]);
        let parsed = parse_binary_drat(&encoded).expect("parse");
        assert_eq!(parsed, steps);
    }

    #[test]
    fn test_detect_format_binary_deletion() {
        let proof = write_binary_drat(&[AyDratProofStep::Delete(vec![1, -2])]);
        assert_eq!(detect_format(&proof), DratFormat::Binary);
        assert_eq!(proof[0], b'd');
        assert_ne!(proof[1], b' ');
    }

    #[test]
    fn test_empty_clause_binary() {
        let steps = vec![AyDratProofStep::Add(vec![])];
        let encoded = write_binary_drat(&steps);
        assert_eq!(encoded, vec![b'a', 0x00]);
        let parsed = parse_binary_drat(&encoded).expect("parse");
        assert_eq!(parsed, steps);
    }
}
