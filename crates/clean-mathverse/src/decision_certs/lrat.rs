// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LRAT certificate parser (text format).
//!
//! LRAT (Linear Resolution Asymmetric Tautology) extends DRAT with clause IDs
//! and resolution hints, enabling linear-time verification. Each addition step
//! includes the IDs of antecedent clauses used in the unit propagation derivation.
//!
//! Reference: Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp —
//! "Efficient Certified RAT Verification" (CADE 2017).

use super::types::{CnfFormula, LratStep, LratStepKind, SatCertFormat, SatCertificate};
use crate::decision::CertError;

// ---------------------------------------------------------------------------
// Text LRAT parser
// ---------------------------------------------------------------------------

/// Parse an LRAT certificate in text format.
///
/// # Format
///
/// Each line is one of:
/// - Addition: `id lit1 lit2 ... 0 hint1 hint2 ... 0`
/// - Deletion: `id d clause_id1 clause_id2 ... 0`
/// - Comment: `c ...` (ignored)
///
/// The clause ID is a positive integer. For addition steps, the clause body
/// comes first (terminated by `0`), followed by resolution hints (clause IDs
/// used to derive this clause via unit propagation, terminated by `0`).
///
/// # Errors
///
/// Returns [`CertError::Format`] if:
/// - A line has no tokens after trimming
/// - The clause ID is not a valid u64
/// - Literal or hint tokens are not valid integers
pub fn parse_lrat_text(input: &str) -> Result<Vec<LratStep>, CertError> {
    let mut steps = Vec::new();

    for line in input.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }

        let tokens: Vec<&str> = trimmed.split_whitespace().collect();
        if tokens.is_empty() {
            continue;
        }

        let id = tokens[0].parse::<u64>().map_err(|_| CertError::Format {
            message: format!("invalid LRAT clause ID: {:?}", tokens[0]),
        })?;

        // Check for deletion line: "id d clause_id1 clause_id2 ... 0"
        if tokens.len() > 1 && tokens[1] == "d" {
            let hints: Vec<u64> = tokens[2..]
                .iter()
                .map(|tok| {
                    tok.parse::<u64>().map_err(|_| CertError::Format {
                        message: format!("invalid LRAT deletion hint: {tok:?}"),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .take_while(|&h| h != 0)
                .collect();

            steps.push(LratStep::delete(id, hints));
            continue;
        }

        // Addition line: "id lit1 lit2 ... 0 hint1 hint2 ... 0"
        let rest = &tokens[1..];
        let mut clause = Vec::new();
        let mut hints = Vec::new();
        let mut past_first_zero = false;

        for &tok in rest {
            if tok == "0" {
                if past_first_zero {
                    // Second 0 terminates hints
                    break;
                }
                past_first_zero = true;
                continue;
            }

            if past_first_zero {
                // Parsing hints (u64 clause IDs)
                let hint = tok.parse::<u64>().map_err(|_| CertError::Format {
                    message: format!("invalid LRAT hint: {tok:?}"),
                })?;
                hints.push(hint);
            } else {
                // Parsing literals (i32)
                let lit = tok.parse::<i32>().map_err(|_| CertError::Format {
                    message: format!("invalid LRAT literal: {tok:?}"),
                })?;
                clause.push(lit);
            }
        }

        steps.push(LratStep::add(id, clause, hints));
    }

    Ok(steps)
}

/// Parse an LRAT text certificate and build a full [`SatCertificate`].
pub fn parse_lrat_text_certificate(
    input: &str,
    formula: CnfFormula,
) -> Result<SatCertificate, CertError> {
    let steps = parse_lrat_text(input)?;
    Ok(SatCertificate {
        formula,
        drat_steps: Vec::new(),
        lrat_steps: steps,
        format: SatCertFormat::LratText,
        verifier_tool: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_lrat_text_addition() {
        let input = "1 1 2 0 0\n2 -1 3 0 1 0\n";
        let steps = parse_lrat_text(input).expect("should parse");
        assert_eq!(steps.len(), 2);

        assert_eq!(steps[0].id, 1);
        assert_eq!(steps[0].kind, LratStepKind::Add);
        assert_eq!(steps[0].clause, vec![1, 2]);
        assert!(steps[0].hints.is_empty());

        assert_eq!(steps[1].id, 2);
        assert_eq!(steps[1].kind, LratStepKind::Add);
        assert_eq!(steps[1].clause, vec![-1, 3]);
        assert_eq!(steps[1].hints, vec![1]);
    }

    #[test]
    fn test_parse_lrat_text_deletion() {
        let input = "3 d 1 2 0\n";
        let steps = parse_lrat_text(input).expect("should parse");
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0].id, 3);
        assert_eq!(steps[0].kind, LratStepKind::Delete);
        assert!(steps[0].clause.is_empty());
        assert_eq!(steps[0].hints, vec![1, 2]);
    }

    #[test]
    fn test_parse_lrat_text_mixed() {
        let input = "\
            c LRAT proof\n\
            1 1 2 0 0\n\
            2 -1 3 0 1 0\n\
            3 d 1 0\n\
            4 3 0 1 2 0\n\
        ";
        let steps = parse_lrat_text(input).expect("should parse");
        assert_eq!(steps.len(), 4);

        // Step 1: addition, clause [1, 2], no hints
        assert_eq!(steps[0].kind, LratStepKind::Add);
        assert_eq!(steps[0].clause, vec![1, 2]);

        // Step 2: addition, clause [-1, 3], hint [1]
        assert_eq!(steps[1].kind, LratStepKind::Add);
        assert_eq!(steps[1].clause, vec![-1, 3]);
        assert_eq!(steps[1].hints, vec![1]);

        // Step 3: deletion of clause 1
        assert_eq!(steps[2].kind, LratStepKind::Delete);
        assert_eq!(steps[2].hints, vec![1]);

        // Step 4: addition, clause [3], hints [1, 2]
        assert_eq!(steps[3].kind, LratStepKind::Add);
        assert_eq!(steps[3].clause, vec![3]);
        assert_eq!(steps[3].hints, vec![1, 2]);
    }

    #[test]
    fn test_parse_lrat_text_empty() {
        let steps = parse_lrat_text("").expect("should parse empty");
        assert!(steps.is_empty());
    }

    #[test]
    fn test_parse_lrat_text_comments_only() {
        let input = "c comment 1\nc comment 2\n";
        let steps = parse_lrat_text(input).expect("should parse");
        assert!(steps.is_empty());
    }

    #[test]
    fn test_parse_lrat_text_invalid_id() {
        let input = "abc 1 2 0 0\n";
        let result = parse_lrat_text(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_lrat_text_invalid_literal() {
        let input = "1 xyz 0 0\n";
        let result = parse_lrat_text(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_lrat_text_invalid_hint() {
        let input = "1 1 0 abc 0\n";
        let result = parse_lrat_text(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_lrat_text_empty_clause() {
        // Empty clause (contradiction): "5 0 1 2 3 0"
        let input = "5 0 1 2 3 0\n";
        let steps = parse_lrat_text(input).expect("should parse");
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0].id, 5);
        assert!(steps[0].clause.is_empty());
        assert_eq!(steps[0].hints, vec![1, 2, 3]);
    }

    #[test]
    fn test_parse_lrat_text_certificate() {
        let formula = CnfFormula::new(3, vec![vec![1, 2], vec![-1, 3]]);
        let lrat = "1 1 0 0\n2 d 1 0\n";
        let cert = parse_lrat_text_certificate(lrat, formula).expect("should parse");
        assert_eq!(cert.format, SatCertFormat::LratText);
        assert!(cert.drat_steps.is_empty());
        assert_eq!(cert.lrat_steps.len(), 2);
        assert_eq!(cert.formula.num_vars, 3);
    }

    #[test]
    fn test_parse_lrat_text_large_ids() {
        let input = "1000000 1 -2 0 999999 0\n";
        let steps = parse_lrat_text(input).expect("should parse large IDs");
        assert_eq!(steps[0].id, 1_000_000);
        assert_eq!(steps[0].hints, vec![999_999]);
    }
}
