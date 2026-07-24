// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification-condition backend input protocol.

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Supported backend input formats for VC submission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[derive(Default)]
pub enum VcInputFormat {
    /// SMT-LIB2 text input.
    #[default]
    SmtLib2,
    /// Why3 input.
    Why3,
    /// Backend-defined custom input.
    Custom,
}

/// A verification condition ready for backend translation.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationCondition {
    /// Assumptions that must hold before the proof obligation is checked.
    pub preconditions: Vec<String>,
    /// Properties the backend must establish under the assumptions.
    pub postconditions: Vec<String>,
    /// Loop or inductive invariants that remain in scope for the VC.
    pub invariants: Vec<String>,
}

impl VerificationCondition {
    /// Construct a new verification condition.
    #[must_use]
    pub fn new(
        preconditions: Vec<String>,
        postconditions: Vec<String>,
        invariants: Vec<String>,
    ) -> Self {
        Self {
            preconditions,
            postconditions,
            invariants,
        }
    }
}

/// Errors produced while translating or submitting verification conditions.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum VcProtocolError {
    /// A batch requested one format while the translator emits another.
    #[error(
        "translator format mismatch: batch requires {expected:?}, translator provides {actual:?}"
    )]
    FormatMismatch {
        /// Format requested by the batch.
        expected: VcInputFormat,
        /// Format emitted by the translator.
        actual: VcInputFormat,
    },
    /// A postcondition list was missing.
    #[error("verification condition must contain at least one postcondition")]
    MissingPostcondition,
    /// One clause was empty or whitespace.
    #[error("{section} clause {index} is empty")]
    EmptyClause {
        /// Clause section name.
        section: &'static str,
        /// Clause index in that section.
        index: usize,
    },
}

/// Protocol-local result type.
pub type Result<T> = std::result::Result<T, VcProtocolError>;

/// Converts VCs into backend-specific input payloads.
pub trait VcTranslator {
    /// Return the backend format produced by this translator.
    fn format(&self) -> VcInputFormat;

    /// Translate one verification condition into backend input text.
    fn translate(&self, vc: &VerificationCondition) -> Result<String>;

    /// Translate every VC in the batch using the same backend format.
    fn translate_batch(&self, batch: &VcBatch) -> Result<Vec<String>> {
        if batch.format != self.format() {
            return Err(VcProtocolError::FormatMismatch {
                expected: batch.format,
                actual: self.format(),
            });
        }

        batch.vcs.iter().map(|vc| self.translate(vc)).collect()
    }
}

/// SMT-LIB2 encoder for backend-facing VCs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SmtLib2Translator;

impl SmtLib2Translator {
    fn validate(vc: &VerificationCondition) -> Result<()> {
        if vc.postconditions.is_empty() {
            return Err(VcProtocolError::MissingPostcondition);
        }

        validate_section("precondition", &vc.preconditions)?;
        validate_section("postcondition", &vc.postconditions)?;
        validate_section("invariant", &vc.invariants)?;
        Ok(())
    }
}

impl VcTranslator for SmtLib2Translator {
    fn format(&self) -> VcInputFormat {
        VcInputFormat::SmtLib2
    }

    fn translate(&self, vc: &VerificationCondition) -> Result<String> {
        Self::validate(vc)?;

        let mut lines = vec!["(set-logic ALL)".to_string(), "; Preconditions".to_string()];
        lines.extend(render_assertions(&vc.preconditions));
        lines.push("; Invariants".to_string());
        lines.extend(render_assertions(&vc.invariants));
        lines.push("; Negated postcondition".to_string());
        lines.push(format!(
            "(assert {})",
            negate_formula(&combine_with_and(&vc.postconditions))
        ));
        lines.push("(check-sat)".to_string());
        lines.push("(exit)".to_string());
        Ok(lines.join("\n"))
    }
}

/// A batch of VCs targeted at one backend input format.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcBatch {
    /// Backend format required for this submission.
    pub format: VcInputFormat,
    /// Verification conditions submitted in request order.
    pub vcs: Vec<VerificationCondition>,
}

impl VcBatch {
    /// Construct a new batch for one backend format.
    #[must_use]
    pub fn new(format: VcInputFormat, vcs: Vec<VerificationCondition>) -> Self {
        Self { format, vcs }
    }

    /// Submit the batch through a backend translator.
    pub fn submit<T: VcTranslator>(&self, translator: &T) -> Result<Vec<String>> {
        translator.translate_batch(self)
    }
}

fn validate_section(section: &'static str, clauses: &[String]) -> Result<()> {
    for (index, clause) in clauses.iter().enumerate() {
        if clause.trim().is_empty() {
            return Err(VcProtocolError::EmptyClause { section, index });
        }
    }
    Ok(())
}

fn render_assertions(clauses: &[String]) -> impl Iterator<Item = String> + '_ {
    clauses
        .iter()
        .map(|clause| format!("(assert {})", clause.trim()))
}

fn combine_with_and(clauses: &[String]) -> String {
    match clauses {
        [clause] => clause.trim().to_string(),
        _ => format!(
            "(and {})",
            clauses
                .iter()
                .map(|clause| clause.trim())
                .collect::<Vec<_>>()
                .join(" ")
        ),
    }
}

fn negate_formula(formula: &str) -> String {
    format!("(not {formula})")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_vc(name: &str) -> VerificationCondition {
        VerificationCondition::new(
            vec!["(> x 0)".to_string(), format!("(= tag_{name} true)")],
            vec![format!("(> result_{name} x)")],
            vec!["(>= x 1)".to_string()],
        )
    }

    #[test]
    fn smtlib2_translation_emits_expected_structure() {
        let translator = SmtLib2Translator;
        let output = translator
            .translate(&VerificationCondition::new(
                vec!["(> x 0)".to_string()],
                vec!["(> y x)".to_string(), "(>= y 1)".to_string()],
                vec!["(>= x 1)".to_string()],
            ))
            .expect("translation should succeed");

        assert!(output.contains("(set-logic ALL)"));
        assert!(output.contains("; Preconditions\n(assert (> x 0))"));
        assert!(output.contains("; Invariants\n(assert (>= x 1))"));
        assert!(output.contains("(assert (not (and (> y x) (>= y 1))))"));
        assert!(output.ends_with("(exit)"));
    }

    #[test]
    fn smtlib2_translation_rejects_missing_postconditions() {
        let translator = SmtLib2Translator;
        let err = translator
            .translate(&VerificationCondition::new(
                vec!["(> x 0)".to_string()],
                Vec::new(),
                vec!["(>= x 1)".to_string()],
            ))
            .expect_err("missing postconditions should fail");

        assert_eq!(err, VcProtocolError::MissingPostcondition);
    }

    #[test]
    fn smtlib2_translation_rejects_blank_clauses() {
        let translator = SmtLib2Translator;
        let err = translator
            .translate(&VerificationCondition::new(
                vec!["  ".to_string()],
                vec!["(> y x)".to_string()],
                Vec::new(),
            ))
            .expect_err("blank clause should fail");

        assert_eq!(
            err,
            VcProtocolError::EmptyClause {
                section: "precondition",
                index: 0,
            }
        );
    }

    #[test]
    fn batch_submission_translates_each_vc_in_order() {
        let translator = SmtLib2Translator;
        let batch = VcBatch::new(
            VcInputFormat::SmtLib2,
            vec![sample_vc("first"), sample_vc("second")],
        );

        let submitted = batch.submit(&translator).expect("batch should translate");

        assert_eq!(submitted.len(), 2);
        assert!(submitted[0].contains("tag_first"));
        assert!(submitted[0].contains("result_first"));
        assert!(submitted[1].contains("tag_second"));
        assert!(submitted[1].contains("result_second"));
    }

    #[test]
    fn batch_submission_rejects_translator_format_mismatch() {
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
        struct Why3Translator;

        impl VcTranslator for Why3Translator {
            fn format(&self) -> VcInputFormat {
                VcInputFormat::Why3
            }

            fn translate(&self, vc: &VerificationCondition) -> Result<String> {
                Ok(format!("goal {}", combine_with_and(&vc.postconditions)))
            }
        }

        let batch = VcBatch::new(VcInputFormat::SmtLib2, vec![sample_vc("mismatch")]);
        let err = batch
            .submit(&Why3Translator)
            .expect_err("format mismatch should fail");

        assert_eq!(
            err,
            VcProtocolError::FormatMismatch {
                expected: VcInputFormat::SmtLib2,
                actual: VcInputFormat::Why3,
            }
        );
    }
}
