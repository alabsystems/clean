// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end verify-and-compose pipeline for gamma-crown certificate chains.
//!
//! Given an ordered sequence of entailment certificate JSON strings (one per
//! network block), this pipeline:
//!
//! 1. Parses each JSON into an `ExternalEntailmentCert`
//! 2. Verifies each certificate independently
//! 3. Composes the chain left-to-right via [`compose_entailment_certs`]
//! 4. Verifies the final composed certificate
//!
//! The result is a single certificate that proves the last block's
//! conclusion from the first block's premises -- an end-to-end bound
//! for the sub-network.

use super::composition::{compose_entailment_certs, CompositionError};
use clean_elab::cert::external::{
    verify_entailment_certificate, ExternalCertError, ExternalEntailmentCert,
};
use thiserror::Error;

/// Errors from the verify-and-compose pipeline.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum PipelineError {
    /// JSON parsing failed for a certificate in the chain.
    #[error("parse error at index {index}: {source}")]
    ParseError {
        index: usize,
        source: serde_json::Error,
    },

    /// Individual certificate verification failed.
    #[error("verification failed at index {index}: {source}")]
    VerificationFailed {
        index: usize,
        source: ExternalCertError,
    },

    /// Certificate composition failed between two adjacent certificates.
    #[error("composition failed between index {left} and {right}: {source}")]
    CompositionFailed {
        left: usize,
        right: usize,
        source: CompositionError,
    },

    /// Pipeline requires at least one certificate.
    #[error("pipeline requires at least one certificate JSON")]
    EmptyPipeline,
}

/// Result of the pipeline: the final certificate plus metadata.
#[derive(Debug, Clone)]
pub struct PipelineResult {
    /// The final certificate (composed if >1 input, verified original if 1).
    pub certificate: ExternalEntailmentCert,
    /// Number of input certificates that were processed.
    pub input_count: usize,
    /// Number of composition steps performed (input_count - 1).
    pub composition_steps: usize,
}

/// Parse, verify, and compose a chain of entailment certificate JSON strings.
///
/// Each element of `cert_jsons` should be a JSON string encoding an
/// `ExternalEntailmentCert`. The certificates are composed left-to-right:
/// cert 0 feeds into cert 1, cert 1 feeds into cert 2, etc.
///
/// # Errors
///
/// Returns the first error encountered (parse, verification, or composition),
/// with the index indicating which certificate caused the failure.
pub fn verify_and_compose_pipeline(cert_jsons: &[&str]) -> Result<PipelineResult, PipelineError> {
    if cert_jsons.is_empty() {
        return Err(PipelineError::EmptyPipeline);
    }

    // Phase 1: Parse all certificates.
    let certs: Vec<ExternalEntailmentCert> = cert_jsons
        .iter()
        .enumerate()
        .map(|(i, json)| {
            serde_json::from_str(json).map_err(|e| PipelineError::ParseError {
                index: i,
                source: e,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Phase 2: Verify each certificate independently.
    for (i, cert) in certs.iter().enumerate() {
        verify_entailment_certificate(cert).map_err(|e| PipelineError::VerificationFailed {
            index: i,
            source: e,
        })?;
    }

    // Phase 3: Compose left-to-right.
    let input_count = certs.len();
    if input_count == 1 {
        return Ok(PipelineResult {
            certificate: certs.into_iter().next().expect("checked non-empty"),
            input_count: 1,
            composition_steps: 0,
        });
    }

    let mut iter = certs.into_iter();
    let first = iter.next().expect("checked non-empty");
    let mut accumulated = ExternalEntailmentCert {
        version: first.version,
        premises: first.premises,
        multipliers: first.multipliers,
        conclusion: first.conclusion,
    };

    for (step, next_cert) in iter.enumerate() {
        let composed = compose_entailment_certs(&accumulated, &next_cert).map_err(|e| {
            PipelineError::CompositionFailed {
                left: step,
                right: step + 1,
                source: e,
            }
        })?;
        accumulated = composed.certificate;
    }

    Ok(PipelineResult {
        certificate: accumulated,
        input_count,
        composition_steps: input_count - 1,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pipeline_empty_returns_error() {
        let result = verify_and_compose_pipeline(&[]);
        assert!(matches!(result, Err(PipelineError::EmptyPipeline)));
    }

    #[test]
    fn test_pipeline_invalid_json_returns_parse_error() {
        let result = verify_and_compose_pipeline(&["not valid json"]);
        match result {
            Err(PipelineError::ParseError { index: 0, .. }) => {}
            other => panic!("expected ParseError at index 0, got {other:?}"),
        }
    }

    #[test]
    fn test_pipeline_single_cert_passes_through() {
        let json = r#"{
            "version": "1.0",
            "premises": [{
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "5"
            }],
            "multipliers": ["1"],
            "conclusion": {
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "6"
            }
        }"#;

        let result = verify_and_compose_pipeline(&[json]).expect("single cert should pass");
        assert_eq!(result.input_count, 1);
        assert_eq!(result.composition_steps, 0);
    }

    #[test]
    fn test_pipeline_bad_cert_in_middle_returns_verification_error() {
        let good_json = r#"{
            "version": "1.0",
            "premises": [{
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "5"
            }],
            "multipliers": ["1"],
            "conclusion": {
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "6"
            }
        }"#;

        // Entailment that claims x <= 5 implies x <= 3 -- invalid (5 > 3).
        let bad_json = r#"{
            "version": "1.0",
            "premises": [{
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "5"
            }],
            "multipliers": ["1"],
            "conclusion": {
                "type": "linear_constraint",
                "kind": "le",
                "coefficients": {"x": "1"},
                "constant": "3"
            }
        }"#;

        let result = verify_and_compose_pipeline(&[good_json, bad_json]);
        match result {
            Err(PipelineError::VerificationFailed { index: 1, .. }) => {}
            other => panic!("expected VerificationFailed at index 1, got {other:?}"),
        }
    }
}
