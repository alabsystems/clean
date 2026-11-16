// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Result and error vocabulary for the end-to-end NN verification pipeline.
//!
//! Split out of [`super`] (`e2e_verifier`) at its own "Types" banner: these are
//! the data types the orchestrator hands back (`VerificationResult`,
//! `TrustLevel`, `LayerVerifyResult`) plus its error enum and the conversions
//! feeding it. `e2e_verifier` re-exports all four, so the historical
//! `nn_verify::e2e_verifier::<name>` paths keep resolving.

use crate::nn_verify::certificate::farkas_bridge::{ExternalFarkasCert, FarkasBridgeError};
use crate::nn_verify::e2e_json_parser::PipelineParseError;
use crate::nn_verify::ibp_crown::Interval;

/// Full verification result for a neural network certificate.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) struct VerificationResult {
    /// Whether the claimed property is verified.
    pub verified: bool,
    /// Per-layer verification results.
    pub layer_results: Vec<LayerVerifyResult>,
    /// Final composed Farkas certificate (if all layers pass).
    pub composed_cert: Option<ExternalFarkasCert>,
    /// Total verification steps performed (one per layer + composition + property check).
    pub verification_steps: usize,
    /// Trust level classification.
    pub trust_level: TrustLevel,
}

/// Trust level for the verification result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TrustLevel {
    /// Fully verified: all Farkas certificates checked, composition valid.
    FullyVerified,
    /// Certificate-based: Farkas certificates verified but formal proofs are DerivedPending.
    CertificateBased,
    /// Partial: some layers verified, some failed.
    Partial {
        /// Number of verified layers.
        verified_layers: usize,
        /// Total number of layers.
        total_layers: usize,
    },
}

/// Verification result for a single layer.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) struct LayerVerifyResult {
    /// Layer index (0-based).
    pub layer_index: usize,
    /// Layer type string.
    pub layer_type: String,
    /// Whether the Farkas certificate is valid.
    pub farkas_valid: bool,
    /// Whether the bounds are structurally valid (non-empty, ordered).
    pub bounds_valid: bool,
    /// Input interval bounds (extracted from the Farkas certificate).
    pub input_interval: Option<Vec<Interval>>,
    /// Output interval bounds (extracted from the Farkas certificate).
    pub output_interval: Option<Vec<Interval>>,
}

/// Errors from the end-to-end verification pipeline.
#[derive(Debug)]
#[non_exhaustive]
pub(crate) enum E2eVerifyError {
    /// Certificate parsing or validation failed.
    ParseError(PipelineParseError),
    /// Farkas bridge error during chain composition.
    BridgeError(FarkasBridgeError),
}

impl std::fmt::Display for E2eVerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ParseError(e) => write!(f, "parse error: {e}"),
            Self::BridgeError(e) => write!(f, "bridge error: {e}"),
        }
    }
}

impl std::error::Error for E2eVerifyError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ParseError(e) => Some(e),
            Self::BridgeError(e) => Some(e),
        }
    }
}

impl From<PipelineParseError> for E2eVerifyError {
    fn from(e: PipelineParseError) -> Self {
        Self::ParseError(e)
    }
}

impl From<FarkasBridgeError> for E2eVerifyError {
    fn from(e: FarkasBridgeError) -> Self {
        Self::BridgeError(e)
    }
}
