// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Types for NN verification certificates.
//!
//! These types represent parsed NN verification certificates from tools like
//! gamma-crown and alpha-beta-CROWN. They normalize the various tool-specific
//! formats into a uniform representation suitable for Mathverse shard import.

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Top-level certificate
// ---------------------------------------------------------------------------

/// A parsed NN verification certificate, normalized from tool-specific formats.
///
/// Each certificate proves (or fails to prove) a property about a neural network
/// and carries trust metadata for Mathverse import.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NNVerificationCert {
    /// Human-readable name for the network being verified.
    pub network_name: String,
    /// The robustness/safety property that was checked.
    pub property: RobustnessProperty,
    /// Which verification tool produced this certificate.
    pub verifier_tool: VerifierTool,
    /// Verification outcome.
    pub result: VerificationResult,
    /// Proof data (bounds, dual variables, etc.) when available.
    pub certificate_data: CertificateData,
    /// Network architecture specification.
    pub network_spec: NetworkSpec,
}

/// Which verification tool produced the certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerifierTool {
    /// gamma-crown (CROWN-family bound propagation).
    GammaCrown,
    /// alpha-beta-CROWN (branch-and-bound + bound propagation).
    AlphaBetaCrown,
    /// Generic VNN-COMP tool.
    VnnComp,
}

impl VerifierTool {
    /// Map to the Mathverse `SourceSystem` for provenance tracking.
    #[must_use]
    pub const fn source_system(self) -> SourceSystem {
        match self {
            Self::GammaCrown => SourceSystem::GammaCrown,
            Self::AlphaBetaCrown => SourceSystem::AlphaBetaCrown,
            Self::VnnComp => SourceSystem::GammaCrown, // closest match
        }
    }
}

/// Verification outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VerificationResult {
    /// Property verified (safe).
    Verified,
    /// Counterexample found (property violated).
    Counterexample,
    /// Inconclusive (timeout, numerical issues, etc.).
    Unknown,
}

impl VerificationResult {
    /// Map to the Mathverse `TrustLevel` for shard import.
    #[must_use]
    pub const fn trust_level(self) -> TrustLevel {
        match self {
            Self::Verified => TrustLevel::CertificateReplayed,
            Self::Counterexample => TrustLevel::PartiallyAxiomatized,
            Self::Unknown => TrustLevel::TrustedOracle,
        }
    }
}

// ---------------------------------------------------------------------------
// Network specification
// ---------------------------------------------------------------------------

/// Neural network architecture specification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NetworkSpec {
    /// Input dimensionality.
    pub input_dim: usize,
    /// Output dimensionality.
    pub output_dim: usize,
    /// Layer specifications, in order from input to output.
    pub layers: Vec<LayerSpec>,
    /// Primary activation function.
    pub activation: Activation,
}

/// Specification for a single network layer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LayerSpec {
    /// Layer kind.
    pub kind: LayerKind,
    /// Input dimension for this layer.
    pub input_dim: usize,
    /// Output dimension for this layer.
    pub output_dim: usize,
}

/// Layer kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum LayerKind {
    /// Fully connected (dense) layer.
    Dense,
    /// Convolutional layer.
    Conv,
    /// Residual connection (skip connection).
    Residual,
    /// Layer normalization.
    LayerNorm,
    /// Batch normalization.
    BatchNorm,
}

/// Activation function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum Activation {
    ReLU,
    Sigmoid,
    Tanh,
    /// No activation (identity).
    None,
}

// ---------------------------------------------------------------------------
// Robustness property
// ---------------------------------------------------------------------------

/// The property being verified: input perturbation region + output constraint.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RobustnessProperty {
    /// Input perturbation region (epsilon-ball specification).
    pub input_region: InputRegion,
    /// Output constraint that must hold for all inputs in the region.
    pub output_constraint: OutputConstraint,
}

/// Input perturbation specification.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub enum InputRegion {
    /// Lp-norm epsilon ball around a reference input.
    EpsilonBall {
        /// Perturbation radius.
        epsilon: f64,
        /// Norm type.
        norm: LpNorm,
        /// Reference input (center of the ball). Empty if not provided.
        center: Vec<f64>,
    },
}

/// Lp norm for perturbation specifications.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LpNorm {
    /// L-infinity norm (max absolute deviation).
    Linf,
    /// L2 (Euclidean) norm.
    L2,
    /// L1 (Manhattan) norm.
    L1,
}

/// Output constraint that must hold under perturbation.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OutputConstraint {
    /// Classification must remain the same as the reference input.
    ClassificationPreserved {
        /// The original predicted class index.
        original_class: usize,
    },
    /// A specific output neuron must remain above/below a bound.
    NeuronBound {
        /// Output neuron index.
        neuron_idx: usize,
        /// Lower bound (if any).
        lower: Option<f64>,
        /// Upper bound (if any).
        upper: Option<f64>,
    },
}

// ---------------------------------------------------------------------------
// Certificate data (proof content)
// ---------------------------------------------------------------------------

/// Proof data attached to the certificate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CertificateData {
    /// Type of proof technique used.
    pub proof_type: ProofType,
    /// Computed bounds on intermediate layers or outputs.
    pub bounds: Vec<LayerBounds>,
    /// Intermediate verification results (e.g., per-neuron split decisions).
    pub intermediate_results: Vec<IntermediateResult>,
}

/// Proof technique used by the verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofType {
    /// LP duality (linear programming relaxation).
    LpDuality,
    /// Mixed-integer linear programming.
    Milp,
    /// Semidefinite programming relaxation.
    Sdp,
    /// Abstract interpretation (interval, zonotope, etc.).
    AbstractInterpretation,
    /// CROWN-family bound propagation.
    BoundPropagation,
}

/// Bounds computed for a single layer.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LayerBounds {
    /// Layer index (0-based from input).
    pub layer_idx: usize,
    /// Lower bounds on neuron activations.
    pub lower: Vec<f64>,
    /// Upper bounds on neuron activations.
    pub upper: Vec<f64>,
}

/// An intermediate result from the verification process.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub enum IntermediateResult {
    /// ReLU neuron stability classification.
    NeuronStability {
        /// Layer index.
        layer_idx: usize,
        /// Number of neurons proven to be always active (lower > 0).
        always_active: usize,
        /// Number of neurons proven to be always inactive (upper <= 0).
        always_inactive: usize,
        /// Number of unstable neurons.
        unstable: usize,
    },
}

// ---------------------------------------------------------------------------
// Axiom profile computation
// ---------------------------------------------------------------------------

impl NNVerificationCert {
    /// Compute the axiom profile for this certificate.
    ///
    /// All NN verification certificates carry `FLOAT_APPROX | NN_ABSTRACTION`
    /// because they depend on floating-point arithmetic and neural network
    /// abstraction techniques.
    #[must_use]
    pub const fn axiom_profile(&self) -> AxiomProfile {
        AxiomProfile::new(AxiomProfile::FLOAT_APPROX.0 | AxiomProfile::NN_ABSTRACTION.0)
    }

    /// Compute the trust level for this certificate.
    #[must_use]
    pub const fn trust_level(&self) -> TrustLevel {
        self.result.trust_level()
    }

    /// Total number of neurons across all layers.
    #[must_use]
    pub fn total_neurons(&self) -> usize {
        self.network_spec.layers.iter().map(|l| l.output_dim).sum()
    }
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Import statistics for a batch of NN verification certificates.
#[derive(Clone, Debug, Default)]
pub struct NnCertImportStats {
    /// Total certificates parsed.
    pub total_parsed: usize,
    /// Certificates with `Verified` result.
    pub verified_count: usize,
    /// Certificates with `Counterexample` result.
    pub counterexample_count: usize,
    /// Certificates with `Unknown` result.
    pub unknown_count: usize,
    /// Total neurons across all certificates.
    pub total_neurons: usize,
    /// Total shard entries written.
    pub entries_written: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_cert() -> NNVerificationCert {
        NNVerificationCert {
            network_name: "mnist_relu_4_256".to_string(),
            property: RobustnessProperty {
                input_region: InputRegion::EpsilonBall {
                    epsilon: 0.03,
                    norm: LpNorm::Linf,
                    center: vec![],
                },
                output_constraint: OutputConstraint::ClassificationPreserved { original_class: 7 },
            },
            verifier_tool: VerifierTool::GammaCrown,
            result: VerificationResult::Verified,
            certificate_data: CertificateData {
                proof_type: ProofType::BoundPropagation,
                bounds: vec![],
                intermediate_results: vec![],
            },
            network_spec: NetworkSpec {
                input_dim: 784,
                output_dim: 10,
                layers: vec![
                    LayerSpec {
                        kind: LayerKind::Dense,
                        input_dim: 784,
                        output_dim: 256,
                    },
                    LayerSpec {
                        kind: LayerKind::Dense,
                        input_dim: 256,
                        output_dim: 256,
                    },
                    LayerSpec {
                        kind: LayerKind::Dense,
                        input_dim: 256,
                        output_dim: 10,
                    },
                ],
                activation: Activation::ReLU,
            },
        }
    }

    #[test]
    fn test_nn_cert_axiom_profile_has_float_and_nn_bits() {
        let cert = sample_cert();
        let profile = cert.axiom_profile();
        assert!(profile.has(AxiomProfile::FLOAT_APPROX));
        assert!(profile.has(AxiomProfile::NN_ABSTRACTION));
        assert!(profile.is_trust_gated());
    }

    #[test]
    fn test_nn_cert_trust_level_verified() {
        let cert = sample_cert();
        assert_eq!(cert.trust_level(), TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_nn_cert_trust_level_counterexample() {
        let mut cert = sample_cert();
        cert.result = VerificationResult::Counterexample;
        assert_eq!(cert.trust_level(), TrustLevel::PartiallyAxiomatized);
    }

    #[test]
    fn test_nn_cert_trust_level_unknown() {
        let mut cert = sample_cert();
        cert.result = VerificationResult::Unknown;
        assert_eq!(cert.trust_level(), TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_nn_cert_total_neurons() {
        let cert = sample_cert();
        assert_eq!(cert.total_neurons(), 256 + 256 + 10);
    }

    #[test]
    fn test_verifier_tool_source_system() {
        assert_eq!(
            VerifierTool::GammaCrown.source_system(),
            SourceSystem::GammaCrown
        );
        assert_eq!(
            VerifierTool::AlphaBetaCrown.source_system(),
            SourceSystem::AlphaBetaCrown
        );
    }

    #[test]
    fn test_serde_roundtrip_cert() {
        let cert = sample_cert();
        let json = serde_json::to_string(&cert).expect("serialize");
        let restored: NNVerificationCert = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(restored.network_name, "mnist_relu_4_256");
        assert_eq!(restored.result, VerificationResult::Verified);
        assert_eq!(restored.network_spec.input_dim, 784);
        assert_eq!(restored.network_spec.layers.len(), 3);
    }

    #[test]
    fn test_serde_roundtrip_layer_kind() {
        for kind in [
            LayerKind::Dense,
            LayerKind::Conv,
            LayerKind::Residual,
            LayerKind::LayerNorm,
            LayerKind::BatchNorm,
        ] {
            let json = serde_json::to_string(&kind).expect("serialize");
            let restored: LayerKind = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(kind, restored);
        }
    }

    #[test]
    fn test_serde_roundtrip_proof_type() {
        for pt in [
            ProofType::LpDuality,
            ProofType::Milp,
            ProofType::Sdp,
            ProofType::AbstractInterpretation,
            ProofType::BoundPropagation,
        ] {
            let json = serde_json::to_string(&pt).expect("serialize");
            let restored: ProofType = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(pt, restored);
        }
    }

    #[test]
    fn test_import_stats_default() {
        let stats = NnCertImportStats::default();
        assert_eq!(stats.total_parsed, 0);
        assert_eq!(stats.entries_written, 0);
    }
}
