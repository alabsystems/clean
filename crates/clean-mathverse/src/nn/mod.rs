// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural network verification certificate format for the Mathverse Library.
//!
//! Supports certificates from:
//! - alpha-beta-CROWN / GammaCROWN (bound propagation proofs)
//! - VNN-COMP format (standardized NN verification)
//!
//! Each certificate proves a property about a neural network (e.g., local
//! robustness, output bounds) and gets an Mathverse entry with the appropriate
//! axiom profile (FLOAT_APPROX, NN_ABSTRACTION).

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

/// A neural network verification certificate.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NnCertificate {
    /// Certificate format/source.
    pub format: NnCertFormat,
    /// Property that was verified.
    pub property: NnProperty,
    /// Verification result.
    pub result: NnVerifyResult,
    /// Network metadata.
    pub network: NetworkInfo,
    /// Numerical bounds (if applicable).
    pub bounds: Option<BoundsInfo>,
    /// Source file path.
    pub source_file: Option<String>,
}

/// NN certificate format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum NnCertFormat {
    /// alpha-beta-CROWN bound propagation.
    AlphaBetaCrown,
    /// GammaCROWN abstraction-based.
    GammaCrown,
    /// VNN-COMP standard format.
    VnnComp,
    /// Generic bound certificate.
    GenericBounds,
}

/// Property being verified.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[non_exhaustive]
pub enum NnProperty {
    /// Local robustness within epsilon ball.
    LocalRobustness { epsilon: f64, norm: LpNorm },
    /// Output bounds on all neurons.
    OutputBounds,
    /// Reachability of a particular output region.
    Reachability { target_class: usize },
    /// General safety property (custom specification).
    SafetySpec { description: String },
}

/// Lp norm for robustness specifications.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LpNorm {
    Linf,
    L2,
    L1,
}

/// Verification result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum NnVerifyResult {
    /// Property holds (verified safe).
    Verified,
    /// Counterexample found (property violated).
    Violated,
    /// Verification timed out.
    Timeout,
    /// Result is unknown (inconclusive).
    Unknown,
}

/// Metadata about the neural network.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NetworkInfo {
    /// Number of layers (including input/output).
    pub num_layers: usize,
    /// Total number of neurons.
    pub num_neurons: usize,
    /// Input dimension.
    pub input_dim: usize,
    /// Output dimension.
    pub output_dim: usize,
    /// Activation function type.
    pub activation: ActivationType,
}

/// Activation function type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ActivationType {
    ReLU,
    Sigmoid,
    Tanh,
    Mixed,
}

/// Numerical bounds from verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BoundsInfo {
    /// Lower bounds on output neurons.
    pub lower: Vec<f64>,
    /// Upper bounds on output neurons.
    pub upper: Vec<f64>,
    /// Tightness measure (0.0 = loose, 1.0 = exact).
    pub tightness: f64,
}

/// Parse a VNN-COMP result line.
pub fn parse_vnncomp_result(line: &str) -> Option<NnVerifyResult> {
    let trimmed = line.trim().to_lowercase();
    if trimmed.contains("holds") || trimmed.contains("unsat") || trimmed == "verified" {
        Some(NnVerifyResult::Verified)
    } else if trimmed.contains("violated") || trimmed.contains("sat") && !trimmed.contains("unsat")
    {
        Some(NnVerifyResult::Violated)
    } else if trimmed.contains("timeout") {
        Some(NnVerifyResult::Timeout)
    } else if trimmed.contains("unknown") {
        Some(NnVerifyResult::Unknown)
    } else {
        None
    }
}

/// Create a certificate for a local robustness verification.
#[must_use]
pub fn robustness_cert(
    epsilon: f64,
    norm: LpNorm,
    result: NnVerifyResult,
    network: NetworkInfo,
    format: NnCertFormat,
) -> NnCertificate {
    NnCertificate {
        format,
        property: NnProperty::LocalRobustness { epsilon, norm },
        result,
        network,
        bounds: None,
        source_file: None,
    }
}

/// Create a certificate with output bounds.
#[must_use]
pub fn bounds_cert(
    lower: Vec<f64>,
    upper: Vec<f64>,
    network: NetworkInfo,
    format: NnCertFormat,
) -> NnCertificate {
    let tightness = if lower.len() == upper.len() && !lower.is_empty() {
        let ranges: Vec<f64> = lower.iter().zip(&upper).map(|(l, u)| u - l).collect();
        let avg_range = ranges.iter().sum::<f64>() / ranges.len() as f64;
        (1.0 - avg_range.min(1.0)).max(0.0)
    } else {
        0.0
    };

    NnCertificate {
        format,
        property: NnProperty::OutputBounds,
        result: NnVerifyResult::Verified,
        network,
        bounds: Some(BoundsInfo {
            lower,
            upper,
            tightness,
        }),
        source_file: None,
    }
}

/// Axiom profile for an NN certificate.
#[must_use]
pub fn nn_axiom_profile(cert: &NnCertificate) -> AxiomProfile {
    let base = AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION;
    match cert.format {
        NnCertFormat::AlphaBetaCrown | NnCertFormat::GammaCrown => base,
        NnCertFormat::VnnComp | NnCertFormat::GenericBounds => base,
    }
}

/// Trust level for an NN certificate.
#[must_use]
pub fn nn_trust_level(cert: &NnCertificate) -> TrustLevel {
    match cert.result {
        NnVerifyResult::Verified => TrustLevel::CertificateReplayed,
        NnVerifyResult::Violated => TrustLevel::PartiallyAxiomatized,
        NnVerifyResult::Timeout | NnVerifyResult::Unknown => TrustLevel::TrustedOracle,
    }
}

/// Provenance for an NN certificate.
#[must_use]
pub fn nn_provenance(cert: &NnCertificate) -> Provenance {
    let source = match cert.format {
        NnCertFormat::GammaCrown => SourceSystem::GammaCrown,
        NnCertFormat::AlphaBetaCrown => SourceSystem::AlphaBetaCrown,
        NnCertFormat::VnnComp | NnCertFormat::GenericBounds => SourceSystem::GammaCrown,
    };
    Provenance {
        source,
        original_name: format!("nn_cert_{}", cert.network.num_neurons),
        source_file: cert.source_file.clone(),
        axiom_profile: nn_axiom_profile(cert),
    }
}

/// Import statistics for NN certificates.
#[derive(Clone, Debug, Default)]
pub struct NnImportStats {
    pub certificates_parsed: usize,
    pub verified_count: usize,
    pub violated_count: usize,
    pub timeout_count: usize,
    pub total_neurons: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_network() -> NetworkInfo {
        NetworkInfo {
            num_layers: 4,
            num_neurons: 100,
            input_dim: 784,
            output_dim: 10,
            activation: ActivationType::ReLU,
        }
    }

    #[test]
    fn test_robustness_cert() {
        let cert = robustness_cert(
            0.03,
            LpNorm::Linf,
            NnVerifyResult::Verified,
            test_network(),
            NnCertFormat::AlphaBetaCrown,
        );
        assert_eq!(cert.result, NnVerifyResult::Verified);
        assert!(nn_axiom_profile(&cert).contains(AxiomProfile::FLOAT_APPROX));
        assert!(nn_axiom_profile(&cert).contains(AxiomProfile::NN_ABSTRACTION));
        assert_eq!(nn_trust_level(&cert), TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_bounds_cert() {
        let cert = bounds_cert(
            vec![0.1, 0.2],
            vec![0.3, 0.4],
            test_network(),
            NnCertFormat::GammaCrown,
        );
        assert!(cert.bounds.is_some());
        let bounds = cert.bounds.as_ref().unwrap();
        assert!(bounds.tightness > 0.0);
    }

    #[test]
    fn test_parse_vnncomp_result() {
        assert_eq!(
            parse_vnncomp_result("holds"),
            Some(NnVerifyResult::Verified)
        );
        assert_eq!(
            parse_vnncomp_result("violated"),
            Some(NnVerifyResult::Violated)
        );
        assert_eq!(
            parse_vnncomp_result("timeout"),
            Some(NnVerifyResult::Timeout)
        );
        assert_eq!(
            parse_vnncomp_result("unknown"),
            Some(NnVerifyResult::Unknown)
        );
        assert_eq!(parse_vnncomp_result("garbage"), None);
    }

    #[test]
    fn test_nn_trust_timeout() {
        let cert = robustness_cert(
            0.01,
            LpNorm::L2,
            NnVerifyResult::Timeout,
            test_network(),
            NnCertFormat::VnnComp,
        );
        assert_eq!(nn_trust_level(&cert), TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_nn_provenance_source() {
        let cert = robustness_cert(
            0.01,
            LpNorm::Linf,
            NnVerifyResult::Verified,
            test_network(),
            NnCertFormat::GammaCrown,
        );
        let prov = nn_provenance(&cert);
        assert_eq!(prov.source, SourceSystem::GammaCrown);
    }
}
