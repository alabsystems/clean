// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Neural network verification certificate types.

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, ExprIdx, SourceSystem};

/// A neural network verification certificate stored in the Mathverse Library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NNVerificationCert {
    /// Network architecture specification (layer sizes, activation functions).
    pub network_spec: ExprIdx,
    /// Property proven (robustness, safety, Lipschitz, equivalence, ...).
    pub property: ExprIdx,
    /// Proof term (kernel-verified reduction to arithmetic lemmas).
    pub proof: ExprIdx,
    /// Source tool and version.
    pub source_tool: SourceSystem,
    /// Verification method used.
    pub method: VerificationMethod,
    /// Axiom profile (most NN certs use real arithmetic + approximation axioms).
    pub axiom_profile: AxiomProfile,
}

/// Method used to produce an NN verification certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum VerificationMethod {
    /// Mixed-integer linear programming (e.g., MN-BaB).
    Milp,
    /// Semidefinite programming (e.g., LipSDP).
    Sdp,
    /// Abstract interpretation (e.g., DeepPoly, ERAN).
    AbstractInterpretation,
    /// Bound propagation (e.g., alpha-beta-CROWN).
    BoundPropagation,
    /// Linear relaxation.
    LinearRelaxation,
    /// Certified training (IBP, SABR).
    CertifiedTraining,
    /// Compositional verification.
    Compositional,
}

use crate::error::{MathverseError, MathverseResult};

/// Validate an NN verification certificate.
///
/// Checks:
/// - `axiom_profile` contains the `NN_ABSTRACTION` bit (all NN certs require it).
/// - `network_spec`, `property`, and `proof` expression indices are non-zero
///   (zero typically indicates an unset/invalid index).
pub fn validate_cert(cert: &NNVerificationCert) -> MathverseResult<()> {
    if !cert.axiom_profile.has(AxiomProfile::NN_ABSTRACTION) {
        return Err(MathverseError::TrustViolation(
            "NN verification cert missing NN_ABSTRACTION in axiom_profile".into(),
        ));
    }
    if cert.network_spec == 0 && cert.property == 0 && cert.proof == 0 {
        return Err(MathverseError::TrustViolation(
            "NN verification cert has all zero expression indices".into(),
        ));
    }
    Ok(())
}

/// Parse a simplified gamma-crown JSON summary into an NNVerificationCert.
///
/// Expected JSON format:
/// ```json
/// {
///   "network_spec_idx": 42,
///   "property_idx": 43,
///   "proof_idx": 44,
///   "method": "BoundPropagation",
///   "source_tool": "GammaCrown",
///   "axiom_bits": 98304
/// }
/// ```
///
/// The `axiom_bits` field is the raw u64 value of the axiom profile bitvector.
/// If omitted, defaults to `FLOAT_APPROX | NN_ABSTRACTION`.
pub fn parse_gamma_crown_summary(json: &str) -> MathverseResult<NNVerificationCert> {
    let v: serde_json::Value = serde_json::from_str(json)?;

    let network_spec = v
        .get("network_spec_idx")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| MathverseError::ImportFailed {
            system: "gamma-crown".into(),
            reason: "missing network_spec_idx".into(),
        })? as ExprIdx;

    let property = v
        .get("property_idx")
        .and_then(|v| v.as_u64())
        .ok_or_else(|| MathverseError::ImportFailed {
            system: "gamma-crown".into(),
            reason: "missing property_idx".into(),
        })? as ExprIdx;

    let proof =
        v.get("proof_idx")
            .and_then(|v| v.as_u64())
            .ok_or_else(|| MathverseError::ImportFailed {
                system: "gamma-crown".into(),
                reason: "missing proof_idx".into(),
            })? as ExprIdx;

    let method = match v
        .get("method")
        .and_then(|v| v.as_str())
        .unwrap_or("BoundPropagation")
    {
        "Milp" => VerificationMethod::Milp,
        "Sdp" => VerificationMethod::Sdp,
        "AbstractInterpretation" => VerificationMethod::AbstractInterpretation,
        "BoundPropagation" => VerificationMethod::BoundPropagation,
        "LinearRelaxation" => VerificationMethod::LinearRelaxation,
        "CertifiedTraining" => VerificationMethod::CertifiedTraining,
        "Compositional" => VerificationMethod::Compositional,
        other => {
            return Err(MathverseError::ImportFailed {
                system: "gamma-crown".into(),
                reason: format!("unknown verification method: {other}"),
            })
        }
    };

    let source_tool_str = v
        .get("source_tool")
        .and_then(|v| v.as_str())
        .unwrap_or("GammaCrown");
    let source_tool = match source_tool_str {
        "GammaCrown" => SourceSystem::GammaCrown,
        "AlphaBetaCrown" => SourceSystem::AlphaBetaCrown,
        other => {
            return Err(MathverseError::ImportFailed {
                system: "gamma-crown".into(),
                reason: format!("unsupported source tool: {other}"),
            })
        }
    };

    let default_bits = (AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION).0;
    let axiom_bits = v
        .get("axiom_bits")
        .and_then(|v| v.as_u64())
        .unwrap_or(default_bits);

    Ok(NNVerificationCert {
        network_spec,
        property,
        proof,
        source_tool,
        method,
        axiom_profile: AxiomProfile::new(axiom_bits),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_valid_cert() -> NNVerificationCert {
        NNVerificationCert {
            network_spec: 10,
            property: 20,
            proof: 30,
            source_tool: SourceSystem::GammaCrown,
            method: VerificationMethod::BoundPropagation,
            axiom_profile: AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
        }
    }

    #[test]
    fn test_validate_cert_valid() {
        let cert = make_valid_cert();
        assert!(validate_cert(&cert).is_ok());
    }

    #[test]
    fn test_validate_cert_missing_nn_abstraction() {
        let mut cert = make_valid_cert();
        cert.axiom_profile = AxiomProfile::FLOAT_APPROX; // no NN_ABSTRACTION
        let result = validate_cert(&cert);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(
            msg.contains("NN_ABSTRACTION"),
            "error should mention NN_ABSTRACTION: {msg}"
        );
    }

    #[test]
    fn test_validate_cert_all_zero_indices() {
        let cert = NNVerificationCert {
            network_spec: 0,
            property: 0,
            proof: 0,
            source_tool: SourceSystem::GammaCrown,
            method: VerificationMethod::BoundPropagation,
            axiom_profile: AxiomProfile::NN_ABSTRACTION,
        };
        let result = validate_cert(&cert);
        assert!(result.is_err());
    }

    #[test]
    fn test_validate_cert_partial_zero_ok() {
        // Having only some zero indices is fine — only all-zero is rejected.
        let cert = NNVerificationCert {
            network_spec: 0,
            property: 0,
            proof: 1, // at least one non-zero
            source_tool: SourceSystem::GammaCrown,
            method: VerificationMethod::BoundPropagation,
            axiom_profile: AxiomProfile::NN_ABSTRACTION,
        };
        assert!(validate_cert(&cert).is_ok());
    }

    #[test]
    fn test_parse_gamma_crown_summary_full() {
        let json = r#"{
            "network_spec_idx": 100,
            "property_idx": 200,
            "proof_idx": 300,
            "method": "BoundPropagation",
            "source_tool": "GammaCrown",
            "axiom_bits": 98304
        }"#;
        let cert = parse_gamma_crown_summary(json).expect("should parse");
        assert_eq!(cert.network_spec, 100);
        assert_eq!(cert.property, 200);
        assert_eq!(cert.proof, 300);
        assert_eq!(cert.method, VerificationMethod::BoundPropagation);
        assert_eq!(cert.source_tool, SourceSystem::GammaCrown);
        assert!(cert.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
        assert!(cert.axiom_profile.has(AxiomProfile::FLOAT_APPROX));
    }

    #[test]
    fn test_parse_gamma_crown_summary_defaults() {
        // Minimal JSON with defaults for method, source_tool, axiom_bits.
        let json = r#"{
            "network_spec_idx": 1,
            "property_idx": 2,
            "proof_idx": 3
        }"#;
        let cert = parse_gamma_crown_summary(json).expect("should parse");
        assert_eq!(cert.method, VerificationMethod::BoundPropagation);
        assert_eq!(cert.source_tool, SourceSystem::GammaCrown);
        assert!(cert.axiom_profile.has(AxiomProfile::FLOAT_APPROX));
        assert!(cert.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
    }

    #[test]
    fn test_parse_gamma_crown_summary_alpha_beta() {
        let json = r#"{
            "network_spec_idx": 5,
            "property_idx": 6,
            "proof_idx": 7,
            "source_tool": "AlphaBetaCrown",
            "method": "Milp"
        }"#;
        let cert = parse_gamma_crown_summary(json).expect("should parse");
        assert_eq!(cert.source_tool, SourceSystem::AlphaBetaCrown);
        assert_eq!(cert.method, VerificationMethod::Milp);
    }

    #[test]
    fn test_parse_gamma_crown_summary_missing_field() {
        let json = r#"{ "property_idx": 2, "proof_idx": 3 }"#;
        let result = parse_gamma_crown_summary(json);
        assert!(result.is_err());
        let msg = format!("{}", result.unwrap_err());
        assert!(
            msg.contains("network_spec_idx"),
            "error should mention missing field: {msg}"
        );
    }

    #[test]
    fn test_parse_gamma_crown_summary_invalid_json() {
        let result = parse_gamma_crown_summary("not json");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_gamma_crown_summary_unknown_method() {
        let json = r#"{
            "network_spec_idx": 1,
            "property_idx": 2,
            "proof_idx": 3,
            "method": "UnknownMethod"
        }"#;
        let result = parse_gamma_crown_summary(json);
        assert!(result.is_err());
    }
}
