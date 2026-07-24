// Copyright 2026 Andrew Yates
// Author: dbx-clean-ai
// SPDX-License-Identifier: Apache-2.0

//! Dependency-free tactic policy adapter for math-project domain profiles.
//!
//! This module intentionally carries only static profile policy and tactic
//! configuration. CLI/server JSON wiring and manifest serialization live
//! outside `clean-elab`.

use super::cert_simp::{CertSimpCandidatePack, CertSimpConfig};
use super::project_mathverse::{NatCoercionPolicy, ProjectMathverseConfig};

/// Tactic-facing domain profiles used to tune proof-state automation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TacticDomainProfile {
    /// General Lean/Init-style goals with no certificate-specific packs.
    General,
    /// SAT, pseudo-Boolean, cardinality, LRAT/DRAT/VeriPB, and Ay obligations.
    SatPb,
    /// Neural-network verification obligations and Gamma-Crown artifacts.
    NnVerify,
    /// Resolution, cutting planes, polynomial-calculus, and lower-bound work.
    ProofComplexity,
}

impl TacticDomainProfile {
    /// Stable manifest/API spelling for this profile.
    pub const fn name(self) -> &'static str {
        match self {
            Self::General => "general",
            Self::SatPb => "sat-pb",
            Self::NnVerify => "nn-verify",
            Self::ProofComplexity => "proof-complexity",
        }
    }

    /// Parse stable manifest/API spellings. Unknown names fail closed.
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "general" | "core" => Some(Self::General),
            "sat-pb" => Some(Self::SatPb),
            "nn-verify" => Some(Self::NnVerify),
            "proof-complexity" => Some(Self::ProofComplexity),
            _ => None,
        }
    }

    /// Semantic heads used by retrieval/ranking layers to recognize residue.
    pub const fn semantic_heads(self) -> &'static [&'static str] {
        match self {
            Self::General => &["Eq", "Iff", "And", "Or", "Exists", "Nat", "Int"],
            Self::SatPb => &[
                "CNF",
                "Clause",
                "Literal",
                "Assignment",
                "PBConstraint",
                "Cardinality",
                "Resolution",
                "Subsumption",
                "VeriPB",
                "LRAT",
                "DRAT",
            ],
            Self::NnVerify => &[
                "Interval",
                "AffineForm",
                "Zonotope",
                "IBP",
                "CROWN",
                "LayerNorm",
                "ReLU",
                "ExternalFarkasCert",
                "GammaCrown",
            ],
            Self::ProofComplexity => &[
                "Resolution",
                "CuttingPlanes",
                "PolynomialCalculus",
                "FourierBoolean",
                "LowerBoundFamily",
                "GF2",
            ],
        }
    }

    /// Normalizer names advertised by this tactic-layer profile.
    pub const fn normalizers(self) -> &'static [&'static str] {
        match self {
            Self::General => &["simp", "omega"],
            Self::SatPb => &["cert_simp", "cert_mathverse", "sat_pb_nf"],
            Self::NnVerify => &["cert_simp", "cert_mathverse", "nn_interval_nf"],
            Self::ProofComplexity => &["cert_simp", "proof_complexity_nf"],
        }
    }

    /// Recommended tactic sequence names for proof-state search.
    pub const fn recommended_tactics(self) -> &'static [&'static str] {
        match self {
            Self::General => &["exact", "apply", "rw", "simp", "omega"],
            Self::SatPb => &["cert_simp", "cert_mathverse", "simp", "omega"],
            Self::NnVerify => &["cert_simp", "cert_mathverse", "linarith", "simp"],
            Self::ProofComplexity => &["cert_simp", "simp", "omega"],
        }
    }

    /// `cert_simp` configuration for this profile.
    pub fn cert_simp_config(self) -> CertSimpConfig {
        cert_simp_config(self)
    }

    /// `cert_mathverse`/project-mathverse configuration for this profile.
    pub fn project_mathverse_config(self) -> ProjectMathverseConfig {
        project_mathverse_config(self)
    }
}

/// `cert_simp` configuration for a tactic domain profile.
pub fn cert_simp_config(profile: TacticDomainProfile) -> CertSimpConfig {
    match profile {
        TacticDomainProfile::General => cert_simp_profile_config(1000, &[]),
        TacticDomainProfile::SatPb => {
            cert_simp_profile_config(5000, &[CertSimpCandidatePack::SatPb])
        }
        TacticDomainProfile::NnVerify => {
            cert_simp_profile_config(5000, &[CertSimpCandidatePack::NnVerify])
        }
        TacticDomainProfile::ProofComplexity => {
            cert_simp_profile_config(5000, &[CertSimpCandidatePack::SatPb])
        }
    }
}

fn cert_simp_profile_config(
    max_steps: usize,
    candidate_packs: &[CertSimpCandidatePack],
) -> CertSimpConfig {
    CertSimpConfig {
        max_steps,
        simplify_hypotheses: true,
        diagnostics: true,
        ..CertSimpConfig::default().with_candidate_packs(candidate_packs)
    }
}

/// `cert_mathverse`/project-mathverse configuration for a tactic domain profile.
pub fn project_mathverse_config(profile: TacticDomainProfile) -> ProjectMathverseConfig {
    let cert_simp = cert_simp_config(profile);
    match profile {
        TacticDomainProfile::General => ProjectMathverseConfig {
            normalize_cert_terms: false,
            cert_simp,
            normalize_casts: true,
            coerce_nat: NatCoercionPolicy::LinearSafe,
            blocker_limit: 4,
            emit_telemetry: true,
        },
        TacticDomainProfile::SatPb => ProjectMathverseConfig {
            normalize_cert_terms: true,
            cert_simp,
            normalize_casts: true,
            coerce_nat: NatCoercionPolicy::LinearSafe,
            blocker_limit: 6,
            emit_telemetry: true,
        },
        TacticDomainProfile::NnVerify => ProjectMathverseConfig {
            normalize_cert_terms: true,
            cert_simp,
            normalize_casts: true,
            coerce_nat: NatCoercionPolicy::LinearSafe,
            blocker_limit: 6,
            emit_telemetry: true,
        },
        TacticDomainProfile::ProofComplexity => ProjectMathverseConfig {
            normalize_cert_terms: true,
            cert_simp,
            normalize_casts: true,
            coerce_nat: NatCoercionPolicy::LinearSafe,
            blocker_limit: 6,
            emit_telemetry: true,
        },
    }
}

/// Recommended tactic sequence names for a tactic domain profile.
pub const fn recommended_tactics(profile: TacticDomainProfile) -> &'static [&'static str] {
    profile.recommended_tactics()
}
