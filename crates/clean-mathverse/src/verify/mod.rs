// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MathverseVerify trait — verification delegation API.

// Submodules consolidated under the `verify/` namespace. Callers reach these
// via their canonical paths: `crate::verify::foreign::`,
// `crate::verify::incremental::`, and `crate::verify::integration::`.
pub mod classify;
/// Content fingerprinting for re-import deduplication (the P1 cache key).
pub(crate) mod fingerprint;
pub mod foreign;
pub mod incremental;
pub mod integration;
pub mod kernel_verified_manifest;
/// Re-import verdict-cache population post-pass (P1 brick 3a).
#[cfg(test)]
pub(crate) mod reimport_cache_pass;
pub mod sharded;
/// Merkle trust receipt over a kernel-verified declaration set (P4).
pub mod trust_receipt;
/// Persistent verdict cache keyed by the Merkle-DAG verified hash (P1 brick 2).
#[cfg(test)]
pub(crate) mod verdict_cache;

use crate::error::MathverseResult;
use crate::graph_alpha::ConjectureSource;
use crate::nn_alpha::NNVerificationCert;
use crate::types::{ConjectureIdx, ConstantIdx, ExprIdx, ImportConfidence, SourceSystem};

/// Format of a foreign proof submitted for verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofFormat {
    /// Lean 4 .olean binary.
    OLean,
    /// Coq SerAPI s-expression.
    CoqSexp,
    /// Metamath .mm text.
    MetamathMm,
    /// OpenTheory .art format.
    OpenTheory,
    /// Alethe SMT proof.
    Alethe,
    /// LFSC SMT proof.
    Lfsc,
    /// TSTP ATP proof.
    Tstp,
    /// DRAT SAT certificate.
    Drat,
    /// LRAT SAT certificate.
    Lrat,
    /// gamma-crown JSON certificate.
    GammaCrownJson,
    /// VNN-COMP format.
    VnnComp,
}

/// Current verification status of a submitted proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationStatus {
    /// Not yet processed.
    Pending,
    /// Verified successfully by the kernel.
    Verified,
    /// Verification failed with the given reason.
    Failed(String),
    /// Verification timed out before completing.
    Timeout,
}

/// Result of verifying a foreign proof.
#[derive(Clone, Debug)]
pub struct VerificationResult {
    /// The constant index assigned in the library (if accepted).
    pub constant_idx: Option<ConstantIdx>,
    /// Source system detected.
    pub source: SourceSystem,
    /// Confidence level of the verification.
    pub confidence: ImportConfidence,
    /// Current verification status.
    pub status: VerificationStatus,
    /// Human-readable summary.
    pub summary: String,
}

/// Trust gate for training data export.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrustGate {
    /// Only KernelVerified theorems — safe for proof generation training.
    ProofGenEligible,
    /// KernelVerified + Translated — safe for premise selection.
    PremiseSelectEligible,
    /// All trust levels — statement-level data only.
    StatementOnly,
}

/// Training data export record.
#[derive(Clone, Debug)]
pub struct TrainingExport {
    pub name: String,
    pub type_expr: String,
    pub proof_sketch: Option<String>,
    pub source: SourceSystem,
    pub confidence: ImportConfidence,
    pub axiom_profile_bits: u64,
    pub deps: Vec<String>,
    pub trust_gate: TrustGate,
}

/// The verification delegation and submission API.
pub trait MathverseVerify {
    /// Verify a proof submitted in a foreign format.
    /// Translates, verifies via clean kernel, and stores if valid.
    fn verify_foreign(
        &mut self,
        format: ProofFormat,
        statement: &[u8],
        proof: &[u8],
    ) -> MathverseResult<VerificationResult>;

    /// Check if a statement is already proven in the library.
    fn is_known(&self, statement: ExprIdx) -> Option<ConstantIdx>;

    /// Submit a proven theorem (type + proof term) from an external prover.
    fn submit_proven(
        &mut self,
        name: &str,
        type_expr: ExprIdx,
        proof: ExprIdx,
        source: ConjectureSource,
    ) -> MathverseResult<ConstantIdx>;

    /// Submit a conjecture for the queue.
    fn submit_conjecture(
        &mut self,
        statement: ExprIdx,
        source: ConjectureSource,
    ) -> MathverseResult<ConjectureIdx>;

    /// Submit a neural network verification certificate.
    fn submit_nn_certificate(&mut self, cert: NNVerificationCert) -> MathverseResult<ConstantIdx>;
}

// ---------------------------------------------------------------------------
// Helpers: format enumeration and source-to-format mapping
// ---------------------------------------------------------------------------

/// All proof formats supported by the verification pipeline.
pub fn supported_formats() -> &'static [ProofFormat] {
    &[
        ProofFormat::OLean,
        ProofFormat::CoqSexp,
        ProofFormat::MetamathMm,
        ProofFormat::OpenTheory,
        ProofFormat::Alethe,
        ProofFormat::Lfsc,
        ProofFormat::Tstp,
        ProofFormat::Drat,
        ProofFormat::Lrat,
        ProofFormat::GammaCrownJson,
        ProofFormat::VnnComp,
    ]
}

/// Map a source proof system to its native proof format (if known).
///
/// Returns `None` for source systems that do not have a single canonical
/// proof format (e.g. Agda, Idris2, Dafny) or that produce proofs
/// which must be translated through intermediate representations.
pub fn format_for_source(source: SourceSystem) -> Option<ProofFormat> {
    match source {
        SourceSystem::Lean4 | SourceSystem::CleanNative => Some(ProofFormat::OLean),
        SourceSystem::Coq => Some(ProofFormat::CoqSexp),
        SourceSystem::Metamath => Some(ProofFormat::MetamathMm),
        SourceSystem::HolLight | SourceSystem::Hol4 => Some(ProofFormat::OpenTheory),
        SourceSystem::Z3 | SourceSystem::Cvc5 => Some(ProofFormat::Alethe),
        SourceSystem::Vampire => Some(ProofFormat::Tstp),
        SourceSystem::CaDiCaL => Some(ProofFormat::Lrat),
        SourceSystem::GammaCrown | SourceSystem::AlphaBetaCrown => {
            Some(ProofFormat::GammaCrownJson)
        }
        // Systems without a single canonical format.
        SourceSystem::Agda
        | SourceSystem::Idris2
        | SourceSystem::FStar
        | SourceSystem::Cedille
        | SourceSystem::Isabelle
        | SourceSystem::Mizar
        | SourceSystem::Dafny
        | SourceSystem::Why3
        | SourceSystem::Nuprl
        | SourceSystem::Pvs
        | SourceSystem::Acl2
        | SourceSystem::LiquidHaskell
        | SourceSystem::Key
        | SourceSystem::FramaC
        | SourceSystem::Spark
        | SourceSystem::Tlc
        | SourceSystem::KeyFramacSpark
        | SourceSystem::SmtSolver
        | SourceSystem::SatSolver
        | SourceSystem::Atp
        | SourceSystem::Arxiv
        | SourceSystem::Dedukti
        | SourceSystem::Lambdapi
        | SourceSystem::Abella
        | SourceSystem::Beluga
        | SourceSystem::Twelf
        | SourceSystem::Naproche
        | SourceSystem::Minlog
        | SourceSystem::Arend
        | SourceSystem::Mm0
        | SourceSystem::Kind2
        | SourceSystem::Rzk
        | SourceSystem::Ats2
        | SourceSystem::Latte
        | SourceSystem::CubicalTT
        | SourceSystem::Cooltt
        | SourceSystem::Redtt
        | SourceSystem::Verus
        | SourceSystem::Creusot
        | SourceSystem::Kani
        | SourceSystem::Prusti
        | SourceSystem::Aeneas
        | SourceSystem::Hax
        | SourceSystem::CreuSat
        | SourceSystem::Stainless
        | SourceSystem::Lisa
        | SourceSystem::MoveProver
        | SourceSystem::Boogie
        | SourceSystem::Viper
        | SourceSystem::VeriFast
        | SourceSystem::Sail
        | SourceSystem::KFramework
        | SourceSystem::Alloy
        | SourceSystem::PLang
        | SourceSystem::EthAct
        | SourceSystem::SvBenchmarks
        | SourceSystem::Matita
        | SourceSystem::Cake => None,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_supported_formats_includes_all_variants() {
        let formats = supported_formats();
        assert_eq!(formats.len(), 11);
        assert!(formats.contains(&ProofFormat::OLean));
        assert!(formats.contains(&ProofFormat::CoqSexp));
        assert!(formats.contains(&ProofFormat::MetamathMm));
        assert!(formats.contains(&ProofFormat::OpenTheory));
        assert!(formats.contains(&ProofFormat::Alethe));
        assert!(formats.contains(&ProofFormat::Lfsc));
        assert!(formats.contains(&ProofFormat::Tstp));
        assert!(formats.contains(&ProofFormat::Drat));
        assert!(formats.contains(&ProofFormat::Lrat));
        assert!(formats.contains(&ProofFormat::GammaCrownJson));
        assert!(formats.contains(&ProofFormat::VnnComp));
    }

    #[test]
    fn test_supported_formats_no_duplicates() {
        let formats = supported_formats();
        for (i, f) in formats.iter().enumerate() {
            for (j, g) in formats.iter().enumerate() {
                if i != j {
                    assert_ne!(f, g, "duplicate format at indices {i} and {j}");
                }
            }
        }
    }

    #[test]
    fn test_format_for_lean4() {
        assert_eq!(
            format_for_source(SourceSystem::Lean4),
            Some(ProofFormat::OLean)
        );
    }

    #[test]
    fn test_format_for_clean_native() {
        assert_eq!(
            format_for_source(SourceSystem::CleanNative),
            Some(ProofFormat::OLean)
        );
    }

    #[test]
    fn test_format_for_coq() {
        assert_eq!(
            format_for_source(SourceSystem::Coq),
            Some(ProofFormat::CoqSexp)
        );
    }

    #[test]
    fn test_format_for_metamath() {
        assert_eq!(
            format_for_source(SourceSystem::Metamath),
            Some(ProofFormat::MetamathMm)
        );
    }

    #[test]
    fn test_format_for_hol_systems() {
        assert_eq!(
            format_for_source(SourceSystem::HolLight),
            Some(ProofFormat::OpenTheory)
        );
        assert_eq!(
            format_for_source(SourceSystem::Hol4),
            Some(ProofFormat::OpenTheory)
        );
    }

    #[test]
    fn test_format_for_smt_solvers() {
        assert_eq!(
            format_for_source(SourceSystem::Z3),
            Some(ProofFormat::Alethe)
        );
        assert_eq!(
            format_for_source(SourceSystem::Cvc5),
            Some(ProofFormat::Alethe)
        );
    }

    #[test]
    fn test_format_for_atp_and_sat() {
        assert_eq!(
            format_for_source(SourceSystem::Vampire),
            Some(ProofFormat::Tstp)
        );
        assert_eq!(
            format_for_source(SourceSystem::CaDiCaL),
            Some(ProofFormat::Lrat)
        );
    }

    #[test]
    fn test_format_for_nn_tools() {
        assert_eq!(
            format_for_source(SourceSystem::GammaCrown),
            Some(ProofFormat::GammaCrownJson)
        );
        assert_eq!(
            format_for_source(SourceSystem::AlphaBetaCrown),
            Some(ProofFormat::GammaCrownJson)
        );
    }

    #[test]
    fn test_format_for_unmapped_systems_returns_none() {
        let unmapped = [
            SourceSystem::Agda,
            SourceSystem::Idris2,
            SourceSystem::FStar,
            SourceSystem::Cedille,
            SourceSystem::Isabelle,
            SourceSystem::Mizar,
            SourceSystem::Dafny,
            SourceSystem::Why3,
            SourceSystem::Nuprl,
            SourceSystem::Pvs,
            SourceSystem::Acl2,
            SourceSystem::LiquidHaskell,
            SourceSystem::Key,
            SourceSystem::FramaC,
            SourceSystem::Spark,
            SourceSystem::Tlc,
        ];
        for sys in unmapped {
            assert!(
                format_for_source(sys).is_none(),
                "{sys:?} should not have a canonical format"
            );
        }
    }

    #[test]
    fn test_verification_status_equality() {
        assert_eq!(VerificationStatus::Pending, VerificationStatus::Pending);
        assert_eq!(VerificationStatus::Verified, VerificationStatus::Verified);
        assert_eq!(VerificationStatus::Timeout, VerificationStatus::Timeout);
        assert_eq!(
            VerificationStatus::Failed("bad".into()),
            VerificationStatus::Failed("bad".into())
        );
        assert_ne!(VerificationStatus::Pending, VerificationStatus::Verified);
        assert_ne!(
            VerificationStatus::Failed("a".into()),
            VerificationStatus::Failed("b".into())
        );
    }

    #[test]
    fn test_verification_result_construction() {
        let result = VerificationResult {
            constant_idx: Some(42),
            source: SourceSystem::Lean4,
            confidence: ImportConfidence::KernelVerified,
            status: VerificationStatus::Verified,
            summary: "ok".into(),
        };
        assert_eq!(result.constant_idx, Some(42));
        assert_eq!(result.source, SourceSystem::Lean4);
        assert_eq!(result.confidence, ImportConfidence::KernelVerified);
        assert_eq!(result.status, VerificationStatus::Verified);
    }
}
