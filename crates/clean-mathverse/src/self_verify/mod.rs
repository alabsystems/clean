// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-verification proofs for the Mathverse import pipeline.
//!
//! Provides a suite of runtime checks that validate structural invariants of
//! the import pipeline. Each proof constructs concrete data, performs an
//! operation, and checks that the result satisfies the expected property.
//!
//! # Proofs
//!
//! 1. **Codec roundtrip** — encode then decode `MathverseConstantHeader`, check equality
//! 2. **Hash consing** — structurally equal headers produce the same bytes
//! 3. **Topological order** — `child_idx < parent_idx` for all dependency refs
//! 4. **Axiom profile propagation** — `profile(T) = union(profile(dep) for dep in deps(T))`
//! 5. **Trust no leakage** — axiomatized cannot reach kernel-verified in default mode

mod proofs;

use serde::{Deserialize, Serialize};

pub use proofs::{
    verify_axiom_profile_propagation, verify_codec_roundtrip, verify_hash_consing,
    verify_topological_order, verify_trust_no_leakage,
};

use crate::types::{
    AxiomProfile, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of a single self-verification proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProofResult {
    /// Name of the proof.
    pub name: String,
    /// Whether the proof passed.
    pub passed: bool,
    /// Human-readable evidence or explanation.
    pub evidence: String,
}

/// Aggregate result of running all self-verification proofs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SelfVerifyResult {
    /// Individual proof results.
    pub proofs: Vec<ProofResult>,
    /// Number of proofs that passed.
    pub passed: usize,
    /// Number of proofs that failed.
    pub failed: usize,
    /// Whether all proofs passed.
    pub all_passed: bool,
}

impl SelfVerifyResult {
    /// Construct from a set of proof results.
    #[must_use]
    pub fn from_proofs(proofs: Vec<ProofResult>) -> Self {
        let passed = proofs.iter().filter(|p| p.passed).count();
        let failed = proofs.len() - passed;
        let all_passed = failed == 0;
        Self {
            proofs,
            passed,
            failed,
            all_passed,
        }
    }

    /// Return a human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let status = if self.all_passed { "PASS" } else { "FAIL" };
        let mut lines = vec![format!(
            "Self-verification {status}: {}/{} proofs passed",
            self.passed,
            self.proofs.len()
        )];
        for p in &self.proofs {
            let mark = if p.passed { "[OK]" } else { "[FAIL]" };
            lines.push(format!("  {mark} {}: {}", p.name, p.evidence));
        }
        lines.join("\n")
    }
}

// ---------------------------------------------------------------------------
// Helper: header construction (shared with proofs module)
// ---------------------------------------------------------------------------

pub(crate) fn make_kernel_header(
    name_idx: u32,
    type_idx: u32,
    value_idx: u32,
    profile: AxiomProfile,
) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::CleanNative as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: 0,
        decl_kind: crate::types::DeclKind::Theorem as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }
}

pub(crate) fn make_axiomatized_header(
    name_idx: u32,
    type_idx: u32,
    profile: AxiomProfile,
) -> MathverseConstantHeader {
    MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: 0,
        decl_kind: crate::types::DeclKind::Axiom as u8,
        axiom_profile: profile | AxiomProfile::AXIOMATIZED,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }
}

// ---------------------------------------------------------------------------
// Runner
// ---------------------------------------------------------------------------

/// Run all self-verification proofs and return aggregate results.
#[must_use]
pub fn run_all_self_verify() -> SelfVerifyResult {
    let proofs = vec![
        verify_codec_roundtrip(),
        verify_hash_consing(),
        verify_topological_order(),
        verify_axiom_profile_propagation(),
        verify_trust_no_leakage(),
    ];
    SelfVerifyResult::from_proofs(proofs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
