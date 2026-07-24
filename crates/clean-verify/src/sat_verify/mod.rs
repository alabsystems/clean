// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SAT Solver Verification Proof Engine
//!
//! Formalizes soundness proofs for SAT solver techniques used in ay (clean's
//! sister SAT/SMT solver). This module provides proof strategies and status
//! tracking for CDCL (Conflict-Driven Clause Learning), proof complexity
//! theory, and Craig interpolation.
//!
//! ## Architecture
//!
//! The proof engine is organized by verification domain:
//!
//! - [`cdcl`]: Abstract CDCL specification with invariants S01-S06, BCP
//!   (Boolean Constraint Propagation) implementation, and DIMACS CNF parsing.
//!
//! - [`proof_complexity`]: Proof system hierarchy including resolution and
//!   cutting planes, plus standard encodings (pigeonhole, Tseitin).
//!
//! - [`interpolation`]: Craig interpolation via McMillan's algorithm on
//!   resolution DAGs, with A/B partitioning and shared-variable extraction.
//!
//! - [`frontier`]: Beyond-resolution proof systems (polynomial calculus,
//!   Fourier-Motzkin, extension rule).
//!
//! ## Relationship to ay
//!
//! ay is the production SAT/SMT solver. This module formalizes the *proof
//! strategies* for SAT correctness -- proving that CDCL is sound, that
//! resolution proofs are valid, and that interpolants satisfy the Craig
//! property. ay implements these algorithms; this module proves they work.
//!
//! ## Cross-References
//!
//! - ay: production SAT/SMT solver that implements CDCL + proof logging
//! - Handbook of Satisfiability (Biere et al., 2021): reference for CDCL
//! - McMillan (2003): "Interpolation and SAT-Based Model Checking"

pub mod ay_contract;
pub mod ay_export;
pub mod ay_import;
pub mod cdcl;
pub mod cnf_core;
pub mod domain;
pub mod drat_to_lrat;
pub mod extended_resolution;
pub mod formula_stats;
pub mod frat;
pub mod frontier;
pub mod gamma_crown_sat;
pub mod gf2_polynomial;
pub mod hard_formulas;
pub mod interpolation;
pub mod lrat;
pub mod lrat_kernel_bridge;
pub mod mathverse_synthesis;
pub mod pipeline;
pub mod proof_checker;
pub mod proof_complexity;
pub mod proof_guided;
pub mod proof_system_core;
pub mod proof_trim;
pub mod pseudo_boolean;
pub mod replacement_evidence;
pub mod sat_comp;
pub mod types;

#[cfg(test)]
mod conformance_tests;
#[cfg(test)]
mod fuzz_tests;
#[cfg(test)]
mod fuzz_tests_proptest;
#[cfg(test)]
mod tests_lit_invariant;

use crate::spec::ProofStatus;

/// Theorem registry for SAT verification proof tracking.
///
/// Each theorem has an identifier (S-number for CDCL invariants, PC-number
/// for proof complexity, I-number for interpolation), a human description,
/// and a [`ProofStatus`] indicating current verification state.
#[derive(Debug, Clone)]
pub struct SatTheoremEntry {
    /// Theorem identifier (e.g., "S01", "PC01", "I01").
    pub id: &'static str,
    /// Human-readable description.
    pub description: &'static str,
    /// Current proof status.
    pub status: ProofStatus,
    /// Domain this theorem belongs to.
    pub domain: SatDomain,
}

/// Domain classification for SAT verification theorems.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SatDomain {
    /// CDCL solver correctness invariants.
    Cdcl,
    /// Proof complexity theory (resolution, cutting planes).
    ProofComplexity,
    /// Craig interpolation.
    Interpolation,
}

impl std::fmt::Display for SatDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SatDomain::Cdcl => write!(f, "CDCL"),
            SatDomain::ProofComplexity => write!(f, "Proof Complexity"),
            SatDomain::Interpolation => write!(f, "Interpolation"),
        }
    }
}

/// Return the full theorem registry for SAT verification proofs.
#[must_use]
pub fn theorem_registry() -> Vec<SatTheoremEntry> {
    let mut entries = Vec::with_capacity(14);
    entries.extend(cdcl_theorems());
    entries.extend(proof_complexity_theorems());
    entries.extend(interpolation_theorems());
    entries
}

fn pending(id: &'static str, desc: &'static str, domain: SatDomain) -> SatTheoremEntry {
    SatTheoremEntry {
        id,
        description: desc,
        status: ProofStatus::DerivedPending,
        domain,
    }
}

// NOTE: A `proved()` helper was removed here as part of #3361 (Phase 0: Stop
// Lying). The only legitimate path to DerivedProved is through the kernel
// promote pipeline (proofs/promote.rs). Hardcoding DerivedProved status
// bypasses verification.

fn cdcl_theorems() -> Vec<SatTheoremEntry> {
    vec![
        pending(
            "S01",
            "Trail consistency: no variable assigned twice",
            SatDomain::Cdcl,
        ),
        pending("S02", "Two-watched-literal invariant", SatDomain::Cdcl),
        pending(
            "S03",
            "Learned clause soundness: resolvent of existing clauses",
            SatDomain::Cdcl,
        ),
        pending(
            "S04",
            "Backtrack correctness: consistent prefix restored",
            SatDomain::Cdcl,
        ),
        pending(
            "S05",
            "Propagation completeness: BCP finds all unit-implied literals",
            SatDomain::Cdcl,
        ),
        pending(
            "S06",
            "Termination: CDCL terminates in finite steps",
            SatDomain::Cdcl,
        ),
    ]
}

fn proof_complexity_theorems() -> Vec<SatTheoremEntry> {
    vec![
        pending("PC01", "Resolution soundness", SatDomain::ProofComplexity),
        pending(
            "PC02",
            "Resolution completeness",
            SatDomain::ProofComplexity,
        ),
        pending(
            "PC03",
            "Cutting planes soundness",
            SatDomain::ProofComplexity,
        ),
        pending("PC04", "CP subsumes resolution", SatDomain::ProofComplexity),
    ]
}

fn interpolation_theorems() -> Vec<SatTheoremEntry> {
    vec![
        pending(
            "I01",
            "Craig interpolation existence",
            SatDomain::Interpolation,
        ),
        pending(
            "I02",
            "McMillan extraction from resolution DAG",
            SatDomain::Interpolation,
        ),
        pending(
            "I03",
            "Shared variables: Vars(I) subset Vars(A) & Vars(B)",
            SatDomain::Interpolation,
        ),
        pending(
            "I04",
            "Pudlak rule for shared pivots",
            SatDomain::Interpolation,
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::ProofStatus;

    #[test]
    fn test_sat_theorem_registry_completeness() {
        let registry = theorem_registry();
        assert_eq!(registry.len(), 14, "expected 14 theorems in registry");
    }

    #[test]
    fn test_sat_theorem_registry_status_distribution() {
        let registry = theorem_registry();
        let proved = registry
            .iter()
            .filter(|t| t.status == ProofStatus::DerivedProved)
            .count();
        let pending = registry
            .iter()
            .filter(|t| t.status == ProofStatus::DerivedPending)
            .count();
        assert_eq!(proved, 0, "no theorems should be DerivedProved");
        assert_eq!(pending, 14, "all 14 theorems should be DerivedPending");
        assert_eq!(proved + pending, registry.len());
    }

    #[test]
    fn test_sat_theorem_registry_domain_counts() {
        let registry = theorem_registry();
        let cdcl = registry
            .iter()
            .filter(|t| t.domain == SatDomain::Cdcl)
            .count();
        let pc = registry
            .iter()
            .filter(|t| t.domain == SatDomain::ProofComplexity)
            .count();
        let interp = registry
            .iter()
            .filter(|t| t.domain == SatDomain::Interpolation)
            .count();
        assert_eq!(cdcl, 6);
        assert_eq!(pc, 4);
        assert_eq!(interp, 4);
    }

    #[test]
    fn test_sat_theorem_ids_unique() {
        let registry = theorem_registry();
        let mut ids: Vec<&str> = registry.iter().map(|t| t.id).collect();
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), registry.len(), "theorem IDs must be unique");
    }

    #[test]
    fn test_sat_domain_display() {
        assert_eq!(SatDomain::Cdcl.to_string(), "CDCL");
        assert_eq!(SatDomain::ProofComplexity.to_string(), "Proof Complexity");
        assert_eq!(SatDomain::Interpolation.to_string(), "Interpolation");
    }
}
