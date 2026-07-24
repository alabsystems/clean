// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof Terms for Kernel Properties
//!
//! This module contains actual proof terms that witness kernel properties.
//! Each proof is a clean term that type-checks against a property's statement.
//!
//! ## Proof Structure
//!
//! Proofs are constructed using:
//! - Lambda abstraction for universal quantification
//! - Application for instantiation
//! - Axioms for base cases (typing rules)
//! - Recursors for induction
//!
//! ## Example
//!
//! The proof that definitional equality is reflexive:
//! ```text
//! def_eq_refl : (e : KExpr) -> DefEq e e
//! def_eq_refl = fun e => DefEq.refl e
//! ```

pub(crate) mod builder;
mod library;
mod library_arith_subst;
mod library_boolean_analysis;
mod library_cdcl_sat;
mod library_expr_structural;
mod library_gf2_sat;
mod library_impl_soundness_core;
mod library_impl_soundness_decomp;
mod library_impl_soundness_infer;
mod library_impl_soundness_infer_binder;
mod library_impl_soundness_misc;
mod library_interp_sat;
mod library_interval_arith;
mod library_micro;
mod library_pc_sat;
mod library_pg_sat;
mod library_simulation;
mod library_subst_micro_env;
mod library_type_checker_spec;
mod library_type_pres;
mod library_type_pres_cases;
mod library_type_preservation;
mod library_whnf_metatheory;
mod library_zonotope;
pub mod promote;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_dependency_audit;
#[cfg(test)]
mod tests_elaboration;
#[cfg(test)]
mod tests_promote;
#[cfg(test)]
mod tests_state_summary_bridge;
#[cfg(test)]
mod tests_type_preservation_chain;
mod verify;

use crate::spec::{ProofStatus, Specification};
use clean_kernel::Expr;
use std::collections::{HashMap, HashSet};

/// A proof term witnessing a property
#[derive(Debug, Clone)]
pub struct ProofTerm {
    /// Name of the property being proved
    pub property: String,
    /// The proof term as clean source
    pub proof_src: String,
    /// Source file where this proof was registered
    pub source_file: String,
    /// 1-based source line where this proof was registered
    pub source_line: u32,
    /// Elaborated proof (reserved for caching)
    pub(super) _elaborated: Option<Expr>,
    /// Human-readable explanation
    pub explanation: String,
}

/// Error during proof verification
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ProofError {
    /// Property name not found in the specification
    #[error("Unknown property: {0}")]
    UnknownProperty(String),
    /// Failed to parse the proof term source
    #[error("Parse error: {0}")]
    ParseError(String),
    /// Type elaboration failed for the proof term
    #[error("Elaboration error: {0}")]
    ElabError(String),
    /// Proof term type doesn't match the property type
    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch {
        /// The expected type from the property signature
        expected: String,
        /// The actual type inferred from the proof term
        actual: String,
    },
}

/// Result of dependency analysis for a single proof
///
/// Part of #326: Proof dependency audit
#[derive(Debug, Clone)]
pub struct DependencyResult {
    /// Computed proof status based on dependencies.
    /// Note: Only meaningful when `error` is `None`. When verification fails,
    /// this field is set to `DerivedPending` as a placeholder.
    pub status: ProofStatus,
    /// Set of HelperAxiom names this proof depends on (empty if error)
    pub axiom_deps: HashSet<String>,
    /// Error message if verification failed; `None` indicates success
    pub error: Option<String>,
}

/// Summary report of proof dependency audit
///
/// Part of #326: Proof dependency audit
#[derive(Debug, Default)]
pub struct DependencyAuditReport {
    /// Per-proof dependency results
    pub results: HashMap<String, DependencyResult>,
    /// Count of fully proved proofs (no axiom deps)
    pub fully_proved: usize,
    /// Count of pending proofs (have axiom deps)
    pub pending: usize,
    /// Count of foundational axioms (reserved - ProofLibrary only has proofs with terms)
    pub axioms: usize,
    /// Count of proofs that failed verification
    pub errors: usize,
}

impl DependencyAuditReport {
    /// Get proofs that depend on a specific axiom (sorted for deterministic output)
    #[must_use]
    pub fn proofs_depending_on(&self, axiom: &str) -> Vec<&str> {
        let mut proofs: Vec<&str> = self
            .results
            .iter()
            .filter(|(_, r)| r.axiom_deps.contains(axiom))
            .map(|(name, _)| name.as_str())
            .collect();
        proofs.sort();
        proofs
    }

    /// Get all unique axiom dependencies across all proofs
    #[must_use]
    pub fn all_axiom_deps(&self) -> HashSet<&str> {
        self.results
            .values()
            .flat_map(|r| r.axiom_deps.iter().map(|s| s.as_str()))
            .collect()
    }

    /// Generate summary text
    #[must_use]
    pub fn summary(&self) -> String {
        let total = self.fully_proved + self.pending + self.axioms + self.errors;
        format!(
            "Proof Dependency Audit:\n\
             - Total proofs: {}\n\
             - Fully proved: {}\n\
             - Pending (axiom deps): {}\n\
             - Axioms: {}\n\
             - Errors: {}\n\
             - Total axiom deps: {}",
            total,
            self.fully_proved,
            self.pending,
            self.axioms,
            self.errors,
            self.all_axiom_deps().len()
        )
    }
}

/// Library of proofs
#[derive(Debug)]
pub struct ProofLibrary {
    pub(super) proofs: HashMap<String, ProofTerm>,
}

impl ProofLibrary {
    /// Create library with available proofs
    #[must_use]
    pub fn new() -> Self {
        let mut lib = ProofLibrary {
            proofs: HashMap::new(),
        };

        lib.add_def_eq_proofs();
        lib.add_typing_proofs();
        lib.add_whnf_proofs();
        lib.add_termination_proofs();
        lib.add_expr_operation_proofs();
        lib.add_soundness_proofs();
        lib.add_type_preservation_proofs();
        lib.add_micro_checker_proofs();
        lib.add_forward_simulation_proofs();
        lib.add_implementation_soundness_proofs();
        lib.add_boolean_analysis_proofs();
        lib.add_cdcl_sat_proofs();
        lib.add_pc_sat_proofs();
        lib.add_interpolation_sat_proofs();
        lib.add_interval_arith_proofs();
        lib.add_gf2_sat_proofs();
        lib.add_pg_sat_proofs();
        lib.add_impl_soundness_core_proofs();
        lib.add_impl_soundness_decomp_proofs();
        lib.add_impl_soundness_infer_proofs();
        lib.add_impl_soundness_infer_binder_proofs();
        lib.add_type_pres_proofs();
        lib.add_type_pres_cases_proofs();
        lib.add_subst_micro_env_proofs();
        lib.add_type_checker_spec_proofs();
        lib.add_whnf_metatheory_proofs();
        lib.add_expr_structural_proofs();
        lib.add_arith_subst_proofs();
        lib.add_impl_soundness_misc_proofs();
        lib.add_zonotope_proofs();

        lib
    }

    /// Get all proofs
    pub fn all_proofs(&self) -> impl Iterator<Item = (&String, &ProofTerm)> {
        self.proofs.iter()
    }

    /// Get a specific proof
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&ProofTerm> {
        self.proofs.get(name)
    }

    /// Audit all proofs for axiom dependencies
    ///
    /// Returns a summary of proof dependency analysis:
    /// - Fully proved: proofs with no HelperAxiom dependencies
    /// - Pending: proofs that depend on HelperAxiom constants
    ///
    /// Part of #326: Proof dependency audit
    #[must_use]
    pub fn audit_dependencies(&self, spec: &Specification) -> DependencyAuditReport {
        let mut report = DependencyAuditReport::default();

        for (name, proof) in &self.proofs {
            match proof.verify_with_deps(spec) {
                Ok((status, deps)) => {
                    report.results.insert(
                        name.clone(),
                        DependencyResult {
                            status,
                            axiom_deps: deps,
                            error: None,
                        },
                    );
                    match status {
                        ProofStatus::DerivedProved => report.fully_proved += 1,
                        ProofStatus::DerivedPending => report.pending += 1,
                        ProofStatus::Axiom => report.axioms += 1,
                    }
                }
                Err(e) => {
                    report.results.insert(
                        name.clone(),
                        DependencyResult {
                            status: ProofStatus::DerivedPending,
                            axiom_deps: HashSet::new(),
                            error: Some(format!("{e}")),
                        },
                    );
                    report.errors += 1;
                }
            }
        }

        report
    }
}

impl Default for ProofLibrary {
    fn default() -> Self {
        Self::new()
    }
}
