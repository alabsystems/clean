// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specification definition type
//!
//! The SpecDefinition struct represents a single definition in the kernel specification.

use clean_kernel::Expr;
use std::collections::HashSet;

use super::types::{AxiomCategory, ProofStatus, TrustLevel};

/// A specification definition
#[derive(Debug, Clone)]
pub struct SpecDefinition {
    /// Definition name
    pub name: String,
    /// Definition type (as clean source)
    pub type_src: String,
    /// Definition value (as clean source)
    pub value_src: Option<String>,
    /// Whether this is an axiom (no value)
    pub is_axiom: bool,
    /// Category of this axiom/theorem for Phase 4 tracking
    pub category: AxiomCategory,
    /// Proof status for DerivedLemma (Part of #327)
    /// Defaults to Axiom for non-DerivedLemma definitions.
    pub proof_status: ProofStatus,
    /// Description
    pub description: String,
    /// Elaborated type (cached)
    pub elaborated_type: Option<Expr>,
    /// Elaborated value (cached)
    pub elaborated_value: Option<Expr>,
    /// Constants referenced in the value/proof (computed after elaboration)
    /// None if not yet computed or for axioms (no value)
    /// Part of #326: Proof dependency audit
    pub dependencies: Option<HashSet<String>>,
    /// HelperAxiom constants this depends on (transitive closure)
    /// Empty if fully constructive (no helper axiom dependencies)
    /// Part of #326: Proof dependency audit
    pub axiom_deps: HashSet<String>,
}

impl SpecDefinition {
    /// Compute trust level from category, is_axiom, and value_src.
    ///
    /// Per designs/2026-01-31-trusted-theory-base.md:
    /// - TrustedBase: FoundationalRule and inductive types (primitive constructs)
    /// - AxiomPending: HelperAxiom or DerivedLemma that should be derived
    /// - Derived: Has value_src (constructive proof)
    ///
    /// Part of #425: Define explicit TTB assumptions.
    #[must_use]
    pub fn trust_level(&self) -> TrustLevel {
        if self.category == AxiomCategory::FoundationalRule {
            return TrustLevel::TrustedBase;
        }
        match self.proof_status {
            ProofStatus::DerivedProved => TrustLevel::Derived,
            ProofStatus::DerivedPending | ProofStatus::Axiom => TrustLevel::AxiomPending,
        }
    }
}
