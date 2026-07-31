// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specification definition type
//!
//! The SpecDefinition struct represents a single definition in the kernel specification.

use clean_kernel::{CertificationAudit, CertificationIssue, Expr};
use std::collections::HashSet;

use super::types::{AxiomCategory, ProofStatus, TrustLevel};

/// Collect the direct declaration references carried by an elaborated value.
pub(crate) fn dependencies_from_value(value: &Expr) -> HashSet<String> {
    value
        .collect_constants()
        .into_iter()
        .map(|name| name.to_string())
        .collect()
}

/// Extract ordinary admitted-axiom/trust-marker debt named by the kernel's
/// strict certification audit.
///
/// Other blockers (for example an elided value, unchecked provenance, or a
/// dependency cycle), including a counterfeit canonical foundation, are
/// integrity failures and are not mislabeled as ordinary axiom dependencies.
pub(crate) fn certification_axiom_deps(audit: &CertificationAudit) -> HashSet<String> {
    audit
        .issues
        .iter()
        .filter_map(|issue| match issue {
            CertificationIssue::NonFoundationalAxiom { name }
            | CertificationIssue::TrustMarker { name } => Some(name.to_string()),
            _ => None,
        })
        .collect()
}

/// Render every strict-certification blocker that is not ordinary admitted
/// axiom/trust-marker debt.
pub(crate) fn certification_integrity_errors(audit: &CertificationAudit) -> Vec<String> {
    audit
        .issues
        .iter()
        .filter(|issue| {
            !matches!(
                issue,
                CertificationIssue::NonFoundationalAxiom { .. }
                    | CertificationIssue::TrustMarker { .. }
            )
        })
        .map(|issue| format!("{issue:?}"))
        .collect()
}

/// A specification definition
#[derive(Debug, Clone)]
pub struct SpecDefinition {
    /// Definition name
    pub name: String,
    /// Definition type (as clean source)
    pub type_src: String,
    /// Definition value (as clean source)
    pub value_src: Option<String>,
    /// Whether the live declaration is an axiom (has no value).
    ///
    /// Checked registration derives this flag from the elaborated value or
    /// existing kernel declaration; caller input is not authoritative.
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
    /// Dependency/provenance fence for the value/proof.
    ///
    /// After elaboration registration automatically unions in every constant
    /// actually referenced by the elaborated value. Callers may predeclare
    /// additional semantic/provenance edges, so this is a conservative
    /// superset rather than necessarily the minimal direct-reference set.
    /// `None` is retained for axioms or declarations with no value/fence.
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
