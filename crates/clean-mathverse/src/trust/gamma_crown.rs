// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust accounting for gamma-crown kernel declarations.
//!
//! Bridges the kernel-side axiom-audit classification
//! ([`clean_kernel::env::axiom_audit::ProofQuality`]) into the coarser Mathverse
//! trust model. Callers pass pre-extracted proof-quality data so this module
//! does not depend directly on the kernel type.
//!
//! # Classification tiers
//!
//! | Tier | Meaning | TrustLevel | AxiomProfile |
//! |------|---------|------------|--------------|
//! | Constructive | zero domain axioms | KernelVerified | NONE |
//! | Trusted | domain-axiom deps | AxiomDependent | NN_ABSTRACTION+inferred |
//! | Pending | sorry / unchecked | TrustedOracle | AXIOMATIZED |
//! | Axiom | not a theorem | PartiallyAxiomatized | AXIOMATIZED |

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, TrustLevel};

/// Extracted proof-quality classification mirrored from the kernel axiom audit.
///
/// Intentionally local to Mathverse so the trust bridge can operate on
/// pre-extracted data without importing the kernel type directly. A `From`
/// impl for [`clean_kernel::env::ProofQuality`] is provided for callers that
/// have access to kernel types.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofQuality {
    /// No domain-specific axiom dependencies.
    Constructive,
    /// Depends on one or more domain-specific axioms.
    AxiomDependent {
        /// Number of distinct domain-specific axioms.
        axiom_count: usize,
        /// Names of the domain-specific axioms.
        axioms: Vec<String>,
    },
    /// The declaration is not a theorem.
    NotATheorem,
    /// The declaration was not kernel-verified.
    Unchecked,
}

impl From<clean_kernel::env::ProofQuality> for ProofQuality {
    fn from(kernel_quality: clean_kernel::env::ProofQuality) -> Self {
        // `clean_kernel::env::ProofQuality` is `#[non_exhaustive]`. Any new
        // variant must map to a safe default here. `Unchecked` is the most
        // conservative classification (pending / sorry-equivalent).
        match kernel_quality {
            clean_kernel::env::ProofQuality::Constructive => Self::Constructive,
            clean_kernel::env::ProofQuality::AxiomDependent {
                axiom_count,
                axioms,
            } => Self::AxiomDependent {
                axiom_count,
                axioms: axioms.into_iter().map(|name| name.to_string()).collect(),
            },
            clean_kernel::env::ProofQuality::NotATheorem => Self::NotATheorem,
            clean_kernel::env::ProofQuality::Unchecked => Self::Unchecked,
            _ => Self::Unchecked,
        }
    }
}

/// Coarse trust classification for gamma-crown declarations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustClassification {
    /// Zero domain-specific axioms and fully proved.
    Constructive,
    /// Type-checked theorem with domain-axiom dependencies.
    Trusted,
    /// Unchecked or contains `sorry`.
    Pending,
    /// Axiom declaration rather than theorem.
    Axiom,
}

/// Trust summary for a single declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclarationTrustSummary {
    pub name: String,
    pub conjecture_id: Option<String>,
    pub classification: TrustClassification,
    pub domain_axiom_count: usize,
    pub domain_axioms: Vec<String>,
    pub axiom_profile: AxiomProfile,
    pub trust_level: TrustLevel,
    pub has_sorry: bool,
}

/// Per-conjecture aggregation of trust information.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConjectureSummary {
    pub conjecture_id: String,
    pub declarations: Vec<String>,
    pub constructive_count: usize,
    pub trusted_count: usize,
    pub pending_count: usize,
    pub axiom_count: usize,
    pub is_fully_constructive: bool,
    pub unique_domain_axioms: Vec<String>,
}

/// Whole-report summary across all gamma-crown declarations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GammaCrownTrustReport {
    pub conjecture_summaries: HashMap<String, ConjectureSummary>,
    pub all_declarations: Vec<DeclarationTrustSummary>,
    pub total_constructive: usize,
    pub total_trusted: usize,
    pub total_pending: usize,
    pub total_axioms: usize,
    pub total_domain_axioms: usize,
}

#[derive(Default)]
struct ConjectureAccumulator {
    declarations: Vec<String>,
    constructive_count: usize,
    trusted_count: usize,
    pending_count: usize,
    axiom_count: usize,
    unique_domain_axioms: HashSet<String>,
}

/// Classify a declaration using pre-extracted kernel proof-quality data.
#[must_use]
pub fn classify_declaration(
    name: &str,
    proof_quality: &ProofQuality,
    has_sorry: bool,
) -> DeclarationTrustSummary {
    let conjecture_id = extract_conjecture_id(name);
    let (domain_axiom_count, domain_axioms) = match proof_quality {
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            let normalized_axioms = normalized_axioms(axioms);
            let count = if normalized_axioms.is_empty() {
                *axiom_count
            } else {
                normalized_axioms.len()
            };
            (count, normalized_axioms)
        }
        _ => (0, Vec::new()),
    };

    let (classification, trust_level, axiom_profile) = match proof_quality {
        ProofQuality::NotATheorem => (
            TrustClassification::Axiom,
            TrustLevel::PartiallyAxiomatized,
            AxiomProfile::AXIOMATIZED,
        ),
        ProofQuality::Unchecked => (
            TrustClassification::Pending,
            TrustLevel::TrustedOracle,
            AxiomProfile::AXIOMATIZED,
        ),
        ProofQuality::Constructive if has_sorry => (
            TrustClassification::Pending,
            TrustLevel::TrustedOracle,
            AxiomProfile::AXIOMATIZED,
        ),
        ProofQuality::AxiomDependent { .. } if has_sorry => (
            TrustClassification::Pending,
            TrustLevel::TrustedOracle,
            AxiomProfile::AXIOMATIZED,
        ),
        ProofQuality::Constructive => (
            TrustClassification::Constructive,
            TrustLevel::KernelVerified,
            AxiomProfile::NONE,
        ),
        ProofQuality::AxiomDependent { .. } => (
            TrustClassification::Trusted,
            TrustLevel::AxiomDependent,
            inferred_axiom_profile(&domain_axioms, domain_axiom_count > 0),
        ),
    };

    DeclarationTrustSummary {
        name: name.to_owned(),
        conjecture_id,
        classification,
        domain_axiom_count,
        domain_axioms,
        axiom_profile,
        trust_level,
        has_sorry,
    }
}

/// Build an aggregate trust report from declaration summaries.
#[must_use]
pub fn build_trust_report(declarations: &[DeclarationTrustSummary]) -> GammaCrownTrustReport {
    let mut conjecture_accumulators: HashMap<String, ConjectureAccumulator> = HashMap::new();
    let mut distinct_domain_axioms = HashSet::new();
    let mut all_declarations = declarations.to_vec();
    let mut total_constructive = 0usize;
    let mut total_trusted = 0usize;
    let mut total_pending = 0usize;
    let mut total_axioms = 0usize;

    all_declarations.sort_by(|left, right| left.name.cmp(&right.name));

    for declaration in &all_declarations {
        match declaration.classification {
            TrustClassification::Constructive => total_constructive += 1,
            TrustClassification::Trusted => total_trusted += 1,
            TrustClassification::Pending => total_pending += 1,
            TrustClassification::Axiom => total_axioms += 1,
        }

        declaration.domain_axioms.iter().cloned().for_each(|axiom| {
            distinct_domain_axioms.insert(axiom);
        });

        if declaration.classification == TrustClassification::Axiom {
            distinct_domain_axioms.insert(declaration.name.clone());
        }

        if let Some(conjecture_id) = declaration.conjecture_id.as_ref() {
            let accumulator = conjecture_accumulators
                .entry(conjecture_id.clone())
                .or_default();
            accumulator.declarations.push(declaration.name.clone());
            match declaration.classification {
                TrustClassification::Constructive => accumulator.constructive_count += 1,
                TrustClassification::Trusted => accumulator.trusted_count += 1,
                TrustClassification::Pending => accumulator.pending_count += 1,
                TrustClassification::Axiom => accumulator.axiom_count += 1,
            }
            declaration.domain_axioms.iter().cloned().for_each(|axiom| {
                accumulator.unique_domain_axioms.insert(axiom);
            });
            if declaration.classification == TrustClassification::Axiom {
                accumulator
                    .unique_domain_axioms
                    .insert(declaration.name.clone());
            }
        }
    }

    let conjecture_summaries = conjecture_accumulators
        .into_iter()
        .map(|(conjecture_id, mut accumulator)| {
            accumulator.declarations.sort();
            let mut unique_domain_axioms: Vec<_> =
                accumulator.unique_domain_axioms.into_iter().collect();
            unique_domain_axioms.sort();

            let summary = ConjectureSummary {
                conjecture_id: conjecture_id.clone(),
                declarations: accumulator.declarations,
                constructive_count: accumulator.constructive_count,
                trusted_count: accumulator.trusted_count,
                pending_count: accumulator.pending_count,
                axiom_count: accumulator.axiom_count,
                is_fully_constructive: accumulator.trusted_count == 0
                    && accumulator.pending_count == 0
                    && accumulator.axiom_count == 0
                    && accumulator.constructive_count > 0,
                unique_domain_axioms,
            };

            (conjecture_id, summary)
        })
        .collect();

    GammaCrownTrustReport {
        conjecture_summaries,
        all_declarations,
        total_constructive,
        total_trusted,
        total_pending,
        total_axioms,
        total_domain_axioms: distinct_domain_axioms.len(),
    }
}

/// Format a trust report as human-readable Markdown.
#[must_use]
pub fn format_trust_report(report: &GammaCrownTrustReport) -> String {
    let total_declarations = report.all_declarations.len();
    let mut markdown = String::new();

    markdown.push_str("# Gamma-Crown Trust Report\n\n");
    markdown.push_str("## Summary\n\n");
    markdown.push_str(&format!("- Total declarations: {total_declarations}\n"));
    markdown.push_str(&format!("- Constructive: {}\n", report.total_constructive));
    markdown.push_str(&format!("- Trusted: {}\n", report.total_trusted));
    markdown.push_str(&format!("- Pending: {}\n", report.total_pending));
    markdown.push_str(&format!("- Axioms: {}\n", report.total_axioms));
    markdown.push_str(&format!(
        "- Distinct domain axioms: {}\n",
        report.total_domain_axioms
    ));

    markdown.push_str("\n## Conjectures\n\n");
    if report.conjecture_summaries.is_empty() {
        markdown.push_str("_No conjectures found._\n");
    } else {
        let mut conjecture_ids: Vec<_> = report.conjecture_summaries.keys().cloned().collect();
        conjecture_ids.sort();

        for conjecture_id in conjecture_ids {
            if let Some(summary) = report.conjecture_summaries.get(&conjecture_id) {
                let status = if summary.is_fully_constructive {
                    "Fully constructive"
                } else {
                    "Mixed trust"
                };
                let unique_domain_axioms = if summary.unique_domain_axioms.is_empty() {
                    "none".to_owned()
                } else {
                    summary
                        .unique_domain_axioms
                        .iter()
                        .map(|axiom| format!("`{axiom}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                let declarations = summary
                    .declarations
                    .iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(", ");

                markdown.push_str(&format!("### {}\n\n", summary.conjecture_id));
                markdown.push_str(&format!("- Status: {status}\n"));
                markdown.push_str(&format!("- Declarations: {declarations}\n"));
                markdown.push_str(&format!(
                    "- Counts: constructive {}, trusted {}, pending {}, axioms {}\n",
                    summary.constructive_count,
                    summary.trusted_count,
                    summary.pending_count,
                    summary.axiom_count
                ));
                markdown.push_str(&format!("- Domain axioms: {unique_domain_axioms}\n\n"));
            }
        }
    }

    markdown.push_str("## Declarations\n\n");
    if report.all_declarations.is_empty() {
        markdown.push_str("_No declarations analyzed._\n");
        return markdown;
    }

    markdown.push_str(
        "| Declaration | Conjecture | Classification | Trust Level | Axiom Profile | Domain Axioms | Sorry |\n",
    );
    markdown.push_str("| --- | --- | --- | --- | --- | ---: | --- |\n");

    for declaration in &report.all_declarations {
        let conjecture = declaration
            .conjecture_id
            .as_deref()
            .map(|id| format!("`{id}`"))
            .unwrap_or_else(|| "-".to_owned());
        markdown.push_str(&format!(
            "| `{}` | {} | {} | `{}` | `{}` | {} | {} |\n",
            declaration.name,
            conjecture,
            declaration.classification.as_str(),
            trust_level_name(declaration.trust_level),
            format_axiom_profile(declaration.axiom_profile),
            declaration.domain_axiom_count,
            if declaration.has_sorry { "yes" } else { "no" }
        ));

        if !declaration.domain_axioms.is_empty() {
            let details = declaration
                .domain_axioms
                .iter()
                .map(|axiom| format!("`{axiom}`"))
                .collect::<Vec<_>>()
                .join(", ");
            markdown.push_str(&format!("|  |  |  |  |  | _{details}_ |  |\n"));
        }
    }

    markdown
}

fn extract_conjecture_id(name: &str) -> Option<String> {
    name.split('.')
        .find_map(parse_conjecture_token)
        .or_else(|| {
            name.split(|ch: char| !ch.is_ascii_alphanumeric())
                .find_map(parse_conjecture_token)
        })
}

fn parse_conjecture_token(token: &str) -> Option<String> {
    let mut chars = token.chars();
    if chars.next()? != 'C' {
        return None;
    }

    let digits: String = chars.take_while(|ch| ch.is_ascii_digit()).collect();
    if digits.len() < 3 {
        return None;
    }

    Some(format!("C{digits}"))
}

fn normalized_axioms(axioms: &[String]) -> Vec<String> {
    let mut normalized: Vec<_> = axioms
        .iter()
        .filter_map(|axiom| {
            let trimmed = axiom.trim();
            (!trimmed.is_empty()).then(|| trimmed.to_owned())
        })
        .collect();
    normalized.sort();
    normalized.dedup();
    normalized
}

fn inferred_axiom_profile(domain_axioms: &[String], has_domain_axioms: bool) -> AxiomProfile {
    let mut profile = AxiomProfile::NONE;

    if has_domain_axioms {
        profile |= AxiomProfile::NN_ABSTRACTION;
    }

    for axiom in domain_axioms.iter().map(|name| name.to_ascii_lowercase()) {
        if ["float", "round", "approx", "interval", "epsilon", "eps"]
            .iter()
            .any(|needle| axiom.contains(needle))
        {
            profile |= AxiomProfile::FLOAT_APPROX;
        }

        if ["real", "rat", "exp"]
            .iter()
            .any(|needle| axiom.contains(needle))
        {
            profile |= AxiomProfile::REAL_AXIOMS;
        }

        if ["lp", "lra", "linear", "dual", "farkas", "milp"]
            .iter()
            .any(|needle| axiom.contains(needle))
        {
            profile |= AxiomProfile::LRA_TRUSTED;
        }

        if ["bridge", "embedding"]
            .iter()
            .any(|needle| axiom.contains(needle))
        {
            profile |= AxiomProfile::BRIDGE_AXIOM;
        }
    }

    profile
}

fn format_axiom_profile(profile: AxiomProfile) -> String {
    let known_flags = [
        (AxiomProfile::CHOICE, "CHOICE"),
        (AxiomProfile::LEM, "LEM"),
        (AxiomProfile::PROP_EXT, "PROP_EXT"),
        (AxiomProfile::FUNC_EXT, "FUNC_EXT"),
        (AxiomProfile::QUOT, "QUOT"),
        (AxiomProfile::UNIVALENCE, "UNIVALENCE"),
        (AxiomProfile::LARGE_ELIM, "LARGE_ELIM"),
        (AxiomProfile::HOL_AXIOMS, "HOL_AXIOMS"),
        (AxiomProfile::MIZAR_TG, "MIZAR_TG"),
        (AxiomProfile::UNIVERSE_INCON, "UNIVERSE_INCON"),
        (AxiomProfile::AXIOMATIZED, "AXIOMATIZED"),
        (AxiomProfile::BRIDGE_AXIOM, "BRIDGE_AXIOM"),
        (AxiomProfile::REAL_AXIOMS, "REAL_AXIOMS"),
        (AxiomProfile::LRA_TRUSTED, "LRA_TRUSTED"),
        (AxiomProfile::FLOAT_APPROX, "FLOAT_APPROX"),
        (AxiomProfile::NN_ABSTRACTION, "NN_ABSTRACTION"),
        (AxiomProfile::COQ_SPROP, "COQ_SPROP"),
        (AxiomProfile::COQ_MODULE_FUNCTOR, "COQ_MODULE_FUNCTOR"),
        (AxiomProfile::COQ_COINDUCTIVE, "COQ_COINDUCTIVE"),
        (AxiomProfile::ISABELLE_LCF_ERASED, "ISABELLE_LCF_ERASED"),
        (AxiomProfile::AGDA_CUBICAL, "AGDA_CUBICAL"),
        (AxiomProfile::IDRIS_QTT, "IDRIS_QTT"),
        (AxiomProfile::SMT_ORACLE, "SMT_ORACLE"),
        (AxiomProfile::SAT_CERT, "SAT_CERT"),
        (AxiomProfile::ATP_CERT, "ATP_CERT"),
        (AxiomProfile::ARXIV_NL_IMPORT, "ARXIV_NL_IMPORT"),
    ];

    let names: Vec<_> = known_flags
        .into_iter()
        .filter_map(|(flag, name)| profile.has(flag).then_some(name))
        .collect();

    if names.is_empty() {
        "NONE".to_owned()
    } else {
        names.join(" | ")
    }
}

fn trust_level_name(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::KernelVerified => "KernelVerified",
        TrustLevel::AxiomDependent => "AxiomDependent",
        TrustLevel::CertificateReplayed => "CertificateReplayed",
        TrustLevel::PartiallyAxiomatized => "PartiallyAxiomatized",
        TrustLevel::TrustedOracle => "TrustedOracle",
    }
}

impl TrustClassification {
    /// Short human-readable name for this classification.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Constructive => "Constructive",
            Self::Trusted => "Trusted",
            Self::Pending => "Pending",
            Self::Axiom => "Axiom",
        }
    }
}

// ---------------------------------------------------------------------------
// Tests — extracted to gamma_crown_trust_tests.rs (#3379) to keep this
// file under the 500-line production cap.
// ---------------------------------------------------------------------------

#[cfg(test)]
#[path = "gamma_crown_tests.rs"]
mod gamma_crown_tests;
