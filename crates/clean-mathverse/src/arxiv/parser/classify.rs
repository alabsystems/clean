// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The amsthm environment vocabulary and its kind classifiers.
//!
//! Two tables (the built-in theorem-like and definition-like environment
//! names) plus the two substring classifiers that map an environment's DISPLAY
//! name — which for `\newtheorem`-declared custom environments is whatever the
//! author wrote — onto a [`TheoremKind`] / [`DefinitionKind`]. Extraction in
//! [`super`] consults these in two places (custom-environment discovery and
//! per-environment kind assignment), so the vocabulary is factored out here to
//! keep the tables and the classifiers that must agree with them adjacent.

use crate::arxiv::types::{DefinitionKind, TheoremKind};

/// Standard amsthm-like theorem environments.
pub(super) const THEOREM_ENV_NAMES: &[&str] = &[
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "conjecture",
    "claim",
    "fact",
];

/// Standard definition-like environments.
pub(super) const DEFINITION_ENV_NAMES: &[&str] = &[
    "definition",
    "notation",
    "convention",
    "example",
    "remark",
    "assumption",
    "axiom",
];

/// Theorem kind display names (lowercase) to TheoremKind mapping.
pub(super) fn classify_theorem(name: &str) -> Option<TheoremKind> {
    let lower = name.to_lowercase();
    if lower.contains("theorem") {
        Some(TheoremKind::Theorem)
    } else if lower.contains("lemma") {
        Some(TheoremKind::Lemma)
    } else if lower.contains("proposition") {
        Some(TheoremKind::Proposition)
    } else if lower.contains("corollary") {
        Some(TheoremKind::Corollary)
    } else if lower.contains("conjecture") {
        Some(TheoremKind::Conjecture)
    } else if lower.contains("claim") {
        Some(TheoremKind::Claim)
    } else if lower.contains("fact") {
        Some(TheoremKind::Fact)
    } else {
        None
    }
}

pub(super) fn classify_definition(name: &str) -> Option<DefinitionKind> {
    let lower = name.to_lowercase();
    if lower.contains("definition") {
        Some(DefinitionKind::Definition)
    } else if lower.contains("notation") {
        Some(DefinitionKind::Notation)
    } else if lower.contains("convention") {
        Some(DefinitionKind::Convention)
    } else if lower.contains("example") {
        Some(DefinitionKind::Example)
    } else if lower.contains("remark") {
        Some(DefinitionKind::Remark)
    } else if lower.contains("assumption") || lower.contains("hypothesis") {
        Some(DefinitionKind::Assumption)
    } else if lower.contains("axiom") {
        Some(DefinitionKind::Axiom)
    } else {
        None
    }
}
