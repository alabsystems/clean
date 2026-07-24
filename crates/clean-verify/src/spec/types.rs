// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specification type definitions
//!
//! Core types for the kernel specification system.

use super::error::SpecError;
use clean_kernel::{Environment, Expr, Level};
use clean_parser::parse_expr;

/// A specification expression (clean surface syntax)
#[derive(Debug, Clone)]
pub struct SpecExpr {
    /// The source text
    pub source: String,
    /// Elaborated kernel expression (if successful)
    pub(crate) kernel_expr: Option<Expr>,
}

impl SpecExpr {
    /// Create a new specification expression from source
    #[must_use]
    pub fn new(source: &str) -> Self {
        SpecExpr {
            source: source.to_string(),
            kernel_expr: None,
        }
    }

    /// Returns the elaborated kernel expression, if available
    #[must_use]
    pub fn kernel_expr(&self) -> Option<&Expr> {
        self.kernel_expr.as_ref()
    }

    /// Elaborate the expression
    pub fn elaborate(&mut self, env: &Environment) -> Result<&Expr, SpecError> {
        if self.kernel_expr.is_none() {
            let surface =
                parse_expr(&self.source).map_err(|e| SpecError::ParseError(e.to_string()))?;
            let expr = clean_elab::elaborate(env, &surface)
                .map_err(|e| SpecError::ElabError(e.to_string()))?;
            self.kernel_expr = Some(expr);
        }
        Ok(self.kernel_expr.as_ref().unwrap())
    }
}

/// A specification level (clean universe level)
#[derive(Debug, Clone)]
pub struct SpecLevel {
    /// The source text
    pub source: String,
    /// Elaborated level (if applicable)
    pub(crate) level: Option<Level>,
}

impl SpecLevel {
    #[must_use]
    pub fn new(source: &str) -> Self {
        SpecLevel {
            source: source.to_string(),
            level: None,
        }
    }

    /// Returns the elaborated level, if available
    #[must_use]
    pub fn level(&self) -> Option<&Level> {
        self.level.as_ref()
    }

    /// Parse as a universe level
    pub fn parse(&mut self) -> Result<&Level, SpecError> {
        if self.level.is_none() {
            // Simple level parsing
            let level = match self.source.trim() {
                "0" | "Prop" => Level::Zero,
                "1" | "Type" => Level::succ(Level::Zero),
                s if s.starts_with("succ ") => {
                    let inner = s.strip_prefix("succ ").unwrap();
                    let mut inner_spec = SpecLevel::new(inner);
                    Level::succ(inner_spec.parse()?.clone())
                }
                _ => {
                    return Err(SpecError::ParseError(format!(
                        "Cannot parse level: {}",
                        self.source
                    )))
                }
            };
            self.level = Some(level);
        }
        Ok(self.level.as_ref().unwrap())
    }
}

/// Category of axioms for tracking which need constructive proofs
///
/// Per Phase 4 self-verification design, we distinguish:
/// - Foundational rules: Core type system that must be axioms
/// - Derived lemmas: Properties that should have constructive proofs
/// - Helper axioms: Intermediate results (may be replaced with derivations)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum AxiomCategory {
    /// Core typing rules that form the trusted base (e.g., sort_typing, pi_formation)
    FoundationalRule,
    /// Lemmas that should be derived from foundational rules (e.g., TypePreservation)
    DerivedLemma,
    /// Helper axioms used in proof construction (may eventually become derived)
    #[default]
    HelperAxiom,
}

/// Proof status for DerivedLemma definitions
///
/// This distinguishes between lemmas that are still axioms (pending proof),
/// lemmas with proofs that depend on helper axioms, and lemmas with fully
/// constructive proofs from the foundational base.
///
/// Part of #327: Phase 4 constructive proof tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum ProofStatus {
    /// No proof exists - the lemma is currently an axiom
    #[default]
    Axiom,
    /// Proof exists but depends on HelperAxiom definitions
    /// These are valid proofs but rely on axioms that should eventually be derived
    DerivedPending,
    /// Constructive proof that depends only on FoundationalRule axioms
    /// This is the goal state for all DerivedLemma definitions
    DerivedProved,
}

impl std::fmt::Display for ProofStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofStatus::Axiom => write!(f, "axiom"),
            ProofStatus::DerivedPending => write!(f, "pending"),
            ProofStatus::DerivedProved => write!(f, "proved"),
        }
    }
}

/// Trust level for Phase 4 self-verification Trusted Theory Base (TTB).
///
/// Per designs/2026-01-31-trusted-theory-base.md, definitions fall into one of:
/// - TrustedBase: Core axioms that form the TTB (foundational rules, inductive types)
/// - AxiomPending: Should be derived but currently axioms
/// - Derived: Has constructive proof term
///
/// Part of #425: Define explicit TTB assumptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Core TTB - irreducibly axiomatic (FoundationalRule and inductive types)
    TrustedBase,
    /// Should be derived but currently axiom (HelperAxiom that should become derived)
    #[default]
    AxiomPending,
    /// Has constructive proof term (is_axiom=false and value_src=Some)
    Derived,
}

impl std::fmt::Display for TrustLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TrustLevel::TrustedBase => write!(f, "TTB"),
            TrustLevel::AxiomPending => write!(f, "pending"),
            TrustLevel::Derived => write!(f, "derived"),
        }
    }
}
