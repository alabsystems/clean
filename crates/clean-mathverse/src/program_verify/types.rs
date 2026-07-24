// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core types for program verification condition import into the Mathverse Library.
//!
//! Defines unified representations for verification conditions (VCs) from
//! program verification tools like Dafny (via Boogie) and Why3 (via WhyML).
//! These types are the interchange format between parsers (`boogie.rs`,
//! `whyml.rs`) and the shard writer.

use serde::{Deserialize, Serialize};

use crate::types::{AxiomProfile, Provenance, SourceSystem, TrustLevel};

// ---------------------------------------------------------------------------
// Verification status
// ---------------------------------------------------------------------------

/// Status of a verification condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcStatus {
    /// The VC was proved by the solver.
    Proved,
    /// The solver could not determine the status.
    Unknown,
    /// The solver determined the VC is invalid (counterexample found).
    Failed,
}

// ---------------------------------------------------------------------------
// VcFormula — structured representation of VC assertions
// ---------------------------------------------------------------------------

/// Kind of a VC formula node.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum VcFormulaKind {
    /// Universal quantification: `forall vars. body`.
    Forall,
    /// Existential quantification: `exists vars. body`.
    Exists,
    /// Implication: `lhs => rhs`.
    Implies,
    /// Conjunction: `a /\ b /\ ...`.
    And,
    /// Disjunction: `a \/ b \/ ...`.
    Or,
    /// Negation: `not a`.
    Not,
    /// Equality: `a = b`.
    Eq,
    /// Less than: `a < b`.
    Lt,
    /// Less than or equal: `a <= b`.
    Le,
    /// Function application: `f(args...)`.
    FuncApp(String),
    /// Integer literal.
    IntLit(i64),
    /// Boolean literal.
    BoolLit(bool),
    /// Variable reference.
    Var(String),
}

/// A structured VC formula node with child sub-formulas.
///
/// Represents the AST of a verification condition. Each node has a kind
/// (operator/literal/variable) and zero or more child sub-formulas.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcFormula {
    /// The kind of this formula node.
    pub kind: VcFormulaKind,
    /// Child sub-formulas (empty for literals and variables).
    pub args: Vec<VcFormula>,
    /// Quantifier-bound variable names (non-empty only for Forall/Exists).
    pub bound_vars: Vec<String>,
}

impl VcFormula {
    /// Create a variable reference.
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self {
            kind: VcFormulaKind::Var(name.into()),
            args: Vec::new(),
            bound_vars: Vec::new(),
        }
    }

    /// Create an integer literal.
    #[must_use]
    pub fn int_lit(value: i64) -> Self {
        Self {
            kind: VcFormulaKind::IntLit(value),
            args: Vec::new(),
            bound_vars: Vec::new(),
        }
    }

    /// Create a boolean literal.
    #[must_use]
    pub fn bool_lit(value: bool) -> Self {
        Self {
            kind: VcFormulaKind::BoolLit(value),
            args: Vec::new(),
            bound_vars: Vec::new(),
        }
    }

    /// Create a negation.
    ///
    /// Constructor named `not` deliberately (matches the VC ADT vocabulary);
    /// this is not the `std::ops::Not` trait method.
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn not(inner: VcFormula) -> Self {
        Self {
            kind: VcFormulaKind::Not,
            args: vec![inner],
            bound_vars: Vec::new(),
        }
    }

    /// Create a conjunction from two or more formulas.
    #[must_use]
    pub fn and(args: Vec<VcFormula>) -> Self {
        Self {
            kind: VcFormulaKind::And,
            args,
            bound_vars: Vec::new(),
        }
    }

    /// Create a disjunction from two or more formulas.
    #[must_use]
    pub fn or(args: Vec<VcFormula>) -> Self {
        Self {
            kind: VcFormulaKind::Or,
            args,
            bound_vars: Vec::new(),
        }
    }

    /// Create an implication: `lhs => rhs`.
    #[must_use]
    pub fn implies(lhs: VcFormula, rhs: VcFormula) -> Self {
        Self {
            kind: VcFormulaKind::Implies,
            args: vec![lhs, rhs],
            bound_vars: Vec::new(),
        }
    }

    /// Create an equality: `lhs = rhs`.
    #[must_use]
    pub fn eq(lhs: VcFormula, rhs: VcFormula) -> Self {
        Self {
            kind: VcFormulaKind::Eq,
            args: vec![lhs, rhs],
            bound_vars: Vec::new(),
        }
    }

    /// Create a function application.
    #[must_use]
    pub fn func_app(name: impl Into<String>, args: Vec<VcFormula>) -> Self {
        Self {
            kind: VcFormulaKind::FuncApp(name.into()),
            args,
            bound_vars: Vec::new(),
        }
    }

    /// Count total nodes in this formula tree (including self).
    #[must_use]
    pub fn node_count(&self) -> usize {
        1 + self.args.iter().map(VcFormula::node_count).sum::<usize>()
    }
}

// ---------------------------------------------------------------------------
// VerificationCondition
// ---------------------------------------------------------------------------

/// A single verification condition from a program verification tool.
///
/// Represents one proof obligation generated by a tool like Dafny/Boogie
/// or Why3/WhyML. Each VC has a name, source location, structured formula,
/// and verification status.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct VerificationCondition {
    /// VC identifier (e.g., `"BinarySearch::postcondition::0"`).
    pub name: String,
    /// Source file path, if known.
    pub source_file: Option<String>,
    /// Source line number, if known.
    pub source_line: Option<u32>,
    /// Structured formula for the VC assertion.
    pub formula: VcFormula,
    /// Verification status.
    pub status: VcStatus,
}

// ---------------------------------------------------------------------------
// ProgramSpec — pre/post/invariant/decreases
// ---------------------------------------------------------------------------

/// A program specification consisting of contracts and annotations.
///
/// Represents the specification surface of a verified function or method:
/// preconditions, postconditions, loop invariants, and termination measures.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgramSpec {
    /// Precondition formulas (`requires` clauses).
    pub preconditions: Vec<VcFormula>,
    /// Postcondition formulas (`ensures` clauses).
    pub postconditions: Vec<VcFormula>,
    /// Loop invariant formulas.
    pub invariants: Vec<VcFormula>,
    /// Termination measure formulas (`decreases` clauses).
    pub decreases: Vec<VcFormula>,
}

impl ProgramSpec {
    /// Total number of specification clauses.
    #[must_use]
    pub fn clause_count(&self) -> usize {
        self.preconditions.len()
            + self.postconditions.len()
            + self.invariants.len()
            + self.decreases.len()
    }

    /// Whether this spec has any clauses.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clause_count() == 0
    }
}

// ---------------------------------------------------------------------------
// VcProofResult
// ---------------------------------------------------------------------------

/// Result of attempting to prove a single verification condition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcProofResult {
    /// Verification status.
    pub status: VcStatus,
    /// Solver time in milliseconds, if recorded.
    pub solver_time_ms: Option<u64>,
    /// Name of the solver used (e.g., `"Z3"`, `"Alt-Ergo"`).
    pub solver_used: Option<String>,
}

// ---------------------------------------------------------------------------
// ProgramVerifyStats
// ---------------------------------------------------------------------------

/// Aggregate statistics from a program verification session.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgramVerifyStats {
    /// Total number of verification conditions.
    pub total_vcs: usize,
    /// Number of VCs proved.
    pub proved: usize,
    /// Number of VCs that failed (counterexample found).
    pub failed: usize,
    /// Number of VCs with unknown status.
    pub unknown: usize,
}

impl ProgramVerifyStats {
    /// Compute statistics from a slice of verification conditions.
    #[must_use]
    pub fn from_vcs(vcs: &[VerificationCondition]) -> Self {
        let total_vcs = vcs.len();
        let proved = vcs
            .iter()
            .filter(|vc| vc.status == VcStatus::Proved)
            .count();
        let failed = vcs
            .iter()
            .filter(|vc| vc.status == VcStatus::Failed)
            .count();
        let unknown = vcs
            .iter()
            .filter(|vc| vc.status == VcStatus::Unknown)
            .count();
        Self {
            total_vcs,
            proved,
            failed,
            unknown,
        }
    }

    /// Fraction of VCs proved, in `[0.0, 1.0]`. Returns `1.0` for empty sets.
    #[must_use]
    pub fn success_rate(&self) -> f64 {
        if self.total_vcs == 0 {
            1.0
        } else {
            self.proved as f64 / self.total_vcs as f64
        }
    }
}

// ---------------------------------------------------------------------------
// Provenance / trust helpers
// ---------------------------------------------------------------------------

/// Axiom profile for a program verification VC entry in the Mathverse shard.
///
/// Program VCs are backed by SMT solvers, so they carry the `SMT_ORACLE`
/// axiom bit by default.
#[must_use]
pub fn program_vc_axiom_profile() -> AxiomProfile {
    AxiomProfile::SMT_ORACLE
}

/// Trust level for a program verification VC.
///
/// Proved VCs without certificate replay are `TrustedOracle` (the solver
/// said "valid" but we have no independent certificate). Unproved VCs
/// get `PartiallyAxiomatized` since the claim is asserted without proof.
#[must_use]
pub fn program_vc_trust_level(status: VcStatus) -> TrustLevel {
    match status {
        VcStatus::Proved => TrustLevel::TrustedOracle,
        VcStatus::Unknown | VcStatus::Failed => TrustLevel::PartiallyAxiomatized,
    }
}

/// Build a provenance record for a program verification VC.
#[must_use]
pub fn program_vc_provenance(source: SourceSystem, vc: &VerificationCondition) -> Provenance {
    Provenance {
        source,
        original_name: vc.name.clone(),
        source_file: vc.source_file.clone(),
        axiom_profile: program_vc_axiom_profile(),
    }
}
