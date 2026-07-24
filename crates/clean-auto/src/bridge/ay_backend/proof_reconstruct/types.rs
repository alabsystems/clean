// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind, FVarId};
use hashbrown::HashMap;
use thiserror::Error;

use crate::bridge::ay_backend::reconstruction_quality::{
    ResidualTrustSource, ResidualTrustSummary,
};

/// Errors during proof reconstruction.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum ReconstructionError {
    /// A ay variable name could not be mapped to a kernel FVar.
    #[error("unknown variable: {name}")]
    UnknownVariable { name: String },

    /// A ay term could not be translated to a kernel expression.
    #[error("unsupported term: {description}")]
    UnsupportedTerm { description: String },

    /// A proof step type is not yet supported for reconstruction.
    #[error("unsupported proof step at index {step_index}: {description}")]
    UnsupportedStep {
        step_index: u32,
        description: String,
    },

    /// Reconstruction reached a soundness boundary where continuing would
    /// require a bridge-owned trust axiom.
    #[error("trust boundary at step {step_index} in {subsystem}: {description}")]
    TrustBoundary {
        step_index: u32,
        subsystem: &'static str,
        description: String,
    },

    /// The proof does not derive the empty clause (no contradiction).
    #[error("proof does not derive empty clause (final step has {literal_count} literals)")]
    NoContradiction { literal_count: usize },

    /// A premise reference is invalid (out of bounds or not yet resolved).
    #[error("invalid premise reference: step {premise} referenced from step {from_step}")]
    InvalidPremise { premise: u32, from_step: u32 },

    /// Proof object not available (resolution needs proof set via reconstruct()).
    #[error("proof object not available for resolution reconstruction")]
    ProofNotAvailable,

    /// Compound witness count exceeded the sentinel FVarId range.
    #[error("sentinel range exhausted: {witness_count} compound witnesses exceed limit")]
    SentinelRangeExhausted { witness_count: u32 },

    /// A non-pivot literal has no corresponding position in the resolvent clause.
    #[error("missing resolvent position for literal at index {literal_index} in step {step_id}")]
    MissingResolventPosition { literal_index: usize, step_id: u32 },

    /// The proof object contains zero steps.
    #[error("empty proof")]
    EmptyProof,
}

/// Result type for reconstruction operations.
pub(crate) type ReconstructResult<T> = Result<T, ReconstructionError>;

impl ReconstructionError {
    pub(crate) fn trust_boundary(
        step_index: u32,
        subsystem: &'static str,
        description: impl Into<String>,
    ) -> Self {
        Self::TrustBoundary {
            step_index,
            subsystem,
            description: description.into(),
        }
    }
}

/// A typed diagnostic preserving both the reconstruction error and its
/// occurrence metadata (step index for per-step failures, `None` for
/// proof-level failures such as `EmptyProof` or `NoContradiction`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReconstructionDiagnostic {
    pub(crate) step_index: Option<u32>,
    pub(crate) error: ReconstructionError,
}

impl ReconstructionDiagnostic {
    pub(crate) fn step(step_index: u32, error: ReconstructionError) -> Self {
        Self {
            step_index: Some(step_index),
            error,
        }
    }

    pub(crate) fn proof_level(error: ReconstructionError) -> Self {
        Self {
            step_index: None,
            error,
        }
    }
}

impl std::fmt::Display for ReconstructionDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(idx) = self.step_index {
            write!(f, "step {}: {}", idx, self.error)
        } else {
            write!(f, "{}", self.error)
        }
    }
}

/// Result of attempting proof reconstruction.
#[derive(Debug)]
pub(crate) struct ReconstructionResult {
    /// The reconstructed kernel proof term, if successful.
    ///
    /// When `Some`, this is a proof of the original goal type that should
    /// type-check in the kernel. When `None`, the caller should fall back
    /// to `trustedAy`.
    pub proof_term: Option<Expr>,

    /// FVarId of the negated-goal assumption proof, if one was introduced.
    ///
    /// When the proof uses proof-by-contradiction, the negated goal is assumed
    /// as a hypothesis with a fresh FVar. The caller must lambda-abstract this
    /// FVar to close the proof: `fun (h : ¬G) => <proof_term>` where `h` is
    /// bound to this FVarId.
    pub negated_goal_fvar: Option<FVarId>,

    /// FVarIds of compound witness assumptions that are unbound in the proof term.
    ///
    /// These arise when ay assumes a proposition that doesn't match any registered
    /// hypothesis or the negated goal. Each entry is (FVarId, assumed_proposition).
    /// A non-empty list indicates the proof term contains free variables and is
    /// NOT a valid closed proof — the caller should reject it.
    pub compound_witness_fvars: Vec<(FVarId, Expr)>,

    /// Whether the selected reconstruction root derives the empty clause.
    ///
    /// A complete UNSAT proof must reach an empty clause. When `false`, the
    /// proof may be partial or malformed — the caller should reject the
    /// proof_term in TrustSolver mode (where kernel type-checking is skipped).
    pub derives_empty_clause: bool,

    /// Number of proof steps that used trustedAy sub-terms.
    ///
    /// When > 0, the proof term contains `trustedAy` axiom applications for
    /// clauses that ay asserted without SAT-level proof (Trust steps). The
    /// remaining steps are kernel-verified. The caller can use this count
    /// to decide whether the partial verification is acceptable.
    pub trust_subterm_count: usize,

    /// Structured source classification for the reachable trusted sub-terms in
    /// `proof_term`.
    pub residual: ResidualTrustSummary,

    /// Statistics about the reconstruction attempt.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) stats: ReconstructionStats,
}

/// Statistics from a reconstruction attempt.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Default)]
pub(crate) struct ReconstructionStats {
    /// Total number of proof steps in the ay proof.
    pub(crate) total_steps: usize,
    /// Number of steps successfully reconstructed.
    pub(crate) reconstructed_steps: usize,
    /// Number of `Assume` steps.
    pub(crate) assume_steps: usize,
    /// Number of `Resolution` steps.
    pub(crate) resolution_steps: usize,
    /// Number of `TheoryLemma` steps.
    pub(crate) theory_lemma_steps: usize,
    /// Number of generic `Step` steps.
    pub(crate) generic_steps: usize,
    /// Number of steps that fell back to trust.
    pub(crate) trust_fallback_steps: usize,
    /// Number of steps rejected at a typed trust boundary.
    pub(crate) trust_boundary_steps: usize,
    /// Number of synthesized trust sub-terms caused by arithmetic boundaries.
    pub(crate) arithmetic_boundary_steps: usize,
    /// Number of explicit `AletheRule::Trust` steps.
    pub(crate) alethe_trust_steps: usize,
    /// Number of trust-only `BvBitBlast` theory lemmas.
    pub(crate) theory_bv_bitblast_steps: usize,
    /// Number of trust-only `ArrayAxiom` theory lemmas.
    pub(crate) theory_array_axiom_steps: usize,
    /// Number of trust-only `Generic` theory lemmas.
    pub(crate) theory_generic_steps: usize,
    /// Number of synthesized trust sub-terms caused by non-inherent local gaps.
    pub(crate) local_gap_steps: usize,
    /// Number of trust-carrying steps filled with trustedAy sub-terms.
    ///
    /// Unlike `trust_fallback_steps` (which counts error fallbacks), this counts
    /// steps that were *successfully* handled by synthesizing a trustedAy axiom
    /// application for the clause type. This includes explicit `Trust` steps
    /// and trust-only theory lemmas such as `BvBitBlast` / `ArrayAxiom`.
    /// Downstream steps referencing these premises can reconstruct normally,
    /// producing a partially-verified proof.
    pub(crate) trust_subterm_steps: usize,
    /// Typed diagnostic for the most recent (last) reconstruction failure.
    pub(crate) last_diagnostic: Option<ReconstructionDiagnostic>,
    /// Typed diagnostic for the first reconstruction failure encountered.
    pub(crate) first_diagnostic: Option<ReconstructionDiagnostic>,
    /// Specific error that prevented full reconstruction, if any.
    /// Compatibility mirror — derived from `last_diagnostic`.
    pub(crate) error: Option<String>,
    /// First error encountered during reconstruction: (step_index, error_description).
    /// Compatibility mirror — derived from `first_diagnostic`.
    pub(crate) first_error: Option<(u32, String)>,
    /// Per-AletheRule attempt counts (key = rule name from `AletheRule::name()`).
    pub(crate) rule_attempts: HashMap<String, usize>,
    /// Per-AletheRule success counts.
    pub(crate) rule_successes: HashMap<String, usize>,
}

impl ReconstructionStats {
    pub(crate) fn record_step_error(&mut self, step_index: u32, error: ReconstructionError) {
        let diagnostic = ReconstructionDiagnostic::step(step_index, error);
        if self.first_diagnostic.is_none() {
            self.first_error = Some((step_index, diagnostic.error.to_string()));
            self.first_diagnostic = Some(diagnostic.clone());
        }
        self.error = Some(format!("step {}: {}", step_index, diagnostic.error));
        self.last_diagnostic = Some(diagnostic);
    }

    pub(crate) fn record_proof_error(&mut self, error: ReconstructionError) {
        let diagnostic = ReconstructionDiagnostic::proof_level(error);
        if self.first_diagnostic.is_none() {
            self.first_error = None;
            self.first_diagnostic = Some(diagnostic.clone());
        }
        self.error = Some(diagnostic.error.to_string());
        self.last_diagnostic = Some(diagnostic);
    }

    pub(crate) fn record_residual_source(&mut self, source: ResidualTrustSource) {
        match source {
            ResidualTrustSource::ArithmeticBoundary => self.arithmetic_boundary_steps += 1,
            ResidualTrustSource::AletheTrustStep => self.alethe_trust_steps += 1,
            ResidualTrustSource::TheoryLemmaBvBitBlast => self.theory_bv_bitblast_steps += 1,
            ResidualTrustSource::TheoryLemmaArrayAxiom => self.theory_array_axiom_steps += 1,
            ResidualTrustSource::TheoryLemmaGeneric => self.theory_generic_steps += 1,
            ResidualTrustSource::LocalReconstructionGap => self.local_gap_steps += 1,
        }
    }
}

/// Mapping from ay variable names to kernel proof context.
///
/// When a tactic sets up the Ay problem, it registers FVars with names
/// like "fvar_123". This struct maps those names back to kernel expressions.
#[derive(Debug, Clone)]
pub struct VariableMapping {
    /// Map from ay variable name → (kernel Expr, type Expr)
    pub(crate) name_to_expr: HashMap<String, (Expr, Expr)>,
    /// Map from ay variable name → (FVarId, proof Expr, proposition type Expr)
    pub(crate) hypothesis_proofs: HashMap<String, (FVarId, Expr, Expr)>,
}

impl Default for VariableMapping {
    fn default() -> Self {
        Self::new()
    }
}

impl VariableMapping {
    /// Create an empty variable mapping.
    pub fn new() -> Self {
        Self {
            name_to_expr: HashMap::new(),
            hypothesis_proofs: HashMap::new(),
        }
    }

    /// Register a ay variable name with its kernel expression and type.
    ///
    /// If the expression is an FVar, asserts it is not in the sentinel
    /// range to prevent collision with reconstruction witnesses.
    pub fn register_var(&mut self, name: &str, expr: Expr, ty: Expr) {
        if let ExprKind::FVar(fvar_id) = expr.kind() {
            assert!(
                !fvar_id.is_sentinel(),
                "register_var: FVarId {} in expr is in sentinel range (>= {})",
                fvar_id.as_u64(),
                FVarId::SENTINEL_RANGE_START,
            );
        }
        self.name_to_expr.insert(name.to_string(), (expr, ty));
    }

    /// Register a hypothesis: ay variable name → FVar proof of a proposition.
    ///
    /// # Panics
    ///
    /// Panics if `fvar_id` falls in the sentinel range reserved for proof
    /// reconstruction witnesses (`FVarId::SENTINEL_RANGE_START..=u64::MAX`).
    pub fn register_hypothesis(
        &mut self,
        name: &str,
        fvar_id: FVarId,
        proof_expr: Expr,
        prop_ty: Expr,
    ) {
        assert!(
            !fvar_id.is_sentinel(),
            "register_hypothesis: FVarId {} is in sentinel range (>= {}), would collide with proof reconstruction witnesses",
            fvar_id.as_u64(),
            FVarId::SENTINEL_RANGE_START,
        );
        self.hypothesis_proofs
            .insert(name.to_string(), (fvar_id, proof_expr, prop_ty));
    }

    /// Look up the kernel expression for a ay variable name.
    pub fn get_var(&self, name: &str) -> Option<&(Expr, Expr)> {
        self.name_to_expr.get(name)
    }

    /// Look up a hypothesis proof by ay variable name.
    pub fn get_hypothesis(&self, name: &str) -> Option<&(FVarId, Expr, Expr)> {
        self.hypothesis_proofs.get(name)
    }

    /// Find a hypothesis whose proposition type matches the given expression.
    ///
    /// This handles non-Var Assume steps (e.g., equality atoms in EUF proofs)
    /// where the ay term is a compound expression like `App(=, [a, b])` rather
    /// than a named boolean variable.
    pub fn find_hypothesis_by_prop(&self, prop: &Expr) -> Option<&(FVarId, Expr, Expr)> {
        self.hypothesis_proofs
            .values()
            .find(|(_fvar_id, _proof_expr, prop_ty)| prop_ty == prop)
    }
}
