// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! SMT-Kernel Bridge
//!
//! This module provides translation between clean-kernel expressions (Expr)
//! and SMT solver terms, enabling proof automation via SMT.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                     SMT-Kernel Bridge                            │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                 │
//! │  Kernel Expr ─────────► Bridge translation/classification ───►  │
//! │  (Prop/Bool)             SMT queries / solver terms    SMT Solver│
//! │                                                                 │
//! │  Proof / Refutation ◄── SmtVerificationResult ◄───────────────  │
//! │  / Unknown reason        Verified / Unverified / Refuted /      │
//! │                           Unknown                               │
//! │                                                                 │
//! └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! Public bridge outcomes are typed:
//! - `Verified` carries a kernel proof term
//! - `Unverified` records UNSAT without a reconstructed kernel proof
//! - `Refuted` records a counterexample / refutation path
//! - `Unknown` preserves solver inconclusive states separately
//!
//! # Public Capability Surface
//!
//! The reviewed bridge / classifier surface currently covers:
//! - Propositional forms: `Eq`, `Neq`, `And`, `Or`, `Not`, `Implies`, `Iff`, `True`, `False`
//! - Comparisons: `Lt`, `Le`, `Gt`, `Ge`
//! - Arithmetic heads: `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Neg`
//! - Quantified forms: `Forall`, `Exists`
//!
//! Quantifier replay uses premise-guided E-matching prioritization where origin
//! metadata is available.
//!
//! # Premise-Guided E-matching
//!
//! The bridge supports premise-relevance scoring for E-matching instantiation.
//! When hypotheses originate from named theorems in a premise database, their
//! relevance scores can influence quantifier instantiation priority.
//!
//! ## Weighting Policy
//!
//! E-matching priority is computed by combining:
//! 1. **Trigger quality** (base score): Selective, ground-matchable patterns score higher
//! 2. **Goal-directed bonus**: Patterns matching goal terms get priority
//! 3. **Premise-relevance bonus**: Scores scaled to [-15, +30] for premises with origin metadata
//!
//! The premise-relevance bonus is *additive* to preserve trigger selectivity.
//! Score 0.0 → -15 (de-prioritize irrelevant), 0.5 → +8, 1.0 → +30.
//!
//! ## Usage with PremiseDatabase
//!
//! ```text
//! // Compute premise scores from goal
//! let mepo = MePoSelector::new(&premise_db);
//! let scored = mepo.select_with_scores(&goal);
//! let scores: HashMap<PremiseId, f64> = scored.iter()
//!     .map(|(p, s)| (p.id, *s))
//!     .collect();
//!
//! // Inject scores into bridge
//! let mut bridge = SmtBridge::new(&env);
//! bridge.set_premise_scores(scores);
//!
//! // Add hypotheses with origin for tracking
//! for (premise, _) in &scored {
//!     bridge.add_hypothesis_with_premise(
//!         &premise.statement,
//!         None,
//!         Some(PremiseOrigin::from_premise_id(premise.id)),
//!     );
//! }
//!
//! // Prove - E-matching will prioritize relevant premises
//! let result = bridge.prove(&goal);
//! ```
//!
//! # Example Usage
//!
//! ```text
//! use clean_auto::bridge::SmtBridge;
//! use clean_kernel::{Environment, Expr};
//!
//! let env = Environment::new();
//! let mut bridge = SmtBridge::new(&env);
//!
//! // Try to prove: ∀ x y : A, x = y → y = x
//! let goal = /* construct goal Expr */;
//! match bridge.prove(&goal) {
//!     Ok(SmtVerificationResult::Verified(proof)) => { /* kernel proof found */ }
//!     Ok(SmtVerificationResult::Unverified { .. }) => { /* UNSAT but no proof term */ }
//!     Ok(SmtVerificationResult::Refuted(_)) => { /* counterexample found */ }
//!     Ok(SmtVerificationResult::Unknown(reason)) => { /* solver inconclusive */ }
//!     Err(e) => { /* translation error */ }
//! }
//! ```

// Bridge-level trust-accounting helpers shared with clean-elab.
pub mod proof_trust;

// Cross-crate classifier contract for the proof-producing SMT translator.
// Exposes SmtLogicalForm and classify_for_proof_translation without making
// expr_classifier public. Part of #2810.
pub mod proof_translation_contract;

// Ay SMT backend (enabled via ay-smt feature)
// Provider-internal: downstream consumers use `ay_contract` instead. Part of #2774.
#[cfg(feature = "ay-smt")]
pub(crate) mod ay_backend;

// Curated cross-crate ay contract — the supported public in-repo ay API.
#[cfg(feature = "ay-smt")]
pub mod ay_contract;

// Split-out submodules
mod arith_chain;
mod arith_reconstruction;
mod chain_search;
mod classify;
pub(crate) mod disjunction;
mod ematching;
pub(crate) mod eq_proof_builders;
mod error;
pub(crate) mod expr_classifier;
mod guided_equality;
pub mod head_family;
mod hypothesis;
mod instantiate;
pub(crate) mod name_match;
mod prefix_analysis;
mod premise_origin;
mod proof_reconstruction;
mod proof_terms;
mod prop_classical_split;
mod prop_eq_rewrite;
mod prop_eq_subgoals;
mod prop_eq_trans;
mod prop_exists;
mod prop_lambda_proofs;
mod prop_literal;
mod prop_local_assumptions;
mod prop_reconstruction;
mod prop_strategies;
mod prop_under_assumption;
mod prove;
mod prove_implication;
pub(crate) mod quantifier;
#[cfg(feature = "ay-smt")]
pub(crate) mod rat_smt;
mod result;
mod scoring;
pub(crate) mod superposition_clausify;
pub(crate) mod superposition_reconstruction;
mod trail_guidance;
mod translate;
pub(crate) mod trigger;

#[cfg(kani)]
mod kani_proofs;

pub use error::BridgeError;
pub(crate) use error::BridgeResult;
pub(crate) use hypothesis::HypothesisOpts;
pub use premise_origin::{PremiseOrigin, QuantifierOrigin};
pub use result::SmtProofResult;
pub use result::{ProofMethod, SmtVerificationResult};

// Re-exports for bridge test modules (used via `use super::*`).
// Grouped under a single `cfg(test)` block to prevent rustfmt reorder drift.
#[cfg(test)]
pub(crate) use {
    crate::proof::ProofStep,
    quantifier::QuantifierKind,
    scoring::{
        GoalDirectedScorer, GoalPatternExtractor, GoalPatterns, GroundTermPattern,
        QuantifierPriorityScorer,
    },
    trigger::TriggerPattern,
};

// Re-export types used across sub-modules (pub(crate) modules, not re-exports)
pub(crate) use expr_classifier::LogicalForm;
use translate::ExprKey;

use crate::premise::PremiseId;
use crate::smt::{SmtSolver, TermId};
use crate::theories::arithmetic::ArithmeticTheory;
use crate::theories::arrays::ArrayTheory;
use crate::theories::equality::EqualityTheory;
#[cfg(test)]
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, LocalContext, TypeChecker};
// Re-exported for test modules that use `use super::*`
#[cfg(test)]
use clean_kernel::BinderInfo;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};

/// Stack overflow guard for recursive Expr traversals.
///
/// Red zone: 32KB remaining triggers growth.
/// Growth: 1MB per extension.
///
/// Mirrors `ay_backend::proof_reconstruct::stack_safe` at crate scope so all
/// bridge sub-modules can use a single import path.
///
/// See: designs/2026-03-15-bridge-recursive-stack-safety-hardening.md
#[inline(always)]
pub(crate) fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(32 * 1024, 1024 * 1024, f)
}

/// SMT Bridge for translating between kernel Expr and SMT solver.
///
/// # Single-shot contract (#2836)
///
/// Each `SmtBridge` instance supports at most one [`prove()`](Self::prove) call.
/// Hypotheses may be added before proving, but a second `prove()` returns
/// [`BridgeError::BridgeReuse`]. Create a new `SmtBridge` for each goal.
pub struct SmtBridge<'env> {
    /// The kernel environment for type inference and universe level computation
    env: &'env Environment,
    /// Optional local context for FVar type resolution during type inference.
    /// When set, TypeChecker can resolve FVar types that appear in hypothesis-
    /// derived expressions. Without this, infer_type fails on all FVar exprs.
    local_ctx: Option<LocalContext>,
    /// The SMT solver
    pub(crate) smt: SmtSolver,
    /// Mapping from kernel expressions to SMT term IDs
    pub(crate) expr_to_term: HashMap<ExprKey, TermId>,
    /// Mapping from SMT term IDs to kernel expressions
    pub(crate) term_to_expr: HashMap<TermId, Expr>,
    /// Mapping from SMT term IDs to their types (for proof building)
    pub(crate) term_to_type: HashMap<TermId, Expr>,
    /// Mapping from free variables to SMT terms
    pub(crate) fvar_to_term: HashMap<FVarId, TermId>,
    /// Counter for generating fresh names
    pub(crate) fresh_counter: u32,
    /// Mapping from asserted equalities to hypothesis FVarIds
    /// The key is (lhs, rhs) in the ORDER the hypothesis was asserted
    /// Only stores the canonical direction, not both
    pub(crate) eq_hypothesis_canonical: HashMap<(TermId, TermId), FVarId>,
    /// Equality theory reference (for proof trace access)
    equality_theory_idx: Option<usize>,
    /// Pending universal quantifier hypotheses for E-matching instantiation
    /// Each entry contains: (types, body, triggers)
    pub(crate) pending_foralls: Vec<PendingForall>,
    /// Maximum number of instantiation rounds
    max_instantiation_rounds: u32,
    /// Maximum instantiations per round
    max_instantiations_per_round: usize,
    /// Set of already-instantiated formulas (for deduplication)
    pub(crate) seen_instances: HashSet<ExprKey>,
    /// Optional premise relevance scores for E-matching priority adjustment
    /// Maps premise IDs to their relevance scores (higher = more relevant)
    /// Set via `set_premise_scores` before calling `prove`
    premise_scores: HashMap<PremiseId, f64>,
    /// Expressions whose translation fell back to unconstrained atoms/terms.
    /// If non-empty after solving, SMT results are downgraded to Unknown
    /// because the solver could satisfy or refute the weakened encoding.
    pub(crate) lossy_atoms: Vec<Expr>,
    /// Count of E-matching hypothesis errors (#2290).
    /// Non-zero indicates degraded E-matching: instantiations were generated
    /// but could not be added as hypotheses (translation failure, unsupported expr).
    pub(crate) ematching_hypothesis_errors: usize,
    /// Deduplication map for opaque atoms (#2251): ensures the same expression
    /// appearing in multiple places (hypothesis and goal) maps to the same SAT
    /// variable, preserving propositional identity.
    atom_to_var: HashMap<ExprKey, u32>,
    /// Propositional hypothesis tracking for non-equality proof reconstruction (#2442).
    /// Stores (FVarId, hypothesis_type) for hypotheses added with FVarIds,
    /// enabling proof reconstruction to find matching hypotheses for goals.
    pub(crate) prop_hypotheses: Vec<(FVarId, Expr)>,
    /// Clause origin tracking: maps SAT clause index → hypothesis FVarId (#2442 Phase 2B).
    /// When an UNSAT core is available, this mapping identifies which hypotheses
    /// participated in the proof, enabling targeted proof reconstruction.
    clause_origins: Vec<Option<FVarId>>,
    /// The FVarId context for nested add_hypothesis calls.
    /// Set before recursive add_hypothesis calls so And-decomposed sub-clauses
    /// inherit the parent hypothesis's FVarId.
    current_hypothesis_fvar: Option<FVarId>,
    /// SAT-variable origin tracking for trail-guided proof reconstruction (#2442).
    /// Maps a SAT variable back to the hypothesis FVarIds that introduced it.
    sat_var_origins: HashMap<u32, HashSet<FVarId>>,
    /// Trail-derived hypothesis hints for the current UNSAT proof attempt (#2442).
    /// Reconstruction prefers these hypotheses first but falls back to the full set.
    trail_hypothesis_hints: HashSet<FVarId>,
    /// Single-shot guard: true after prove() has been called once (#2836).
    /// Prevents reuse of a bridge instance whose solver/lossy state is stale.
    prove_called: bool,
    /// Node-count budget for propositional proof reconstruction (#2489).
    /// Decremented on each `build_prop_proof_inner` call. Prevents OOM from
    /// exponential branching in mutual recursion (build_prop_proof_inner ↔
    /// try_or_elim ↔ try_prove_under_assumption). Uses `Cell` for interior
    /// mutability since reconstruction methods take `&self`.
    prop_reconstruction_budget: Cell<u32>,
    /// FVarIds of Or-typed hypotheses currently being eliminated by `try_or_elim`.
    /// Prevents re-entrant Or.elim on the same hypothesis when `build_prop_proof_inner`
    /// recurses through `try_prove_under_assumption`. Without this guard, the mutual
    /// recursion produces deeply nested `Or.rec` terms. (#2442)
    or_elim_active: RefCell<Vec<FVarId>>,
    /// FVarIds of Exists-typed hypotheses currently being eliminated by `try_exists_elim`.
    /// Prevents re-entrant `Exists.elim` on the same hypothesis when continuation
    /// search recurses back through `build_prop_proof_inner`.
    exists_elim_active: RefCell<Vec<FVarId>>,
    /// Bound existential witnesses available to nested proof reconstruction.
    /// Each entry stores `(type, expr)` in the current de Bruijn scope so
    /// nested `Exists.intro` goals can reuse witnesses opened by `Exists.elim`.
    bound_exists_witnesses: RefCell<Vec<(Expr, Expr)>>,
}

/// A pending universal quantifier hypothesis awaiting instantiation
#[derive(Clone, Debug)]
pub(crate) struct PendingForall {
    /// The quantified types (reserved for future type-based instantiation)
    pub(crate) _tys: Vec<Expr>,
    /// The flattened body with BVars for all bound variables
    pub(crate) body: Expr,
    /// E-matching triggers extracted from the body
    pub(crate) triggers: Vec<crate::egraph::Trigger>,
    /// Bound variable indices for trigger matching
    pub(crate) bound_vars: Vec<u32>,
    /// Priority score for instantiation ordering (higher = instantiate first)
    pub(crate) priority: i32,
    /// Number of times this forall has been instantiated (for fairness)
    pub(crate) instantiation_count: u32,
    /// Origin of this quantifier for premise-guided scoring.
    pub(crate) origin: Option<QuantifierOrigin>,
}

impl PendingForall {
    /// Compute total priority including premise relevance bonus.
    #[must_use]
    pub(crate) fn total_priority(&self, premise_scores: &HashMap<PremiseId, f64>) -> i32 {
        let base = self.priority;
        let bonus = self.compute_premise_bonus(premise_scores);
        base.saturating_add(bonus)
    }

    /// Compute premise relevance bonus scaled to [-15, +30] range.
    #[must_use]
    pub(crate) fn compute_premise_bonus(&self, premise_scores: &HashMap<PremiseId, f64>) -> i32 {
        self.origin
            .as_ref()
            .map_or(0, |origin| origin.relevance_bonus(premise_scores))
    }
}

impl<'env> SmtBridge<'env> {
    /// Create a new SMT bridge
    pub fn new(env: &'env Environment) -> Self {
        let mut smt = SmtSolver::new();
        // Add equality theory by default
        let eq_idx = smt.add_theory(Box::new(EqualityTheory::new()));
        // Add arithmetic theory for Lt/Le comparisons
        let _arith_idx = smt.add_theory(Box::new(ArithmeticTheory::new()));
        // Add array theory for read-over-write axioms (select/store)
        let _array_idx = smt.add_theory(Box::new(ArrayTheory::new()));

        SmtBridge {
            env,
            local_ctx: None,
            smt,
            expr_to_term: HashMap::new(),
            term_to_expr: HashMap::new(),
            term_to_type: HashMap::new(),
            fvar_to_term: HashMap::new(),
            fresh_counter: 0,
            eq_hypothesis_canonical: HashMap::new(),
            equality_theory_idx: Some(eq_idx),
            pending_foralls: Vec::new(),
            max_instantiation_rounds: 3,
            max_instantiations_per_round: 10,
            seen_instances: HashSet::new(),
            premise_scores: HashMap::new(),
            lossy_atoms: Vec::new(),
            ematching_hypothesis_errors: 0,
            atom_to_var: HashMap::new(),
            prop_hypotheses: Vec::new(),
            clause_origins: Vec::new(),
            current_hypothesis_fvar: None,
            sat_var_origins: HashMap::new(),
            trail_hypothesis_hints: HashSet::new(),
            prove_called: false,
            prop_reconstruction_budget: Cell::new(10_000),
            or_elim_active: RefCell::new(Vec::new()),
            exists_elim_active: RefCell::new(Vec::new()),
            bound_exists_witnesses: RefCell::new(Vec::new()),
        }
    }

    /// Set the local context for FVar type resolution.
    ///
    /// When set, the bridge's internal TypeChecker can resolve types of free
    /// variables that appear in hypothesis-derived expressions. Without this,
    /// `infer_type` fails on any expression containing FVars, leaving
    /// `term_to_type` unpopulated for most hypothesis-derived terms.
    pub fn set_local_ctx(&mut self, ctx: LocalContext) {
        self.local_ctx = Some(ctx);
    }

    /// Create a TypeChecker with the bridge's environment and optional local context.
    pub(crate) fn make_tc(&self) -> TypeChecker<'env> {
        match &self.local_ctx {
            Some(ctx) => TypeChecker::with_context(self.env, ctx.clone()),
            None => TypeChecker::new(self.env),
        }
    }

    /// Set premise relevance scores for E-matching priority adjustment
    ///
    /// Call this before `prove()` to influence E-matching instantiation order.
    /// Hypotheses whose `PendingForall.origin` carries a matching premise ID in
    /// this map will receive an additive priority bonus proportional to score.
    ///
    /// # Arguments
    /// * `scores` - Map from premise ID to relevance score (0.0 to 1.0 typical)
    ///
    /// # Example
    ///
    /// ```text
    /// let mut bridge = SmtBridge::new(&env);
    /// // Compute scores using MePoSelector::select_with_scores or similar
    /// let scores: HashMap<PremiseId, f64> = compute_relevance(&goal);
    /// bridge.set_premise_scores(scores);
    /// bridge.add_hypothesis_with_premise(&hyp, None, Some(PremiseOrigin::from_premise_id(id)));
    /// let result = bridge.prove(&goal);
    /// ```
    pub fn set_premise_scores(&mut self, scores: HashMap<PremiseId, f64>) {
        self.premise_scores = scores;
    }

    /// Get a typed reference to the equality theory solver
    pub(crate) fn equality_theory(&self) -> Option<&EqualityTheory> {
        self.equality_theory_idx
            .and_then(|idx| self.smt.get_theory_typed::<EqualityTheory>(idx))
    }

    /// Get a mutable typed reference to the equality theory solver
    pub(crate) fn equality_theory_mut(&mut self) -> Option<&mut EqualityTheory> {
        self.equality_theory_idx
            .and_then(|idx| self.smt.get_theory_typed_mut::<EqualityTheory>(idx))
    }

    /// Set the maximum number of E-matching instantiation rounds
    pub fn set_max_instantiation_rounds(&mut self, rounds: u32) {
        self.max_instantiation_rounds = rounds;
    }

    /// Set the maximum number of instantiations per round
    pub fn set_max_instantiations_per_round(&mut self, count: usize) {
        self.max_instantiations_per_round = count;
    }

    /// Record an expression whose SMT lowering fell back to an unconstrained
    /// placeholder, forcing the overall solve result to degrade to Unknown.
    pub(super) fn record_lossy_expr(&mut self, expr: &Expr) {
        self.lossy_atoms.push(expr.strip_mdata().clone());
    }

    /// Whether an opaque proposition must be treated as lossy rather than as a
    /// stable uninterpreted atom.
    ///
    /// Const/FVar atoms and Const/FVar-headed applications preserve exact
    /// propositional identity. Unsupported forms such as `Let`, `Sort`,
    /// `Proj`, literals, and lambda/complex-headed applications would
    /// otherwise be replaced by unconstrained placeholders.
    pub(super) fn requires_lossy_guard(expr: &Expr) -> bool {
        let expr = expr.strip_mdata();
        match expr.kind() {
            ExprKind::Const(..) | ExprKind::FVar(..) => false,
            ExprKind::App(..) => {
                let head = expr.get_app_fn().strip_mdata();
                !matches!(head.kind(), ExprKind::Const(..) | ExprKind::FVar(..))
            }
            _ => true,
        }
    }

    // Method implementations split into submodules:
    // - prove() → bridge/prove.rs
    // - E-matching instantiation → bridge/ematching.rs
    // - Trail guidance → bridge/trail_guidance.rs
    // - Trigger methods → bridge/trigger.rs
    // - Proof reconstruction → bridge/proof_reconstruction.rs
}

#[cfg(test)]
pub(crate) mod tests;
