// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ Tactics for clean
//!
//! This module provides automated tactics for TLA+ proof obligations,
//! mapping from Isabelle tactics used by TLAPS.
//!
//! ## Tactic Mapping
//!
//! | Isabelle | clean Equivalent |
//! |----------|------------------|
//! | `auto` | `tla_auto` (simp + aesop + superposition) |
//! | `force` | `tla_force` (quantifier reasoning) |
//! | `blast` | `tla_blast` (tableau prover) |
//! | `clarsimp` | `tla_clarsimp` (simp + classical) |
//!
//! ## Module Structure
//!
//! - `arithmetic`: Arithmetic simplification and ring normalization
//! - `helpers`: Shared helper utilities for expression manipulation
//! - `arith`: Arithmetic normalization and identity checking
//! - `expr_utils`: Expression extractors, predicates, and utilities
//! - `induction`: Natural, well-founded, and lexicographic induction
//! - `positivity`: Positivity proofs for natural numbers
//! - `progress`: Progress measure and variant function proofs
//! - `rewrite`: Hypothesis-based recursive rewriting
//! - `ring`: Polynomial normalization for ring step cases
//! - `temporal`: Temporal logic (□, ◇, ~>, fixed-point induction)
//!
//! ## Implementation
//!
//! Uses clean-elab's tactic framework (simp, aesop, tauto) and clean-auto's
//! SMT bridge for automated proving.

mod arith;
pub mod arithmetic;
mod exists;
mod expr_utils;
pub mod helpers;
mod induction;
mod positivity;
mod progress;
mod rewrite;
mod ring;
mod temporal;
pub mod verify;
use crate::encoding::TlaContext;
use crate::obligation::{ObligationResult, TlaObligation};
use crate::TlaError;
use clean_auto::AutomationEngine;
use clean_elab::tactic::{aesop, intro, simp, tauto, ProofState, SimpConfig, TacticError};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind};
use std::time::{Duration, Instant};
pub use verify::verify_obligation;

/// Result from tla_auto tactic
#[derive(Debug, Clone)]
pub struct TlaAutoResult {
    /// Whether the goal was solved
    pub solved: bool,
    /// Proof certificate if solved
    pub certificate: Option<Vec<u8>>,
    /// Tactics that made progress
    pub tactics_used: Vec<String>,
    /// Error if failed
    pub error: Option<String>,
}

impl TlaAutoResult {
    /// Create a successful result
    pub fn success(certificate: Vec<u8>, tactics: Vec<String>) -> Self {
        Self {
            solved: true,
            certificate: Some(certificate),
            tactics_used: tactics,
            error: None,
        }
    }

    /// Create a failed result
    pub fn failure(error: &str, tactics: Vec<String>) -> Self {
        Self {
            solved: false,
            certificate: None,
            tactics_used: tactics,
            error: Some(error.to_string()),
        }
    }
}

/// Information about a recursive definition like sum_def_succ:
/// ∀k ∈ Nat. f(k+1) = g(f(k), k)
/// For multi-argument functions like ∀k ∈ Nat. pow(n, k+1) = n * pow(n, k),
/// we store the prefix arguments separately.
pub(super) struct RecursiveRewrite {
    /// The function being defined (e.g., "pow")
    pub(super) func_name: String,
    /// Prefix arguments for multi-arg functions (e.g., for `pow(2, k+1)`, this is `[2]`)
    /// These must match exactly when applying the rewrite
    pub(super) prefix_args: Vec<Expr>,
    /// The RHS template with BVar(0) representing the variable
    /// For sum_def_succ: f(#0) + (#0 + 1)
    pub(super) rhs_template: Expr,
}

/// TLA+ tactic engine
pub struct TlaTacticEngine {
    /// Translation context
    ctx: TlaContext,
    /// Kernel environment for proof checking
    pub(super) env: Environment,
    /// Enable trace output
    pub(super) trace: bool,
    /// Maximum simplification iterations (reserved for future use)
    _max_simp_iters: u32,
    /// Timeout in milliseconds
    pub(super) timeout_ms: u64,
    /// SMT automation engine
    pub(super) auto_engine: AutomationEngine,
}

impl TlaTacticEngine {
    /// Create a new tactic engine
    pub fn new() -> Self {
        let mut ctx = TlaContext::new();

        // Ensure core logical connectives exist so tauto/cases/by_cases can run.
        let _ = ctx.env.init_true_false();
        let _ = ctx.env.init_and();
        let _ = ctx.env.init_iff();
        let _ = ctx.env.init_classical();

        Self {
            env: ctx.env.clone(),
            ctx,
            trace: false,
            _max_simp_iters: 100,
            timeout_ms: 10_000, // 10 seconds default
            auto_engine: AutomationEngine::new(),
        }
    }

    /// Create with a pre-configured environment
    pub fn with_env(mut env: Environment) -> Self {
        // Make sure the passed env supports propositional tactics too.
        let _ = env.init_true_false();
        let _ = env.init_and();
        let _ = env.init_iff();
        let _ = env.init_classical();

        let mut ctx = TlaContext::new();
        ctx.env = env.clone();

        Self {
            ctx,
            env,
            trace: false,
            _max_simp_iters: 100,
            timeout_ms: 10_000,
            auto_engine: AutomationEngine::new(),
        }
    }

    /// Enable/disable trace output
    pub fn with_trace(mut self, enable: bool) -> Self {
        self.trace = enable;
        self
    }

    /// Set timeout
    pub fn with_timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = ms;
        self
    }

    /// Process an obligation with automatic tactic selection
    pub fn prove(&mut self, obligation: &TlaObligation) -> ObligationResult {
        let start = Instant::now();
        let mut tactics_tried = Vec::new();

        // Choose tactic based on hint or heuristics
        let tactic = obligation.tactic_hint.as_deref().unwrap_or_else(|| {
            if obligation.is_temporal() {
                "temporal"
            } else if obligation.likely_needs_induction() {
                "induction"
            } else {
                "auto"
            }
        });

        let result = match tactic {
            "auto" => self.tla_auto(obligation, &mut tactics_tried),
            "force" => self.tla_force(obligation, &mut tactics_tried),
            "blast" => self.tla_blast(obligation, &mut tactics_tried),
            "clarsimp" => self.tla_clarsimp(obligation, &mut tactics_tried),
            "temporal" => self.tla_temporal(obligation, &mut tactics_tried),
            "induction" => self.tla_induction(obligation, &mut tactics_tried),
            other => Err(TlaError::UnknownOperator(format!(
                "Unknown tactic: {}",
                other
            ))),
        };

        let elapsed = start.elapsed().as_millis() as u64;

        match result {
            Ok(cert) => ObligationResult::success(cert, elapsed, tactics_tried),
            Err(e) => ObligationResult::failure(e.to_string(), elapsed, tactics_tried),
        }
    }

    /// Automatic proof search (equivalent to Isabelle's `auto`)
    ///
    /// Strategy:
    /// 1. Check for trivially true/false goals
    /// 2. Try simplification
    /// 3. Try aesop (AND-OR tree search)
    /// 4. Try superposition
    fn tla_auto(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        // Step 1: Translate to clean
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Step 1.5: Check for trivially provable goals
        tactics.push("trivial".to_string());
        if let Some(cert) = self.try_trivial(&goal)? {
            return Ok(cert);
        }

        // Step 2: Try simplification
        tactics.push("simp".to_string());
        if let Some(cert) = self.try_simp(&goal)? {
            return Ok(cert);
        }

        // Step 3: Try intro/cases (break down connectives)
        tactics.push("intro_cases".to_string());
        if let Some(cert) = self.try_intro_cases(&goal)? {
            return Ok(cert);
        }

        // Step 4: Try aesop (best-first search)
        tactics.push("aesop".to_string());
        if let Some(cert) = self.try_aesop(&goal)? {
            return Ok(cert);
        }

        // Step 5: Try superposition
        tactics.push("superposition".to_string());
        if let Some(cert) = self.try_superposition(&goal)? {
            return Ok(cert);
        }

        Err(TlaError::ProofFailed(
            "auto: no tactic succeeded".to_string(),
        ))
    }

    /// Quantifier reasoning (equivalent to Isabelle's `force`)
    fn tla_force(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Force focuses on quantifier instantiation
        tactics.push("intro_all".to_string());
        if let Some(cert) = self.try_intro_all(&goal)? {
            return Ok(cert);
        }

        tactics.push("existsi".to_string());
        if let Some(cert) = self.try_exists_instantiation(&goal)? {
            return Ok(cert);
        }

        // Fall back to auto
        self.tla_auto(obligation, tactics)
    }

    /// Tableau prover (equivalent to Isabelle's `blast`)
    fn tla_blast(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Blast uses tableaux proof search
        tactics.push("tableau".to_string());
        if let Some(cert) = self.try_tableau(&goal)? {
            return Ok(cert);
        }

        Err(TlaError::ProofFailed(
            "blast: tableau search failed".to_string(),
        ))
    }

    /// Simplification + classical reasoning (equivalent to Isabelle's `clarsimp`)
    fn tla_clarsimp(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Clarsimp = clarify + simp
        tactics.push("clarify".to_string());
        tactics.push("simp".to_string());

        if let Some(cert) = self.try_simp(&goal)? {
            return Ok(cert);
        }

        // Classical reasoning
        tactics.push("classical".to_string());
        if let Some(cert) = self.try_classical(&goal)? {
            return Ok(cert);
        }

        Err(TlaError::ProofFailed("clarsimp: failed".to_string()))
    }

    /// Temporal logic reasoning
    fn tla_temporal(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Temporal tactics use fixed point theory
        tactics.push("unfold_temporal".to_string());
        if let Some(cert) = self.try_temporal_unfold(&goal)? {
            return Ok(cert);
        }

        tactics.push("lfp_induction".to_string());
        if let Some(cert) = self.try_lfp_induction(&goal)? {
            return Ok(cert);
        }

        tactics.push("gfp_coinduction".to_string());
        if let Some(cert) = self.try_gfp_coinduction(&goal)? {
            return Ok(cert);
        }

        Err(TlaError::ProofFailed(
            "temporal: no tactic succeeded".to_string(),
        ))
    }

    /// Induction tactic
    fn tla_induction(
        &mut self,
        obligation: &TlaObligation,
        tactics: &mut Vec<String>,
    ) -> Result<String, TlaError> {
        let goal = obligation.to_clean_goal(&mut self.ctx)?;

        // Natural number induction
        tactics.push("nat_induction".to_string());
        if let Some(cert) = self.try_nat_induction(&goal)? {
            return Ok(cert);
        }

        // Well-founded induction
        tactics.push("wf_induction".to_string());
        if let Some(cert) = self.try_wf_induction(&goal)? {
            return Ok(cert);
        }

        // Fall back to auto
        self.tla_auto(obligation, tactics)
    }

    // ================================================================
    // Internal tactic implementations
    // ================================================================

    /// Create a proof state from a goal expression
    pub(super) fn make_proof_state(&self, goal: &Expr) -> ProofState {
        ProofState::new(self.env.clone(), goal.clone())
    }

    /// Generate a proof certificate string
    pub(super) fn generate_certificate(&self, tactic_name: &str) -> String {
        // Generate a simple certificate describing the proof
        // In the future, this could produce DRAT/LRAT certificates
        format!("{{\"tactic\":\"{}\",\"status\":\"proved\"}}", tactic_name)
    }

    /// Try trivial goal check (True, trivial, exact hypotheses)
    fn try_trivial(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Check for trivially true goals (True, Bool.true, trivial)
        if self.is_trivially_true(goal) {
            if self.trace {
                eprintln!("[TLA] trivial: goal is True");
            }
            return Ok(Some(self.generate_certificate("trivial")));
        }

        // Check for goals that are just hypotheses wrapped in Pi
        // Handle sequent encoding: h1 → h2 → ... → goal
        // If goal == True after peeling hypotheses, it's trivial
        if let Some(inner) = self.peel_pis_to_innermost(goal) {
            if self.is_trivially_true(&inner) {
                if self.trace {
                    eprintln!("[TLA] trivial: goal is True after peeling hypotheses");
                }
                return Ok(Some(self.generate_certificate("trivial_sequent")));
            }
        }

        Ok(None)
    }

    /// Peel off non-dependent Pi bindings to get the innermost goal
    fn peel_pis_to_innermost(&self, expr: &Expr) -> Option<Expr> {
        let mut current = expr.clone();
        let mut peeled = false;

        while let ExprKind::Pi(_, _, body) = current.kind() {
            if !body.has_loose_bvars() {
                current = body.as_ref().clone();
                peeled = true;
            } else {
                break;
            }
        }

        if peeled {
            Some(current)
        } else {
            None
        }
    }

    /// Peel off hypothesis bindings and collect their types.
    ///
    /// For a sequent-encoded goal like:
    /// ```text
    /// Pi(Implicit, TLA.Value,    -- declaration (skip)
    ///    Pi(Default, h1_type,    -- hypothesis (collect)
    ///       Pi(Default, h2_type, -- hypothesis (collect)
    ///          goal)))           -- inner goal
    /// ```
    ///
    /// This returns `([h1_type, h2_type], goal)`.
    ///
    /// Key insight: Implicit Pis are declarations (constants, variables),
    /// non-implicit non-dependent Pis are hypotheses (implications).
    pub(super) fn peel_hypotheses_with_context(&self, expr: &Expr) -> (Vec<Expr>, Expr) {
        use clean_kernel::expr::BinderInfo;

        let mut current = expr.clone();
        let mut hypothesis_types = Vec::new();

        loop {
            match current.kind() {
                // Skip implicit declarations (constants, variables)
                // These are dependent Pis that introduce names used in the body
                ExprKind::Pi(bd, _, body) if bd.info == BinderInfo::Implicit => {
                    current = body.as_ref().clone();
                }
                // Non-implicit, non-dependent Pi = hypothesis (implication)
                ExprKind::Pi(_, ty, body) if !body.has_loose_bvars() => {
                    hypothesis_types.push(ty.as_ref().clone());
                    current = body.as_ref().clone();
                }
                // Anything else: stop peeling
                _ => break,
            }
        }

        (hypothesis_types, current)
    }

    /// Wrap an expression with hypotheses as implications (Pi bindings).
    ///
    /// Given hypotheses [h1, h2, ...] and a goal G, produces:
    /// h1 → h2 → ... → G
    ///
    /// This allows subgoals (like induction cases) to use the hypotheses
    /// from the original obligation.
    pub(super) fn wrap_with_hypotheses(&self, hypotheses: &[Expr], goal: Expr) -> Expr {
        let mut result = goal;
        for hyp in hypotheses.iter().rev() {
            result = Expr::pi(clean_kernel::expr::BinderInfo::Default, hyp.clone(), result);
        }
        result
    }

    /// Try simplification using clean-elab simp tactic
    pub(super) fn try_simp(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);
        let config = SimpConfig::new();

        match simp(&mut state, config) {
            Ok(()) if state.is_complete() => {
                if self.trace {
                    eprintln!("[TLA] simp: goal closed");
                }
                Ok(Some(self.generate_certificate("simp")))
            }
            Ok(()) => {
                if self.trace {
                    eprintln!("[TLA] simp: made progress but goal not closed");
                }
                Ok(None) // Made progress but goal not fully solved
            }
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("simp"))),
            Err(_) => Ok(None),
        }
    }

    /// Try intro followed by cases/split to decompose the goal
    fn try_intro_cases(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);

        // Try intro as many times as possible
        while intro(&mut state, "_h").is_ok() {
            if self.trace {
                eprintln!("[TLA] intro_cases: introduced hypothesis");
            }
        }

        // Then try tauto for propositional reasoning
        match tauto(&mut state) {
            Ok(()) if state.is_complete() => Ok(Some(self.generate_certificate("intro_tauto"))),
            Ok(()) => Ok(None),
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("intro_tauto"))),
            Err(_) => Ok(None),
        }
    }

    /// Try aesop (AND-OR tree search)
    fn try_aesop(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);

        match aesop(&mut state) {
            Ok(()) if state.is_complete() => {
                if self.trace {
                    eprintln!("[TLA] aesop: goal closed");
                }
                Ok(Some(self.generate_certificate("aesop")))
            }
            Ok(()) => Ok(None),
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("aesop"))),
            Err(_) => Ok(None),
        }
    }

    /// Try SMT-based superposition proving via clean-auto
    pub(super) fn try_superposition(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let timeout = Duration::from_millis(self.timeout_ms);

        match self.auto_engine.auto_prove(&self.env, goal, timeout, None) {
            Some(result) => {
                if self.trace {
                    eprintln!(
                        "[TLA] superposition: {} ({}ms)",
                        result.proof_text, result.time_ms
                    );
                }
                Ok(Some(format!(
                    "{{\"tactic\":\"superposition\",\"proof\":\"{}\",\"time_ms\":{}}}",
                    result.proof_text.replace('"', "\\\""),
                    result.time_ms
                )))
            }
            None => Ok(None),
        }
    }

    /// Try introducing all universal quantifiers
    fn try_intro_all(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);
        let mut intro_count = 0;

        // Keep introducing until we can't anymore
        while intro(&mut state, &format!("_x{}", intro_count)).is_ok() {
            intro_count += 1;
            if self.trace {
                eprintln!("[TLA] intro_all: introduced variable _{}", intro_count);
            }
        }

        if intro_count > 0 && state.is_complete() {
            Ok(Some(self.generate_certificate("intro_all")))
        } else {
            Ok(None)
        }
    }

    /// Try tableau-style proof search (use tauto for now)
    fn try_tableau(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);

        // Tauto implements tableau-style search for propositional logic
        match tauto(&mut state) {
            Ok(()) if state.is_complete() => {
                if self.trace {
                    eprintln!("[TLA] tableau: goal closed via tauto");
                }
                Ok(Some(self.generate_certificate("tableau")))
            }
            Ok(()) => Ok(None),
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("tableau"))),
            Err(_) => Ok(None),
        }
    }

    /// Try classical reasoning (law of excluded middle, double negation)
    fn try_classical(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Classical reasoning is handled by tauto
        self.try_tableau(goal)
    }
}

impl Default for TlaTacticEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// Prove a TLA+ obligation
///
/// Main entry point for TLAPS integration.
pub fn prove_tla_obligation(obligation: &TlaObligation) -> ObligationResult {
    let mut engine = TlaTacticEngine::new();
    engine.prove(obligation)
}

/// Prove a TLA+ obligation with trace output enabled.
pub fn prove_tla_obligation_traced(obligation: &TlaObligation) -> ObligationResult {
    let mut engine = TlaTacticEngine::new().with_trace(true);
    engine.prove(obligation)
}

#[cfg(test)]
mod falsification_tests;
#[cfg(test)]
mod tests;
