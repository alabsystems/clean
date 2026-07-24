// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic dispatch and basic tactic building blocks.
//!
//! Contains top-level tactic dispatch (tla_auto, tla_force, etc.) and
//! basic tactic implementations (simp, aesop, superposition, tableau, etc.).

use super::TlaTacticEngine;
use crate::TlaError;
use clean_elab::tactic::{aesop, intro, simp, tauto, SimpConfig, TacticError};
use clean_kernel::{Expr, ExprKind};
use std::time::Duration;

impl TlaTacticEngine {
    /// Automatic proof search (equivalent to Isabelle's `auto`)
    ///
    /// Strategy:
    /// 1. Check for trivially true/false goals
    /// 2. Try simplification
    /// 3. Try aesop (AND-OR tree search)
    /// 4. Try superposition
    pub(crate) fn tla_auto(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    pub(crate) fn tla_force(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    pub(crate) fn tla_blast(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    pub(crate) fn tla_clarsimp(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    pub(crate) fn tla_temporal(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    pub(crate) fn tla_induction(
        &mut self,
        obligation: &crate::obligation::TlaObligation,
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
    // Internal tactic building blocks
    // ================================================================

    /// Create a proof state from a goal expression
    pub(crate) fn make_proof_state(&self, goal: &Expr) -> clean_elab::tactic::ProofState {
        clean_elab::tactic::ProofState::new(self.env.clone(), goal.clone())
    }

    /// Generate a proof certificate string
    pub(crate) fn generate_certificate(&self, tactic_name: &str) -> String {
        format!("{{\"tactic\":\"{}\",\"status\":\"proved\"}}", tactic_name)
    }

    /// Try trivial goal check (True, trivial, exact hypotheses)
    pub(crate) fn try_trivial(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
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
    pub(crate) fn peel_pis_to_innermost(&self, expr: &Expr) -> Option<Expr> {
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
    pub(crate) fn peel_hypotheses_with_context(&self, expr: &Expr) -> (Vec<Expr>, Expr) {
        use clean_kernel::expr::BinderInfo;

        let mut current = expr.clone();
        let mut hypothesis_types = Vec::new();

        loop {
            match current.kind() {
                // Skip implicit declarations (constants, variables)
                ExprKind::Pi(BinderInfo::Implicit, _, body) => {
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
    pub(crate) fn wrap_with_hypotheses(&self, hypotheses: &[Expr], goal: Expr) -> Expr {
        let mut result = goal;
        for hyp in hypotheses.iter().rev() {
            result = Expr::pi(clean_kernel::expr::BinderInfo::Default, hyp.clone(), result);
        }
        result
    }

    /// Try simplification using clean-elab simp tactic
    pub(crate) fn try_simp(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
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
                Ok(None)
            }
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("simp"))),
            Err(_) => Ok(None),
        }
    }

    /// Try intro followed by cases/split to decompose the goal
    pub(crate) fn try_intro_cases(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);

        while intro(&mut state, "_h".to_string()).is_ok() {
            if self.trace {
                eprintln!("[TLA] intro_cases: introduced hypothesis");
            }
        }

        match tauto(&mut state) {
            Ok(()) if state.is_complete() => Ok(Some(self.generate_certificate("intro_tauto"))),
            Ok(()) => Ok(None),
            Err(TacticError::NoGoals) => Ok(Some(self.generate_certificate("intro_tauto"))),
            Err(_) => Ok(None),
        }
    }

    /// Try aesop (AND-OR tree search)
    pub(crate) fn try_aesop(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
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
    pub(crate) fn try_superposition(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
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
    pub(crate) fn try_intro_all(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);
        let mut intro_count = 0;

        while intro(&mut state, format!("_x{}", intro_count)).is_ok() {
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

    /// Try existential instantiation (not yet implemented fully)
    pub(crate) fn try_exists_instantiation(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        self.try_superposition(goal)
    }

    /// Try tableau-style proof search (use tauto for now)
    pub(crate) fn try_tableau(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let mut state = self.make_proof_state(goal);

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
    pub(crate) fn try_classical(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        self.try_tableau(goal)
    }

    // ================================================================
    // Trivial / comparison checks
    // ================================================================

    /// Check if expression is trivially true (Bool.true or similar)
    pub(crate) fn is_trivially_true(&self, expr: &Expr) -> bool {
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "Bool.true" || s == "True" || s == "trivial";
        }

        // Check for trivially true comparisons
        if let Some((op, lhs, rhs)) = self.extract_comparison(expr) {
            if self.exprs_equal(&lhs, &rhs)
                && (op == "Eq" || op == "TLA.eq" || op == "TLA.le" || op == "TLA.ge")
            {
                return true;
            }
            if (op == "TLA.ge" || op == "Nat.ge") && self.is_zero(&rhs) {
                return true;
            }
            if (op == "TLA.lt" || op == "TLA.le") && self.is_expr_plus_positive(&lhs, &rhs) {
                return true;
            }
            if (op == "TLA.gt" || op == "TLA.ge") && self.is_expr_plus_positive(&rhs, &lhs) {
                return true;
            }
        }

        false
    }

    /// Check if rhs is lhs + k where k is positive.
    pub(crate) fn is_expr_plus_positive(&self, lhs: &Expr, rhs: &Expr) -> bool {
        if let ExprKind::App(f, k) = rhs.kind() {
            if let ExprKind::App(add, inner_lhs) = f.kind() {
                if let ExprKind::Const(name, _) = add.kind() {
                    if name.to_string() == "TLA.add" || name.to_string() == "Nat.add" {
                        if self.exprs_equal(inner_lhs, lhs) && self.is_positive_constant(k) {
                            return true;
                        }
                        if self.exprs_equal(k.as_ref(), lhs) && self.is_positive_constant(inner_lhs)
                        {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Check if expression is trivially false (Bool.false or False)
    pub(crate) fn is_trivially_false(&self, expr: &Expr) -> bool {
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "Bool.false" || s == "False";
        }
        false
    }

    /// Check if an implication P → Q is trivially true.
    pub(crate) fn is_implication_trivially_true(
        &self,
        antecedent: &Expr,
        consequent: &Expr,
    ) -> bool {
        self.is_trivially_true(consequent)
            || self.is_trivially_false(antecedent)
            || self.exprs_equal(antecedent, consequent)
    }

    /// Check if two expressions are structurally equal
    pub(crate) fn exprs_equal(&self, a: &Expr, b: &Expr) -> bool {
        a == b
    }
}
