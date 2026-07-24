// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Proof, ProofId, TermId, TermStore};
use clean_kernel::{Expr, FVarId};
use hashbrown::HashMap;

use super::trace::{ProofTrace, StepView};
use super::{
    ReconstructResult, ReconstructionError, ReconstructionResult, ReconstructionStats,
    VariableMapping,
};
use crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSummary;

mod assume;
mod residual;
mod trust;

/// Context for proof reconstruction.
///
/// Holds all state needed to translate a ay proof into kernel proof terms.
pub(crate) struct ReconstructionContext<'a> {
    /// Borrowing proof-trace adapter for decoupled ay access (#2451).
    /// Initialized with only the term store for translation contexts, then
    /// attached to the ay proof object when `reconstruct()` starts.
    pub(crate) trace: Option<ProofTrace<'a>>,
    /// Variable mapping from ay names to kernel expressions.
    pub(crate) var_map: &'a VariableMapping,
    /// Cache of already-translated terms (TermId → kernel Expr).
    pub(crate) term_cache: HashMap<TermId, Expr>,
    /// Cache of already-reconstructed proof steps (ProofId → kernel proof Expr).
    pub(crate) step_cache: Vec<Option<Expr>>,
    /// Residual trust carried by each reconstructed step's proof term.
    step_residual_cache: Vec<Option<ResidualTrustSummary>>,
    /// Statistics accumulated during reconstruction.
    pub(crate) stats: ReconstructionStats,
    /// Fresh FVar representing the proof of the negated goal assumption.
    /// Created on first negated-goal Assume step; the caller lambda-abstracts it.
    negated_goal_proof: Option<(FVarId, Expr)>,
    /// Stack of binder names for named→de Bruijn index conversion.
    /// Pushed when entering quantifier bodies, popped on exit.
    /// Last entry = innermost binder = BVar(0).
    pub(crate) binder_names: Vec<String>,
    /// Compound witness FVars and their assumed propositions.
    /// Tracked so the caller can detect open terms and reject them.
    compound_witnesses: Vec<(FVarId, Expr)>,
    /// Count of compound witnesses allocated (for sentinel FVarId allocation).
    /// Incremented each time a new compound witness FVar is created.
    /// Used instead of step_id to avoid exhausting the sentinel range on proofs
    /// with many steps but few compound witnesses.
    compound_witness_count: u32,
}

impl<'a> ReconstructionContext<'a> {
    /// Create a new reconstruction context (translation-only, no proof attached).
    ///
    /// Used by tests that need a context without a full proof object.
    /// Production callers should use [`with_proof`](Self::with_proof).
    #[cfg(test)]
    pub fn new(
        terms: &'a TermStore,
        var_map: &'a VariableMapping,
        proof_step_count: usize,
    ) -> Self {
        Self {
            trace: Some(ProofTrace::without_proof(terms)),
            var_map,
            term_cache: HashMap::new(),
            step_cache: vec![None; proof_step_count],
            step_residual_cache: vec![None; proof_step_count],
            stats: ReconstructionStats {
                total_steps: proof_step_count,
                ..Default::default()
            },
            negated_goal_proof: None,
            binder_names: Vec::new(),
            compound_witnesses: Vec::new(),
            compound_witness_count: 0,
        }
    }

    /// Create a reconstruction context with the proof already attached.
    ///
    /// Routes step-count through the trace adapter so callers never touch
    /// raw `Proof` fields.
    pub(crate) fn with_proof(
        proof: &'a Proof,
        terms: &'a TermStore,
        var_map: &'a VariableMapping,
    ) -> Self {
        let trace = ProofTrace::new(proof, terms);
        let step_count = trace.step_count();
        Self {
            trace: Some(trace),
            var_map,
            term_cache: HashMap::new(),
            step_cache: vec![None; step_count],
            step_residual_cache: vec![None; step_count],
            stats: ReconstructionStats {
                total_steps: step_count,
                ..Default::default()
            },
            negated_goal_proof: None,
            binder_names: Vec::new(),
            compound_witnesses: Vec::new(),
            compound_witness_count: 0,
        }
    }

    /// Access the trace adapter.
    ///
    /// Panics if `new()` did not seed the context correctly.
    pub(crate) fn trace(&self) -> &ProofTrace<'a> {
        self.trace
            .as_ref()
            .expect("invariant: trace seeded by new()")
    }

    /// Look up a term in the cache, returning a typed error on miss.
    pub(super) fn cached_term(
        &self,
        id: TermId,
        step_id: ProofId,
        context: &str,
    ) -> ReconstructResult<Expr> {
        self.term_cache
            .get(&id)
            .cloned()
            .ok_or_else(|| ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("{context}: term not in cache"),
            })
    }

    /// Unwrap a negated literal, returning its inner term ID.
    pub(super) fn unwrap_not(&self, lit: TermId, step_id: ProofId) -> ReconstructResult<TermId> {
        self.trace()
            .as_not(lit)
            .ok_or_else(|| ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "expected negated literal".to_string(),
            })
    }

    /// Attempt to reconstruct a complete proof from the ay proof object.
    pub fn reconstruct(&mut self, proof: &'a Proof, negated_goal: &Expr) -> ReconstructionResult {
        self.trace
            .as_mut()
            .expect("invariant: trace seeded by new()")
            .attach_proof(proof);
        let step_count = self.trace().step_count();
        let root_idx = self.trace().root_empty_clause_step();
        let reachable = root_idx.map(|idx| self.trace().reachable_from(idx));
        for idx in 0..step_count {
            if let Some(reachable) = reachable.as_ref() {
                if !reachable[idx] {
                    continue;
                }
            }
            let step_view = self.trace().step(idx);
            let proof_id = ProofId(idx as u32);
            match self.reconstruct_step(step_view, proof_id, negated_goal) {
                Ok(expr) => self.record_successful_step(idx, proof_id, expr),
                Err(error) => self.record_failed_step(idx, error),
            }
        }
        self.finish_reconstruction(root_idx)
    }

    fn reconstruct_step(
        &mut self,
        step: StepView<'a>,
        step_id: ProofId,
        negated_goal: &Expr,
    ) -> ReconstructResult<Expr> {
        match step {
            StepView::Assume(term_id) => {
                self.stats.assume_steps += 1;
                self.reconstruct_assume(term_id, step_id, negated_goal)
            }
            StepView::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => {
                self.stats.resolution_steps += 1;
                self.reconstruct_resolution(clause, pivot, clause1, clause2, step_id)
            }
            StepView::TheoryLemma {
                theory,
                clause,
                farkas,
                kind,
                lia,
            } => {
                self.stats.theory_lemma_steps += 1;
                self.reconstruct_theory_lemma(theory, clause, farkas, kind, lia, step_id)
            }
            StepView::Step {
                rule,
                rule_name,
                clause,
                premises,
                ..
            } => {
                self.stats.generic_steps += 1;
                self.reconstruct_generic_step(rule, rule_name, clause, premises, step_id)
            }
            StepView::Anchor => Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "subproof anchor".to_string(),
            }),
            StepView::Unknown => Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "unknown proof step variant".to_string(),
            }),
        }
    }
}
