// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hypothesis assertion for the SMT bridge.
//!
//! Provides two methods for adding hypotheses to the SMT context (#2391):
//! - `add_hypothesis`: Assert a proposition with optional FVarId and premise origin
//! - `add_hypothesis_with_prefix_analysis`: Quantifier-aware assertion with Skolemization

use super::expr_classifier::LogicalForm;
use super::scoring::QuantifierPriorityScorer;
use super::{BridgeResult, PendingForall, QuantifierOrigin, SmtBridge};
use crate::smt::TheoryLiteral;
use clean_kernel::{Expr, FVarId};

/// Options for hypothesis assertion (#2391).
///
/// Consolidates the optional parameters for `add_hypothesis` and
/// `add_hypothesis_with_prefix_analysis`.
#[derive(Clone, Debug, Default)]
pub struct HypothesisOpts {
    /// FVarId for proof reconstruction (links hypothesis to local context entry).
    pub fvar: Option<FVarId>,
    /// Quantifier origin for E-matching relevance scoring.
    pub origin: Option<QuantifierOrigin>,
}

impl HypothesisOpts {
    /// Create default options (no fvar, no origin).
    pub fn new() -> Self {
        Self::default()
    }

    /// Set the FVarId for proof reconstruction.
    pub fn with_fvar(mut self, fvar: FVarId) -> Self {
        self.fvar = Some(fvar);
        self
    }

    /// Set the quantifier origin for E-matching scoring.
    pub fn with_origin(mut self, origin: QuantifierOrigin) -> Self {
        self.origin = Some(origin);
        self
    }
}

impl<'env> SmtBridge<'env> {
    /// Assert a hypothesis with no FVarId or origin.
    #[inline]
    pub fn add_hypothesis(&mut self, hyp: &Expr) -> BridgeResult<()> {
        self.add_hypothesis_with_opts(hyp, HypothesisOpts::new())
    }

    /// Assert a hypothesis with optional FVarId for proof reconstruction.
    #[inline]
    pub fn add_hypothesis_with_fvar(
        &mut self,
        hyp: &Expr,
        fvar: Option<FVarId>,
    ) -> BridgeResult<()> {
        let opts = match fvar {
            Some(fvar) => HypothesisOpts::new().with_fvar(fvar),
            None => HypothesisOpts::new(),
        };
        self.add_hypothesis_with_opts(hyp, opts)
    }

    /// Assert a hypothesis with optional FVarId and premise origin.
    #[inline]
    pub fn add_hypothesis_with_premise(
        &mut self,
        hyp: &Expr,
        fvar: Option<FVarId>,
        origin: Option<QuantifierOrigin>,
    ) -> BridgeResult<()> {
        let opts = match (fvar, origin) {
            (Some(fvar), Some(origin)) => HypothesisOpts::new().with_fvar(fvar).with_origin(origin),
            (Some(fvar), None) => HypothesisOpts::new().with_fvar(fvar),
            (None, Some(origin)) => HypothesisOpts::new().with_origin(origin),
            (None, None) => HypothesisOpts::new(),
        };
        self.add_hypothesis_with_opts(hyp, opts)
    }

    /// Assert a hypothesis with full options struct (#2391).
    ///
    /// Primary consolidated API — subsumes `add_hypothesis`, `add_hypothesis_with_fvar`,
    /// and `add_hypothesis_with_premise`.
    pub(crate) fn add_hypothesis_with_opts(
        &mut self,
        hyp: &Expr,
        opts: HypothesisOpts,
    ) -> BridgeResult<()> {
        self.add_hypothesis_inner(hyp, opts.fvar, opts.origin)
    }

    /// Core hypothesis assertion implementation.
    ///
    /// Wrapped with `stack_safe` at entry to ensure the entire function body
    /// (including Forall/Exists arms that do significant work before recursing)
    /// gets stack growth on deep alternating-quantifier chains (#3045).
    fn add_hypothesis_inner(
        &mut self,
        hyp: &Expr,
        fvar: Option<FVarId>,
        origin: Option<QuantifierOrigin>,
    ) -> BridgeResult<()> {
        crate::bridge::stack_safe(|| self.add_hypothesis_inner_impl(hyp, fvar, origin))
    }

    /// Inner implementation of hypothesis assertion, called within a stack_safe guard.
    fn add_hypothesis_inner_impl(
        &mut self,
        hyp: &Expr,
        fvar: Option<FVarId>,
        origin: Option<QuantifierOrigin>,
    ) -> BridgeResult<()> {
        if let Some(id) = fvar {
            if self.current_hypothesis_fvar != Some(id) {
                self.prop_hypotheses.push((id, hyp.clone()));
            }
        } // #2442
          // Determine effective FVarId for clause origin tracking (#2442 Phase 2B).
          // Explicit fvar takes precedence over the inherited context.
        let effective_fvar = fvar.or(self.current_hypothesis_fvar);
        match self.classify_prop(hyp) {
            LogicalForm::Eq { ty, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                // Populate term_to_type so proof reconstruction knows the type
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let eq_lit = TheoryLiteral::Eq(t1, t2);
                let pre_count = self.smt.num_clauses();
                let _ = self.smt.assert_eq(t1, t2);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&eq_lit, effective_fvar);
                // Track the hypothesis for proof reconstruction
                // Only store the canonical (original) direction
                if let Some(fvar_id) = effective_fvar {
                    self.eq_hypothesis_canonical.insert((t1, t2), fvar_id);
                    if let Some(eq) = self.equality_theory_mut() {
                        eq.register_hypothesis(t1, t2, fvar_id);
                    }
                }
                Ok(())
            }
            LogicalForm::Neq { ty, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                // Populate term_to_type for disequality terms too
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let neq_lit = TheoryLiteral::Neq(t1, t2);
                let pre_count = self.smt.num_clauses();
                let _ = self.smt.assert_neq(t1, t2);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&neq_lit, effective_fvar);
                Ok(())
            }
            // Arithmetic comparisons as hypotheses
            LogicalForm::Lt { ty, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                // Populate term_to_type for comparison terms (Part of #2069)
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let lt_lit = TheoryLiteral::Lt(t1, t2);
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![lt_lit.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&lt_lit, effective_fvar);
                Ok(())
            }
            LogicalForm::Le { ty, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let le_lit = TheoryLiteral::Le(t1, t2);
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![le_lit.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&le_lit, effective_fvar);
                Ok(())
            }
            LogicalForm::Gt { ty, lhs, rhs } => {
                // a > b ≡ b < a
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let gt_lit = TheoryLiteral::Lt(t2, t1);
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![gt_lit.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&gt_lit, effective_fvar);
                Ok(())
            }
            LogicalForm::Ge { ty, lhs, rhs } => {
                // a ≥ b ≡ b ≤ a
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                self.term_to_type.insert(t1, ty.clone());
                self.term_to_type.insert(t2, ty.clone());
                let ge_lit = TheoryLiteral::Le(t2, t1);
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![ge_lit.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&ge_lit, effective_fvar);
                Ok(())
            }
            LogicalForm::And(p, q) => {
                // P ∧ Q means both P and Q hold.
                // Propagate the FVarId context so sub-clauses inherit it (#2442 Phase 2B).
                let prev_fvar = self.current_hypothesis_fvar;
                if effective_fvar.is_some() {
                    self.current_hypothesis_fvar = effective_fvar;
                }
                let result = crate::bridge::stack_safe(|| {
                    self.add_hypothesis_inner(&p, fvar, origin.clone())?;
                    self.add_hypothesis_inner(&q, fvar, origin.clone())?;
                    Ok(())
                });
                self.current_hypothesis_fvar = prev_fvar;
                result
            }
            LogicalForm::Implies(p, q) => {
                // P → Q as a clause: ¬P ∨ Q
                let np = self.prop_to_literal(&p, false)?;
                let pq = self.prop_to_literal(&q, true)?;
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![np.clone(), pq.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_clause_literal_origins(&[np, pq], effective_fvar);
                Ok(())
            }
            LogicalForm::Not(p) => {
                // ¬P means P is false
                let np = self.prop_to_literal(&p, false)?;
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![np.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&np, effective_fvar);
                Ok(())
            }
            LogicalForm::True => Ok(()), // No information
            LogicalForm::False => {
                // False hypothesis - anything follows
                // Add empty clause to make UNSAT
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![]);
                self.record_clause_origins(pre_count, effective_fvar);
                Ok(())
            }
            LogicalForm::Or(p, q) => {
                // P ∨ Q as a clause
                let pp = self.prop_to_literal(&p, true)?;
                let pq = self.prop_to_literal(&q, true)?;
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![pp.clone(), pq.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_clause_literal_origins(&[pp, pq], effective_fvar);
                Ok(())
            }
            LogicalForm::Forall {
                ref binder_type,
                ref body,
            } => {
                // ∀ x : T, P(x) as hypothesis
                // Strategy: Extract E-matching triggers and store for later instantiation
                // The actual instantiation happens in prove() after the E-graph is populated

                let (bound_types, flat_body) = self.flatten_forall(binder_type, body);
                let bound_count = u32::try_from(bound_types.len())
                    .expect("invariant: forall bound-variable count fits in u32");
                let pending_bound_vars: Vec<u32> = (0..bound_count).collect();
                let triggers = self.extract_ematch_triggers(&flat_body, &pending_bound_vars);

                if !triggers.is_empty() {
                    let pending_origin =
                        QuantifierOrigin::inherit_or_local(origin.clone(), effective_fvar);

                    // Store for E-matching instantiation with priority scoring
                    let pending = PendingForall {
                        _tys: bound_types.clone(),
                        body: flat_body.clone(),
                        triggers,
                        bound_vars: pending_bound_vars.clone(),
                        priority: 0,
                        instantiation_count: 0,
                        origin: pending_origin,
                    };
                    let scorer = QuantifierPriorityScorer::new();
                    let priority = scorer.score(&pending);
                    self.pending_foralls.push(PendingForall {
                        priority,
                        ..pending
                    });
                }

                // Also instantiate with a fresh witness as fallback
                // This ensures we don't lose any proof power
                let mut witness_terms = Vec::new();
                for (i, bound_ty) in bound_types.iter().enumerate() {
                    let skolem_name = format!("forall_witness_{}_{}", i, self.fresh_counter);
                    self.fresh_counter += 1;
                    witness_terms.push(self.create_witness_term(&skolem_name, bound_ty));
                }
                let witness_bound_vars = Self::flattened_bvar_indices(bound_count);

                if let Some(inst) = self.instantiate_body_with_terms(
                    &flat_body,
                    &witness_bound_vars,
                    &witness_terms,
                ) {
                    let prev_fvar = self.current_hypothesis_fvar;
                    if effective_fvar.is_some() {
                        self.current_hypothesis_fvar = effective_fvar;
                    }
                    let result = self.add_hypothesis_inner(&inst, fvar, origin);
                    self.current_hypothesis_fvar = prev_fvar;
                    result?;
                }
                Ok(())
            }
            LogicalForm::Exists {
                ref binder_type,
                ref body,
            } => {
                // ∃ x : T, P(x) as hypothesis means there exists a witness
                // Flatten nested exists: ∃ x : A, ∃ y : B, P(x, y) → create witnesses for both
                let (bound_types, flat_body) = self.flatten_exists(binder_type, body);
                let bound_count = u32::try_from(bound_types.len())
                    .expect("invariant: exists bound-variable count fits in u32");
                let witness_bound_vars = Self::flattened_bvar_indices(bound_count);

                // Create Skolem witnesses for all bound variables
                let mut witness_terms = Vec::new();
                for (i, bound_ty) in bound_types.iter().enumerate() {
                    let skolem_name = format!("exists_witness_{}_{}", i, self.fresh_counter);
                    self.fresh_counter += 1;
                    witness_terms.push(self.create_witness_term(&skolem_name, bound_ty));
                }

                // Instantiate the body with all Skolem witnesses
                if let Some(inst) = self.instantiate_body_with_terms(
                    &flat_body,
                    &witness_bound_vars,
                    &witness_terms,
                ) {
                    let prev_fvar = self.current_hypothesis_fvar;
                    if effective_fvar.is_some() {
                        self.current_hypothesis_fvar = effective_fvar;
                    }
                    let result = self.add_hypothesis_inner(&inst, fvar, origin);
                    self.current_hypothesis_fvar = prev_fvar;
                    result
                } else {
                    Ok(()) // Conservative: can't use this hypothesis
                }
            }
            // Iff and arithmetic are folded by classify_prop; Atom is the catch-all
            LogicalForm::Iff(..)
            | LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. }
            | LogicalForm::Atom(_) => {
                // Unknown atom - create boolean and assert it
                let lit = self.prop_to_literal(hyp, true)?;
                let pre_count = self.smt.num_clauses();
                self.smt.add_clause(vec![lit.clone()]);
                self.record_clause_origins(pre_count, effective_fvar);
                self.record_theory_literal_origin(&lit, effective_fvar);
                Ok(())
            }
        }
    }

    /// Record clause origins for any new clauses added since `pre_count` (#2442 Phase 2B).
    ///
    /// Fills `clause_origins` so that `clause_origins[i] = Some(fvar)` for each
    /// new clause index `i` in `[pre_count, current_count)`. This allows the
    /// UNSAT core to be mapped back to hypothesis FVarIds.
    fn record_clause_origins(&mut self, pre_count: usize, fvar: Option<FVarId>) {
        let post_count = self.smt.num_clauses();
        // Extend clause_origins to cover all new clause indices
        while self.clause_origins.len() < post_count {
            self.clause_origins.push(None);
        }
        // Tag new clauses with the hypothesis FVarId
        if let Some(id) = fvar {
            for entry in self.clause_origins[pre_count..post_count].iter_mut() {
                *entry = Some(id);
            }
        }
    }
}
