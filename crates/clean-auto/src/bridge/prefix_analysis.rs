// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier prefix analysis and Skolemization for hypothesis assertion.
//!
//! Extracted from `hypothesis.rs` to keep file sizes under 500 lines.
//! Contains methods for analyzing mixed quantifier scopes (∀∃ alternation)
//! and applying proper Skolemization before hypothesis assertion.

use super::quantifier::{QuantifierKind, QuantifierPrefix};
use super::scoring::QuantifierPriorityScorer;
use super::HypothesisOpts;
use super::{BridgeError, BridgeResult, PendingForall, QuantifierOrigin, SmtBridge};
use clean_kernel::{Expr, FVarId};
use std::collections::HashMap;

impl<'env> SmtBridge<'env> {
    /// Analyze a hypothesis for its quantifier structure and add it to the SMT context.
    ///
    /// This function handles mixed quantifier scopes with proper Skolemization:
    /// - For ∀x. ∃y. P(x,y): creates Skolem function sk_y(x) depending on x
    /// - For ∃x. ∀y. P(x,y): creates Skolem constant sk_x, then handles ∀y universally
    ///
    /// Returns the alternation depth for proof strategy selection.
    ///
    /// Backward-compatible wrapper — calls `add_hypothesis_with_prefix_analysis_opts`
    /// with no origin.
    pub fn add_hypothesis_with_prefix_analysis(&mut self, hyp: &Expr) -> BridgeResult<u32> {
        self.add_hypothesis_with_prefix_analysis_opts(hyp, HypothesisOpts::default())
    }

    /// Quantifier-aware hypothesis assertion with full options (#2391).
    ///
    /// Analyzes the quantifier structure and applies proper Skolemization for
    /// mixed quantifier scopes. Returns the alternation depth for proof strategy
    /// selection.
    pub(crate) fn add_hypothesis_with_prefix_analysis_opts(
        &mut self,
        hyp: &Expr,
        opts: HypothesisOpts,
    ) -> BridgeResult<u32> {
        let prop = self.classify_prop(hyp);
        let prefix = self.flatten_quantifier_prefix(&prop)?;

        if prefix.is_empty() {
            // No quantifiers, use normal hypothesis handling
            self.add_hypothesis_with_premise(hyp, opts.fvar, opts.origin)?;
            return Ok(0);
        }

        let alternation_depth = prefix.alternation_depth();

        // For simple cases (purely universal or purely existential), use existing handlers
        if prefix.is_purely_universal() {
            self.add_hypothesis_with_premise(hyp, opts.fvar, opts.origin)?;
            return Ok(alternation_depth);
        }

        if prefix.is_purely_existential() {
            self.add_hypothesis_with_premise(hyp, opts.fvar, opts.origin)?;
            return Ok(alternation_depth);
        }

        // Mixed quantifier scope: use proper Skolemization
        self.handle_mixed_quantifier_hypothesis_with_origin(&prefix, opts.origin, opts.fvar)?;

        Ok(alternation_depth)
    }

    /// Backward-compatible alias for `add_hypothesis_with_prefix_analysis_opts`.
    pub fn add_hypothesis_with_prefix_analysis_and_premise(
        &mut self,
        hyp: &Expr,
        origin: Option<QuantifierOrigin>,
    ) -> BridgeResult<u32> {
        self.add_hypothesis_with_prefix_analysis_opts(hyp, HypothesisOpts { fvar: None, origin })
    }

    /// Handle a hypothesis with mixed quantifier scope using proper Skolemization.
    ///
    /// For ∀x. ∃y. P(x,y):
    /// - Create a fresh Skolem function symbol sk_y
    /// - The Skolem term for y is sk_y(x), depending on x
    /// - Add the instantiation: P(x, sk_y(x)) as a universal hypothesis
    ///
    /// For ∃x. ∀y. P(x,y):
    /// - Create a fresh Skolem constant sk_x (no dependencies)
    /// - Add P(sk_x, y) as a universal hypothesis over y
    pub(super) fn handle_mixed_quantifier_hypothesis_with_origin(
        &mut self,
        prefix: &QuantifierPrefix,
        origin: Option<QuantifierOrigin>,
        fvar: Option<FVarId>,
    ) -> BridgeResult<()> {
        let deps = prefix.skolem_dependencies();

        // Create Skolem terms for existential variables
        let mut skolem_terms: HashMap<u32, crate::smt::TermId> = HashMap::new();
        let mut forall_witnesses: HashMap<u32, crate::smt::TermId> = HashMap::new();

        // First pass: create witnesses for universal variables
        for binder in &prefix.binders {
            if binder.kind == QuantifierKind::Forall {
                let witness_name =
                    format!("forall_witness_{}_{}", binder.index, self.fresh_counter);
                self.fresh_counter += 1;
                forall_witnesses.insert(
                    binder.index,
                    self.create_witness_term(&witness_name, &binder.ty),
                );
            }
        }

        // Second pass: create Skolem terms for existential variables
        for binder in &prefix.binders {
            if binder.kind == QuantifierKind::Exists {
                let dep_indices = deps.get(&binder.index).cloned().unwrap_or_default();

                if dep_indices.is_empty() {
                    // No dependencies: simple Skolem constant
                    let skolem_name = format!("skolem_{}_{}", binder.index, self.fresh_counter);
                    self.fresh_counter += 1;
                    skolem_terms.insert(
                        binder.index,
                        self.create_witness_term(&skolem_name, &binder.ty),
                    );
                } else {
                    // Has dependencies: Skolem function applied to preceding universals
                    let skolem_fn_name =
                        format!("skolem_fn_{}_{}", binder.index, self.fresh_counter);
                    self.fresh_counter += 1;
                    let skolem_fn = self.smt.const_term(skolem_fn_name.clone());

                    // Apply Skolem function to all preceding universal witnesses
                    let mut skolem_term = skolem_fn;
                    for dep_idx in &dep_indices {
                        if let Some(&witness) = forall_witnesses.get(dep_idx) {
                            skolem_term = self.smt.app_term(
                                format!("{skolem_fn_name}_{dep_idx}"),
                                vec![skolem_term, witness],
                            );
                        }
                    }
                    // Register the applied term so instantiate_body_with_terms can find it
                    self.register_witness_for_term(skolem_term, &binder.ty);
                    skolem_terms.insert(binder.index, skolem_term);
                }
            }
        }

        // Build the substitution list
        let mut bound_vars = Vec::new();
        let mut witness_terms = Vec::new();

        for binder in &prefix.binders {
            bound_vars.push(binder.index);
            match binder.kind {
                QuantifierKind::Forall => {
                    witness_terms.push(*forall_witnesses.get(&binder.index).ok_or_else(|| {
                        BridgeError::TranslationFailed {
                            context: format!("missing forall witness for binder {}", binder.index),
                        }
                    })?);
                }
                QuantifierKind::Exists => {
                    witness_terms.push(*skolem_terms.get(&binder.index).ok_or_else(|| {
                        BridgeError::TranslationFailed {
                            context: format!("missing skolem term for binder {}", binder.index),
                        }
                    })?);
                }
            }
        }

        // Instantiate the body
        if let Some(inst) =
            self.instantiate_body_with_terms(&prefix.body, &bound_vars, &witness_terms)
        {
            self.add_hypothesis_with_opts(
                &inst,
                HypothesisOpts {
                    fvar,
                    origin: origin.clone(),
                },
            )?;
        }

        // Also store the universal part for E-matching if there are universals
        let forall_indices = prefix.forall_indices();
        if !forall_indices.is_empty() {
            let triggers = self.extract_ematch_triggers(&prefix.body, &forall_indices);
            if !triggers.is_empty() {
                let tys: Vec<Expr> = prefix
                    .binders
                    .iter()
                    .filter(|b| b.kind == QuantifierKind::Forall)
                    .map(|b| b.ty.clone())
                    .collect();

                let pending_origin = QuantifierOrigin::inherit_or_local(origin, fvar)
                    .or(Some(QuantifierOrigin::Synthesized));

                let pending = PendingForall {
                    _tys: tys,
                    body: prefix.body.clone(),
                    triggers,
                    bound_vars: forall_indices,
                    priority: 0,
                    instantiation_count: 0,
                    origin: pending_origin,
                };
                // Compute initial priority using the scorer
                let scorer = QuantifierPriorityScorer::new();
                let priority = scorer.score(&pending);
                self.pending_foralls.push(PendingForall {
                    priority,
                    ..pending
                });
            }
        }

        Ok(())
    }
}
