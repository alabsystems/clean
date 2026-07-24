// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theory lemma proof reconstruction: ay TheoryLemma steps → kernel proof terms.
//!
//! Theory lemmas are tautological clauses asserted by theory solvers (EUF, LRA, etc.).
//! Each lemma is a disjunction of literals that is provable from the theory axioms.
//!
//! # Supported Theories
//!
//! - **EUF Transitivity** (`EufTransitive`): `¬(a₁=a₂) ∨ ¬(a₂=a₃) ∨ ... ∨ a₁=aₙ`
//!   Proven via `Classical.em` case splits + `Eq.trans` chain.
//! - **EUF Congruent** (`EufCongruent`): `¬(a₁=b₁) ∨ ... ∨ f(ā)=f(b̄)`
//!   Proven via `Classical.em` case splits + `congrArg`/`congr` chain.
//! - **EUF Congruent Pred** (`EufCongruentPred`): `¬(a₁=b₁) ∨ ... ∨ ¬(P ā) ∨ P(b̄)`
//!   Proven via `Classical.em` case splits + `congr` chain + `Eq.mpr`.
//!
//! # Partially Supported
//!
//! - **LRA Farkas** (`LraFarkas`): Classical.em case splits with Farkas combination
//!   proofs. Concrete and cyclic chains close with kernel-verified arithmetic
//!   lemmas; symbolic or non-chainable arithmetic returns `Err(TrustBoundary)`
//!   so the tactic layer can decide whether to trust ay.
//!
//! # Supported (delegates to Farkas)
//!
//! - **LIA Generic** (`LiaGeneric`): Integer arithmetic lemmas with Farkas certificates.
//!   Structurally identical to LRA Farkas (negated arithmetic bounds over Int-sorted
//!   terms), so delegates to `reconstruct_lra_farkas`. Chain builders already dispatch
//!   on sort (Int vs Real) for le_trans/lt_trans.
//!
//! # Supported (trust-carried)
//!
//! - `BvBitBlast`, `ArrayAxiom`, `Generic`: ay exports these theory lemmas as
//!   `trust`, not as replayable Alethe rules. Reconstruction therefore
//!   synthesizes `trustedAy` clause sub-terms directly, matching `Trust`-step
//!   handling instead of reporting a generic unsupported-step failure.
//!
//! # Unsupported (returns `UnsupportedStep`)
//!
//! - `Other`: future ay theory lemma variants that clean does not recognize yet.
//!
//! # Module Structure
//!
//! - `theory_lemma.rs` — dispatch, clause parsing, chain ordering
//! - `theory_lemma_euf.rs` — Classical.em proof building for EUF transitivity/congruent

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::farkas_certificate::FarkasCertificate;
use super::trace::{FarkasView, LiaAnnotationView, TheoryLemmaView};
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSource;
use crate::bridge::disjunction;

/// Parsed congruent-pred clause components.
pub(super) struct CongruentPredParsed {
    /// Negated equalities: ¬(aᵢ = bᵢ)
    pub(super) neg_eqs: Vec<ClauseEquality>,
    /// Index of the negated predicate ¬(P a₁...aₙ) in the clause.
    pub(super) neg_pred_idx: usize,
    /// Index of the positive predicate P(b₁...bₙ) in the clause.
    pub(super) pos_pred_idx: usize,
}

/// An equality extracted from a clause literal.
pub(super) struct ClauseEquality {
    /// Index of this literal in the clause.
    pub(super) clause_idx: usize,
    /// LHS TermId of the equality.
    pub(super) lhs: TermId,
    /// RHS TermId of the equality.
    pub(super) rhs: TermId,
}

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct a TheoryLemma step by dispatching on the lemma kind.
    pub(super) fn reconstruct_theory_lemma(
        &mut self,
        _theory: &str,
        clause: &[TermId],
        farkas: Option<FarkasView>,
        kind: TheoryLemmaView,
        lia: Option<LiaAnnotationView>,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        match kind {
            TheoryLemmaView::BvBitBlast => {
                // ZERO-TRUST path (C1 slice): when ay attaches a structured
                // `ay_proof::bv_blast_export::BvBlastProof` for the 32-bit
                // bvsub/bvadd identical-operand equality slice, the consumer in
                // `theory_lemma_bv::reconstruct_bv_bitblast` replays it into a
                // kernel `False` proof with NO `trustedAy` subterm (tested via
                // `tests_theory_lemma_bv`). The *live ay trace* does not yet carry
                // that artifact on its `BvBitBlast` theory-lemma view, so this arm
                // keeps the trust fallback until the solver surfaces the proof.
                // HONEST GAP: this fallback emits `trustedAy`; only the
                // BvBlastProof-driven `reconstruct_bv_bitblast` path is zero-trust.
                // NOTE: that path is currently gated behind the off-by-default
                // `ay-bv-blast` feature (upstream `ay` removed
                // `ay_proof::bv_blast_export`); the live default path is this
                // trust fallback either way, so gating it out changes nothing
                // observable here.
                return self.reconstruct_trust_theory_lemma(
                    "BvBitBlast",
                    ResidualTrustSource::TheoryLemmaBvBitBlast,
                    clause,
                    step_id,
                );
            }
            TheoryLemmaView::ArrayAxiom => {
                return self.reconstruct_trust_theory_lemma(
                    "ArrayAxiom",
                    ResidualTrustSource::TheoryLemmaArrayAxiom,
                    clause,
                    step_id,
                );
            }
            TheoryLemmaView::Generic => {
                return self.reconstruct_trust_theory_lemma(
                    "Generic",
                    ResidualTrustSource::TheoryLemmaGeneric,
                    clause,
                    step_id,
                );
            }
            _ => {}
        }

        let props = self.translate_clause_props(clause)?;
        if props.is_empty() {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "theory lemma with empty clause".to_string(),
            });
        }

        let target = disjunction::or_chain_type(&props);

        match kind {
            TheoryLemmaView::EufTransitive => {
                self.reconstruct_euf_transitivity(clause, &props, &target, step_id)
            }
            TheoryLemmaView::EufCongruent => {
                self.reconstruct_euf_congruent(clause, &props, &target, step_id)
            }
            TheoryLemmaView::EufCongruentPred => {
                self.reconstruct_euf_congruent_pred(clause, &props, &target, step_id)
            }
            TheoryLemmaView::LraFarkas | TheoryLemmaView::LiaGeneric => {
                // Log LIA annotation when ay provides one — these carry
                // proof-shape information that future reconstruction passes
                // can use to avoid the trust fallback for integer arithmetic.
                if let Some(ref ann) = lia {
                    tracing::debug!(
                        step = step_id.0,
                        ?ann,
                        "LIA annotation present on theory lemma"
                    );
                }
                // Build a validated certificate once; downstream modules use it
                // instead of re-reading the trace. Handles the LiaGeneric
                // missing-annotation fallback internally.
                let cert = FarkasCertificate::from_trace(farkas, clause, step_id, self.trace())?;
                self.reconstruct_lra_farkas(clause, &cert, &props, &target, step_id)
            }
            TheoryLemmaView::BvBitBlast
            | TheoryLemmaView::ArrayAxiom
            | TheoryLemmaView::Generic => unreachable!("handled before prop translation"),
            TheoryLemmaView::Other => Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("theory lemma kind {:?} not yet supported", kind),
            }),
        }
    }

    /// Reconstruct an EUF transitivity lemma.
    ///
    /// Pattern: `{¬(a₁=a₂), ¬(a₂=a₃), ..., a₁=aₙ}`
    ///
    /// Uses `Classical.em` to case-split on each negated equality:
    /// - If the equality doesn't hold: inject `¬(aᵢ=aᵢ₊₁)` into the clause
    /// - If all equalities hold: build `Eq.trans` chain for the conclusion
    fn reconstruct_euf_transitivity(
        &mut self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let (neg_eqs, pos_eq) = self.parse_euf_clause(clause, step_id)?;
        let chain = self.order_transitivity_chain(&neg_eqs, &pos_eq, step_id)?;
        self.build_em_transitivity_proof(clause, props, target, &chain, &pos_eq, step_id)
    }

    /// Reconstruct a trust-only theory lemma by synthesizing a `trustedAy`
    /// sub-term for the clause.
    fn reconstruct_trust_theory_lemma(
        &mut self,
        kind: &'static str,
        source: ResidualTrustSource,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let proof = self.build_trusted_ay_subterm_for_clause(clause)?;
        self.stats.trust_subterm_steps += 1;
        self.stats.record_residual_source(source);
        tracing::debug!(
            step = step_id.0,
            theory_lemma_kind = kind,
            clause_len = clause.len(),
            "trust-only theory lemma filled with trustedAy sub-term"
        );
        Ok(proof)
    }

    /// Reconstruct an EUF congruent lemma.
    ///
    /// Pattern: `{¬(a₁=b₁), ¬(a₂=b₂), ..., f(ā)=f(b̄)}`
    ///
    /// Uses `Classical.em` to case-split on each negated equality:
    /// - If the equality doesn't hold: inject `¬(aᵢ=bᵢ)` into the clause
    /// - If all equalities hold: build `congrArg` chain for the conclusion
    fn reconstruct_euf_congruent(
        &mut self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let (neg_eqs, pos_eq) = self.parse_euf_clause(clause, step_id)?;
        self.build_em_congruent_proof(clause, props, target, &neg_eqs, &pos_eq, step_id)
    }

    /// Parse a clause into negated equalities and a positive equality.
    pub(super) fn parse_euf_clause(
        &self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<(Vec<ClauseEquality>, ClauseEquality)> {
        let mut neg_eqs = Vec::new();
        let mut pos_eq = None;

        let trace = self.trace();
        for (i, &lit) in clause.iter().enumerate() {
            if let Some(inner) = trace.as_not(lit) {
                if let Some((lhs, rhs)) = trace.as_equality(inner) {
                    neg_eqs.push(ClauseEquality {
                        clause_idx: i,
                        lhs,
                        rhs,
                    });
                }
            } else if let Some((lhs, rhs)) = trace.as_equality(lit) {
                if pos_eq.is_none() {
                    pos_eq = Some(ClauseEquality {
                        clause_idx: i,
                        lhs,
                        rhs,
                    });
                }
            }
        }

        let pos = pos_eq.ok_or_else(|| ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: "EUF lemma: no positive equality found in clause".to_string(),
        })?;

        Ok((neg_eqs, pos))
    }

    /// Reconstruct an EUF congruent-pred lemma.
    ///
    /// Pattern: `{¬(a₁=b₁), ..., ¬(aₙ=bₙ), ¬(P a₁...aₙ), (P b₁...bₙ)}`
    ///
    /// Uses `Classical.em` case splits on each equality and the predicate:
    /// - If any equality doesn't hold: inject negation into clause
    /// - If P(a...) doesn't hold: inject ¬P(a...) into clause
    /// - If all equalities and P(a...) hold: congr chain + Eq.mpr → P(b...)
    fn reconstruct_euf_congruent_pred(
        &mut self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let parsed = self.parse_euf_congruent_pred_clause(clause, step_id)?;
        self.build_em_congruent_pred_proof(clause, props, target, &parsed, step_id)
    }

    /// Parse a congruent-pred clause into its constituent parts.
    ///
    /// Clause: `[¬(= a₁ b₁), ..., ¬(= aₙ bₙ), ¬(P a₁...aₙ), (P b₁...bₙ)]`
    pub(super) fn parse_euf_congruent_pred_clause(
        &self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<CongruentPredParsed> {
        let mut neg_eqs = Vec::new();
        let mut neg_pred_idx = None;
        let mut pos_pred_idx = None;

        let trace = self.trace();
        for (i, &lit) in clause.iter().enumerate() {
            if let Some(inner) = trace.as_not(lit) {
                if let Some((lhs, rhs)) = trace.as_equality(inner) {
                    neg_eqs.push(ClauseEquality {
                        clause_idx: i,
                        lhs,
                        rhs,
                    });
                } else {
                    // Negated non-equality: ¬(P a...)
                    neg_pred_idx = Some(i);
                }
            } else {
                // Positive non-equality: P(b...)
                if trace.as_equality(lit).is_none() {
                    pos_pred_idx = Some(i);
                }
            }
        }

        let neg_pred = neg_pred_idx.ok_or_else(|| ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: "EUF congruent-pred: no negated predicate found".to_string(),
        })?;
        let pos_pred = pos_pred_idx.ok_or_else(|| ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: "EUF congruent-pred: no positive predicate found".to_string(),
        })?;

        Ok(CongruentPredParsed {
            neg_eqs,
            neg_pred_idx: neg_pred,
            pos_pred_idx: pos_pred,
        })
    }

    /// Check if a term is an equality `(= a b)` and return the operands.
    ///
    /// Delegates to the trace adapter (#2451).
    pub(super) fn as_equality(&self, term_id: TermId) -> Option<(TermId, TermId)> {
        self.trace().as_equality(term_id)
    }

    /// Order negated equalities into a transitivity chain from conclusion LHS to RHS.
    ///
    /// Given negated equalities like `{a=b, c=d, b=c}` and conclusion `a=d`,
    /// produces the ordered chain `[(a=b, false), (b=c, false), (c=d, false)]`
    /// where the bool indicates whether Eq.symm is needed.
    pub(super) fn order_transitivity_chain(
        &self,
        neg_eqs: &[ClauseEquality],
        conclusion: &ClauseEquality,
        step_id: ProofId,
    ) -> ReconstructResult<Vec<(usize, bool)>> {
        use std::collections::{HashMap, VecDeque};

        // Build adjacency: node → [(neighbor, clause_index, needs_symm)]
        // Use clause_idx (position in original clause) so callers can index
        // clause[] and props[] directly from the chain values.
        let mut adj: HashMap<TermId, Vec<(TermId, usize, bool)>> = HashMap::new();
        for eq in neg_eqs.iter() {
            adj.entry(eq.lhs)
                .or_default()
                .push((eq.rhs, eq.clause_idx, false));
            adj.entry(eq.rhs)
                .or_default()
                .push((eq.lhs, eq.clause_idx, true));
        }

        // BFS with parent pointers instead of cloning path vectors.
        let mut parent: HashMap<TermId, (TermId, usize, bool)> = HashMap::new();
        let mut queue: VecDeque<TermId> = VecDeque::new();
        queue.push_back(conclusion.lhs);

        while let Some(current) = queue.pop_front() {
            if current == conclusion.rhs {
                // Reconstruct path backwards from parent pointers
                let mut path = Vec::new();
                let mut node = current;
                while node != conclusion.lhs {
                    let &(prev, eq_idx, needs_symm) = parent
                        .get(&node)
                        .expect("invariant: BFS visited node has parent entry");
                    path.push((eq_idx, needs_symm));
                    node = prev;
                }
                path.reverse();
                return Ok(path);
            }
            if let Some(neighbors) = adj.get(&current) {
                for &(neighbor, eq_idx, needs_symm) in neighbors {
                    if neighbor != conclusion.lhs && !parent.contains_key(&neighbor) {
                        parent.insert(neighbor, (current, eq_idx, needs_symm));
                        queue.push_back(neighbor);
                    }
                }
            }
        }

        Err(ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: "EUF transitivity: cannot order equalities into chain".to_string(),
        })
    }
}
