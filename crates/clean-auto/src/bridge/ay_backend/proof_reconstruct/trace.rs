// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Borrowing proof-trace adapter: matches raw ay_core proof payload enums and exposes local
//! view types for the rest of proof_reconstruct. Design: `designs/2026-03-11-2451-*.md`
#![allow(dead_code)]

use super::trace_convert::{
    constant_view, farkas_view, lia_annotation_view, rule_view, theory_lemma_view,
};
use super::ReconstructionError;
use ay_core::{
    FarkasAnnotation, Proof, ProofId, ProofStep, Symbol, TermData, TermId, TermStore, TheoryLit,
};
use num_rational::Rational64;

/// View of a proof step, borrowing data from the underlying ay proof.
#[derive(Debug)]
pub(crate) enum StepView<'a> {
    Assume(TermId),
    Resolution {
        clause: &'a [TermId],
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
    },
    TheoryLemma {
        theory: &'a str,
        clause: &'a [TermId],
        farkas: Option<FarkasView>,
        kind: TheoryLemmaView,
        /// LIA-specific proof annotation, when ay provided one.
        lia: Option<LiaAnnotationView>,
    },
    Step {
        rule: RuleView,
        rule_name: &'a str,
        clause: &'a [TermId],
        premises: &'a [ProofId],
        args: &'a [TermId],
    },
    Anchor,
    Unknown,
}

/// View of a ay term, borrowing data from the underlying term store.
#[derive(Debug)]
pub(crate) enum TermView<'a> {
    Const(ConstantView<'a>),
    Var {
        name: &'a str,
        id: u32,
    },
    NamedApp {
        name: &'a str,
        args: &'a [TermId],
    },
    IndexedApp {
        name: &'a str,
        args: &'a [TermId],
    },
    Not(TermId),
    Ite(TermId, TermId, TermId),
    Let {
        body: TermId,
    },
    Forall {
        vars: &'a [(String, ay::Sort)],
        body: TermId,
    },
    Exists {
        vars: &'a [(String, ay::Sort)],
        body: TermId,
    },
    Unknown,
}

/// View of a ay constant.
#[derive(Debug)]
pub(crate) enum ConstantView<'a> {
    Bool(bool),
    Int(&'a num_bigint::BigInt),
    Rational(&'a ay_core::RationalWrapper),
    BitVec {
        value: &'a num_bigint::BigInt,
        width: u32,
    },
    String(&'a str),
    Unknown,
}

/// Alethe rule view — only the variants clean dispatches on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RuleView {
    ThResolution,
    Or,
    OrPos,
    OrNeg,
    EquivPos1,
    EquivPos2,
    EquivNeg1,
    EquivNeg2,
    XorPos1,
    XorPos2,
    XorNeg1,
    XorNeg2,
    AndPos(u32),
    AndNeg,
    /// `eq_reflexive`: ⊢ (= t t). Reconstructs to `@Eq.refl.{u} ty t`.
    EqReflexive,
    /// `symm`: premise ⊢ (= a b); clause ⊢ (= b a). Reconstructs to `@Eq.symm.{u} ty a b <premise>`.
    Symm,
    /// `trans`: premises ⊢ (= t₀ t₁),…,(= tₙ₋₁ tₙ); clause ⊢ (= t₀ tₙ). Left-nested `@Eq.trans.{u}` chain.
    Trans,
    True,
    False,
    /// `resolution`: n-ary propositional resolution (no inline pivot). Binary
    /// case delegates to `reconstruct_th_resolution`; n-ary fails closed.
    Resolution,
    /// `contraction`: deduplicate a clause's literals. Premise proves
    /// `P₀ ∨ … ∨ Pₙ` (with duplicates); conclusion is the deduplicated
    /// disjunction. Reconstructed via an `Or.rec` walk — zero added trust.
    Contraction,
    /// `eq_congruent`: ⊢ ¬(=a₁ b₁) ∨ … ∨ (= (f ā) (f b̄)). Reuses the EUF
    /// congruent Classical.em + congrArg/congr machinery.
    EqCongruent,
    /// `cong`: premised congruence. Unit conclusion (= (f ā) (f b̄)) from
    /// per-argument premise equalities; reconstructs a congrArg/congr chain.
    Cong,
    Trust,
    Hole,
    Other,
}

/// View of a theory lemma kind — only the variants clean consumes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryLemmaView {
    EufTransitive,
    EufCongruent,
    EufCongruentPred,
    LraFarkas,
    LiaGeneric,
    BvBitBlast,
    ArrayAxiom,
    Generic,
    Other,
}

/// View of a Farkas certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct FarkasView {
    pub(crate) coefficient_count: usize,
    pub(crate) is_valid: bool,
    pub(crate) all_unit_coefficients: bool,
}

/// clean-local view of ay's `LiaAnnotation` for LIA theory lemma proof shapes.
///
/// When present on a `TheoryLemma` step, this tells the proof reconstructor
/// which LIA-specific proof strategy to apply instead of treating the lemma
/// as a generic Farkas combination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LiaAnnotationView {
    /// Bounds gap: the effective integer bounds are contradictory
    /// (e.g., `x >= 6 AND x <= 5`).
    BoundsGap,
    /// Divisibility conflict: GCD of constraint coefficients does not divide
    /// the constant (e.g., `2|x AND x = 3`).
    Divisibility,
    /// Cutting plane: a Farkas combination followed by integer rounding
    /// (division + ceiling) produces a contradiction. Carries the divisor
    /// for the rounding step.
    CuttingPlane {
        /// Divisor for the cutting-plane rounding step (must be > 0).
        divisor: i64,
    },
}

/// Borrowing adapter over a ay proof and term store.
pub(crate) struct ProofTrace<'a> {
    proof: Option<&'a Proof>,
    terms: &'a TermStore,
}

impl<'a> ProofTrace<'a> {
    pub(crate) fn new(proof: &'a Proof, terms: &'a TermStore) -> Self {
        Self {
            proof: Some(proof),
            terms,
        }
    }

    pub(crate) fn terms(&self) -> &'a TermStore {
        self.terms
    }

    pub(crate) fn without_proof(terms: &'a TermStore) -> Self {
        Self { proof: None, terms }
    }

    pub(crate) fn attach_proof(&mut self, proof: &'a Proof) {
        self.proof = Some(proof);
    }

    pub(crate) fn step_count(&self) -> usize {
        self.proof.map_or(0, |proof| proof.steps.len())
    }

    /// Clause positions whose Farkas coefficients are non-zero.
    pub(crate) fn farkas_active_clause_indices(&self, step_id: ProofId) -> Option<Vec<usize>> {
        let proof = self.proof?;
        let ProofStep::TheoryLemma {
            farkas: Some(farkas),
            ..
        } = proof.steps.get(step_id.0 as usize)?
        else {
            return None;
        };
        Some(
            farkas
                .coefficients
                .iter()
                .enumerate()
                .filter_map(|(idx, coeff)| (*coeff != 0_i64.into()).then_some(idx))
                .collect(),
        )
    }

    /// Non-zero Farkas coefficients as `(clause_idx, coeff)` pairs. Part of #2581.
    pub(crate) fn farkas_active_coefficients(
        &self,
        step_id: ProofId,
    ) -> Option<Vec<(usize, Rational64)>> {
        let proof = self.proof?;
        let ProofStep::TheoryLemma {
            farkas: Some(farkas),
            ..
        } = proof.steps.get(step_id.0 as usize)?
        else {
            return None;
        };
        Some(
            farkas
                .coefficients
                .iter()
                .enumerate()
                .filter_map(|(idx, c)| (*c != Rational64::from_integer(0)).then_some((idx, *c)))
                .collect(),
        )
    }

    /// Validate the active Farkas subset via ay-core's full checker.
    pub(crate) fn validate_farkas_active_conflict(
        &self,
        clause: &[TermId],
        step_id: ProofId,
        active_coefficients: &[(usize, Rational64)],
    ) -> Result<(), ReconstructionError> {
        let (mut conflict, mut coeffs) = (Vec::new(), Vec::new());
        for &(idx, coeff) in active_coefficients {
            let inner =
                self.as_not(clause[idx])
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: format!(
                            "Farkas active literal at clause index {idx} is not a negation"
                        ),
                    })?;
            conflict.push(TheoryLit::new(inner, true));
            coeffs.push(coeff);
        }
        ay_core::proof_validation::verify_farkas_conflict_lits_full(
            self.terms,
            &conflict,
            &FarkasAnnotation::new(coeffs),
        )
        .map_err(|e| {
            ReconstructionError::trust_boundary(
                step_id.0,
                "LRA",
                format!("Farkas semantic validation failed: {e}"),
            )
        })
    }

    /// Get a local view of the proof step at the given index.
    pub(crate) fn step(&self, idx: usize) -> StepView<'a> {
        match self.proof.and_then(|proof| proof.steps.get(idx)) {
            Some(step) => self.step_view(step),
            None => StepView::Unknown,
        }
    }

    /// Get a local view from a ProofId.
    pub(crate) fn step_by_id(&self, id: ProofId) -> StepView<'a> {
        self.step(id.0 as usize)
    }

    fn step_view(&self, step: &'a ProofStep) -> StepView<'a> {
        match step {
            ProofStep::Assume(t) => StepView::Assume(*t),
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => StepView::Resolution {
                clause,
                pivot: *pivot,
                clause1: *clause1,
                clause2: *clause2,
            },
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                kind,
                lia,
            } => StepView::TheoryLemma {
                theory,
                clause,
                farkas: farkas.as_ref().map(farkas_view),
                kind: theory_lemma_view(kind),
                lia: lia.as_ref().map(lia_annotation_view),
            },
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => StepView::Step {
                rule: rule_view(rule),
                rule_name: rule.name(),
                clause,
                premises,
                args,
            },
            ProofStep::Anchor { .. } => StepView::Anchor,
            _ => StepView::Unknown,
        }
    }

    /// Extract the clause literal list from the step at `idx`.
    ///
    /// For Assume steps, the TermId may be a compound `Or` expression
    /// that gets flattened. For Resolution/TheoryLemma/Step, the clause
    /// field already lists individual literals.
    pub(crate) fn clause_of_step(&self, idx: usize) -> Vec<TermId> {
        match self.proof.and_then(|proof| proof.steps.get(idx)) {
            Some(step) => self.clause_of_step_inner(step),
            None => vec![],
        }
    }

    pub(crate) fn clause_of_step_by_id(&self, id: ProofId) -> Vec<TermId> {
        self.clause_of_step(id.0 as usize)
    }

    fn clause_of_step_inner(&self, step: &ProofStep) -> Vec<TermId> {
        match step {
            ProofStep::Assume(t) => self.flatten_or(*t),
            ProofStep::Resolution { clause, .. } => clause.clone(),
            ProofStep::TheoryLemma { clause, .. } => clause.clone(),
            ProofStep::Step { clause, .. } => clause.clone(),
            ProofStep::Anchor { .. } => vec![],
            _ => vec![],
        }
    }

    /// Get a local view of the term at `id`.
    pub(crate) fn term(&self, id: TermId) -> TermView<'a> {
        term_view(self.terms, id)
    }

    /// If the term is `Not(inner)`, return the inner TermId.
    pub(crate) fn as_not(&self, id: TermId) -> Option<TermId> {
        not_inner(self.terms, id)
    }

    /// If the term is `App(Named(name), args)`, return `(name, args)`.
    pub(crate) fn as_named_app(&self, id: TermId) -> Option<(&'a str, &'a [TermId])> {
        match self.terms.get(id) {
            TermData::App(Symbol::Named(name), args) => Some((name, args)),
            _ => None,
        }
    }

    /// If the term is `Var(name, _)`, return the variable name.
    pub(crate) fn as_var_name(&self, id: TermId) -> Option<&'a str> {
        match self.terms.get(id) {
            TermData::Var(name, _) => Some(name),
            _ => None,
        }
    }

    /// Get the sort of a term.
    pub(crate) fn sort(&self, id: TermId) -> &'a ay::Sort {
        self.terms.sort(id)
    }

    /// Flatten an Or-expression into its individual disjunct TermIds.
    ///
    /// `Or(a, Or(b, c))` → `[a, b, c]`
    /// `p` → `[p]` (non-Or term is a single literal)
    pub(crate) fn flatten_or(&self, term: TermId) -> Vec<TermId> {
        super::stack_safe(|| match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
                let mut result = Vec::new();
                for &arg in args {
                    result.extend(self.flatten_or(arg));
                }
                result
            }
            _ => vec![term],
        })
    }

    /// Check whether two terms form a negation pair (one is `Not` of the other).
    pub(crate) fn is_negation_pair(&self, a: TermId, b: TermId) -> bool {
        are_negation_pair(self.terms, a, b)
    }

    /// If the term is an And application `(and a₁ ... aₙ)`, return the conjunct TermIds.
    pub(crate) fn as_and(&self, id: TermId) -> Option<&'a [TermId]> {
        match self.terms.get(id) {
            TermData::App(Symbol::Named(name), args) if name == "and" && args.len() >= 2 => {
                Some(args)
            }
            _ => None,
        }
    }

    /// If the term is an equality application `(= lhs rhs)`, return the pair.
    pub(crate) fn as_equality(&self, id: TermId) -> Option<(TermId, TermId)> {
        match self.terms.get(id) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// If the term is a constant, return a view of it.
    pub(crate) fn as_constant(&self, id: TermId) -> Option<ConstantView<'a>> {
        match self.terms.get(id) {
            TermData::Const(c) => Some(constant_view(c)),
            _ => None,
        }
    }
}

/// View a term directly from a term store, without requiring a proof handle.
fn term_view<'a>(terms: &'a TermStore, id: TermId) -> TermView<'a> {
    match terms.get(id) {
        TermData::Const(c) => TermView::Const(constant_view(c)),
        TermData::Var(name, uid) => TermView::Var { name, id: *uid },
        TermData::App(Symbol::Named(name), args) => TermView::NamedApp { name, args },
        TermData::App(Symbol::Indexed(name, _), args) => TermView::IndexedApp { name, args },
        TermData::Not(inner) => TermView::Not(*inner),
        TermData::Ite(c, t, e) => TermView::Ite(*c, *t, *e),
        TermData::Let(_bindings, body) => TermView::Let { body: *body },
        TermData::Forall(vars, body, _triggers) => TermView::Forall { vars, body: *body },
        TermData::Exists(vars, body, _triggers) => TermView::Exists { vars, body: *body },
        _ => TermView::Unknown,
    }
}

/// Return the inner term if the given term is a negation.
fn not_inner(terms: &TermStore, id: TermId) -> Option<TermId> {
    match terms.get(id) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

/// Check whether two terms are complementary literals.
fn are_negation_pair(terms: &TermStore, a: TermId, b: TermId) -> bool {
    matches!(terms.get(a), TermData::Not(inner) if *inner == b)
        || matches!(terms.get(b), TermData::Not(inner) if *inner == a)
}
