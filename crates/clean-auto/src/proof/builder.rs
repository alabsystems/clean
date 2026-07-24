// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof builder: constructs kernel expressions from proof steps.

use super::{ProofReconstructionError, ProofStep};
use crate::smt::TermId;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Level, TypeChecker};
use std::collections::HashMap;

/// Proof builder that constructs kernel expressions from proof steps
pub struct ProofBuilder<'a> {
    /// Mapping from SMT term IDs to kernel expressions
    pub(super) term_to_expr: &'a HashMap<TermId, Expr>,
    /// Mapping from SMT term IDs to their types
    pub(super) term_to_type: &'a HashMap<TermId, Expr>,
    /// Optional environment for computing universe levels via type inference.
    /// When None, falls back to u=v=1 (Level::succ(Level::zero())).
    pub(super) env: Option<&'a Environment>,
    /// Reverse map from hypothesis FVarId to (lhs_term, rhs_term) in canonical direction.
    /// Used to supply explicit implicit arguments to Eq.symm/Eq.trans.
    pub(super) hyp_terms: HashMap<FVarId, (TermId, TermId)>,
}

impl<'a> ProofBuilder<'a> {
    /// Create a new proof builder
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "internal proof reconstruction still keeps a constructor without environment-backed sort inference"
        )
    )]
    pub fn new(
        term_to_expr: &'a HashMap<TermId, Expr>,
        term_to_type: &'a HashMap<TermId, Expr>,
    ) -> Self {
        ProofBuilder {
            term_to_expr,
            term_to_type,
            env: None,
            hyp_terms: HashMap::new(),
        }
    }

    /// Create a new proof builder with environment for accurate universe levels
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "internal proof reconstruction still keeps the env-only constructor alongside with_hypotheses"
        )
    )]
    pub fn with_env(
        term_to_expr: &'a HashMap<TermId, Expr>,
        term_to_type: &'a HashMap<TermId, Expr>,
        env: &'a Environment,
    ) -> Self {
        ProofBuilder {
            term_to_expr,
            term_to_type,
            env: Some(env),
            hyp_terms: HashMap::new(),
        }
    }

    /// Create a proof builder with hypothesis term info for explicit proof construction.
    ///
    /// `eq_hypotheses` maps `(lhs_term, rhs_term) → FVarId` for each equality hypothesis.
    /// This is inverted to build a reverse map from FVarId → (lhs, rhs) so the builder
    /// can supply explicit implicit arguments to Eq.symm/Eq.trans.
    pub fn with_hypotheses(
        term_to_expr: &'a HashMap<TermId, Expr>,
        term_to_type: &'a HashMap<TermId, Expr>,
        env: &'a Environment,
        eq_hypotheses: &HashMap<(TermId, TermId), FVarId>,
    ) -> Self {
        let hyp_terms: HashMap<FVarId, (TermId, TermId)> = eq_hypotheses
            .iter()
            .map(|(&(t1, t2), &fvar)| (fvar, (t1, t2)))
            .collect();
        ProofBuilder {
            term_to_expr,
            term_to_type,
            env: Some(env),
            hyp_terms,
        }
    }

    /// Compute the sort level of a type expression using the environment.
    ///
    /// # Errors
    ///
    /// Returns `SortInferenceFailed` if no environment is available or if
    /// `TypeChecker::infer_sort` fails.
    pub(super) fn sort_level_of_type(&self, ty: &Expr) -> Result<Level, ProofReconstructionError> {
        let env = self.env.ok_or_else(|| {
            ProofReconstructionError::SortInferenceFailed("no environment available".into())
        })?;
        let tc = TypeChecker::new(env);
        tc.infer_sort(ty)
            .map_err(|e| ProofReconstructionError::SortInferenceFailed(format!("{e:?}")))
    }

    /// Compute universe levels (u, v) for congrArg/congr from a function expression.
    ///
    /// Infers the function's type (which should be a Pi type `(x : α) → β`),
    /// then u = sort of α (domain) and v = sort of β (codomain).
    pub(super) fn congr_universe_levels(
        &self,
        func_expr: &Expr,
    ) -> Result<(Level, Level), ProofReconstructionError> {
        let env = self.env.ok_or(ProofReconstructionError::NoEnvironment)?;
        let tc = TypeChecker::new(env);
        let func_ty = tc.infer_type(func_expr).map_err(|e| {
            ProofReconstructionError::CongruenceInferenceFailed {
                func: format!("{func_expr:?}"),
                reason: format!("infer_type failed: {e:?}"),
            }
        })?;
        match func_ty.kind() {
            ExprKind::Pi(_, domain, body) => {
                let u = tc.infer_sort(domain).map_err(|e| {
                    ProofReconstructionError::SortInferenceFailed(format!("domain sort: {e:?}"))
                })?;
                let v = tc.infer_sort(body).map_err(|e| {
                    ProofReconstructionError::SortInferenceFailed(format!("codomain sort: {e:?}"))
                })?;
                Ok((u, v))
            }
            _ => Err(ProofReconstructionError::CongruenceInferenceFailed {
                func: format!("{func_expr:?}"),
                reason: "type is not a Pi".into(),
            }),
        }
    }

    /// Compute the (lhs_term, rhs_term) equality span of a proof step.
    ///
    /// Returns `Some((lhs, rhs))` where the step proves `expr(lhs) = expr(rhs)`.
    /// Returns `None` when the span cannot be determined (e.g., Congr, Axiom).
    pub(super) fn step_span(&self, step: &ProofStep) -> Option<(TermId, TermId)> {
        match step {
            ProofStep::Refl(t) => Some((*t, *t)),
            ProofStep::Hypothesis(fvar) => self.hyp_terms.get(fvar).copied(),
            ProofStep::Symm(inner) => {
                let (a, b) = self.step_span(inner)?;
                Some((b, a))
            }
            ProofStep::Trans(p1, p2) => {
                let (a, _b) = self.step_span(p1)?;
                let (_b2, c) = self.step_span(p2)?;
                Some((a, c))
            }
            ProofStep::Congr(..) | ProofStep::Axiom(..) | ProofStep::Propositional(..) => None,
        }
    }

    /// Build a kernel proof term from a proof step
    pub fn build(&self, step: &ProofStep) -> Result<Expr, ProofReconstructionError> {
        match step {
            ProofStep::Refl(term_id) => {
                let expr = self
                    .term_to_expr
                    .get(term_id)
                    .ok_or(ProofReconstructionError::MissingTermMapping(*term_id))?;
                let ty = self
                    .term_to_type
                    .get(term_id)
                    .cloned()
                    .ok_or(ProofReconstructionError::MissingTermMapping(*term_id))?;
                self.mk_eq_refl(&ty, expr)
            }
            ProofStep::Symm(inner) => self.build_symm(inner),
            ProofStep::Trans(p1, p2) => self.build_trans(p1, p2),
            ProofStep::Congr(func_expr, arg_proofs) => self.build_congr(func_expr, arg_proofs),
            ProofStep::Hypothesis(fvar) => {
                // Return the free variable representing the hypothesis
                Ok(Expr::fvar(*fvar))
            }
            ProofStep::Axiom(name, levels) => {
                // Return an axiom reference - this MUST be a constant that is
                // actually declared in the environment. Using this for arbitrary
                // unverified assertions undermines soundness.
                //
                // The kernel type checker will verify that this constant exists
                // and has the correct type, so unsound axioms will be rejected.
                Ok(Expr::const_(Name::from_string(name), levels.clone()))
            }
            ProofStep::Propositional(strategy) => {
                // Propositional proof steps carry their proof terms externally
                // (built by build_propositional_proof). The ProofBuilder is not
                // expected to reconstruct them — this arm is unreachable in
                // normal usage since propositional proofs bypass ProofBuilder.
                Err(ProofReconstructionError::StepSpanUnknown {
                    context: format!("propositional step ({strategy}) has no builder path"),
                })
            }
        }
    }

    /// Build proof for `Congr(func_expr, arg_proofs)`.
    pub(super) fn build_congr(
        &self,
        func_expr: &Expr,
        arg_proofs: &[ProofStep],
    ) -> Result<Expr, ProofReconstructionError> {
        let arg_proof_terms: Result<Vec<Expr>, _> =
            arg_proofs.iter().map(|p| self.build(p)).collect();
        let arg_proof_terms = arg_proof_terms?;

        if arg_proof_terms.is_empty() {
            // Nullary function: f = f is just reflexivity.
            // Look up the function's type from the environment for Eq.refl.
            let func_name_n = match func_expr.kind() {
                ExprKind::Const(name, _) => name.clone(),
                _ => {
                    return Err(ProofReconstructionError::CongruenceInferenceFailed {
                        func: format!("{func_expr:?}"),
                        reason: "nullary congr requires a named constant".into(),
                    })
                }
            };
            let func_ty = self
                .env
                .ok_or(ProofReconstructionError::NoEnvironment)?
                .get_const(&func_name_n)
                .map(|c| c.type_.clone())
                .ok_or_else(|| ProofReconstructionError::CongruenceInferenceFailed {
                    func: func_name_n.to_string(),
                    reason: "constant not declared in environment".into(),
                })?;
            self.mk_eq_refl(&func_ty, func_expr)
        } else if arg_proof_terms.len() == 1 {
            // Single argument: use congrArg
            self.mk_congr_arg(func_expr, &arg_proof_terms[0], &arg_proofs[0])
        } else {
            // Multiple arguments: use congrArg + congr composition
            self.mk_congr_multi(func_expr, &arg_proof_terms, arg_proofs)
        }
    }

    /// Try to build `@Eq.symm.{u} α a b h` with explicit implicit arguments.
    ///
    /// Succeeds when the inner step is a hypothesis whose canonical direction
    /// (lhs, rhs) is tracked in `hyp_terms`.
    fn try_explicit_symm(&self, inner: &ProofStep) -> Option<Expr> {
        let fvar = match inner {
            ProofStep::Hypothesis(fv) => fv,
            _ => return None,
        };
        let &(t1, t2) = self.hyp_terms.get(fvar)?;
        let a_expr = self.term_to_expr.get(&t1)?;
        let b_expr = self.term_to_expr.get(&t2)?;
        let eq_ty = self.term_to_type.get(&t1).cloned()?;
        let u = self.sort_level_of_type(&eq_ty).ok()?;
        Some(crate::bridge::eq_proof_builders::mk_eq_symm(
            &u,
            &eq_ty,
            a_expr,
            b_expr,
            &Expr::fvar(*fvar),
        ))
    }

    /// Build proof for `Symm(inner)` — explicit `@Eq.symm.{u} α a b h`.
    fn build_symm(&self, inner: &ProofStep) -> Result<Expr, ProofReconstructionError> {
        // Fast path: hypothesis with known canonical direction
        if let Some(proof) = self.try_explicit_symm(inner) {
            return Ok(proof);
        }
        // General path: use step_span to determine a, b
        let (t_a, t_b) =
            self.step_span(inner)
                .ok_or_else(|| ProofReconstructionError::StepSpanUnknown {
                    context: "Eq.symm".into(),
                })?;
        let inner_proof = self.build(inner)?;
        let a_expr = self
            .term_to_expr
            .get(&t_a)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a))?;
        let b_expr = self
            .term_to_expr
            .get(&t_b)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_b))?;
        let eq_ty = self
            .term_to_type
            .get(&t_a)
            .cloned()
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a))?;
        let u = self.sort_level_of_type(&eq_ty)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_symm(
            &u,
            &eq_ty,
            a_expr,
            b_expr,
            &inner_proof,
        ))
    }

    /// Build proof for `Trans(p1, p2)` — explicit `@Eq.trans.{u} α a b c h₁ h₂`.
    fn build_trans(
        &self,
        p1: &ProofStep,
        p2: &ProofStep,
    ) -> Result<Expr, ProofReconstructionError> {
        let proof1 = self.build(p1)?;
        let proof2 = self.build(p2)?;
        let (t_a, t_b) =
            self.step_span(p1)
                .ok_or_else(|| ProofReconstructionError::StepSpanUnknown {
                    context: "Eq.trans lhs".into(),
                })?;
        let (_, t_c) =
            self.step_span(p2)
                .ok_or_else(|| ProofReconstructionError::StepSpanUnknown {
                    context: "Eq.trans rhs".into(),
                })?;
        let a_expr = self
            .term_to_expr
            .get(&t_a)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a))?;
        let b_expr = self
            .term_to_expr
            .get(&t_b)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_b))?;
        let c_expr = self
            .term_to_expr
            .get(&t_c)
            .ok_or(ProofReconstructionError::MissingTermMapping(t_c))?;
        let eq_ty = self
            .term_to_type
            .get(&t_a)
            .cloned()
            .ok_or(ProofReconstructionError::MissingTermMapping(t_a))?;
        let u = self.sort_level_of_type(&eq_ty)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_trans(
            &u, &eq_ty, a_expr, b_expr, c_expr, &proof1, &proof2,
        ))
    }

    /// Build Eq.refl : ∀ {α : Sort u} (a : α), a = a
    pub(super) fn mk_eq_refl(
        &self,
        ty: &Expr,
        val: &Expr,
    ) -> Result<Expr, ProofReconstructionError> {
        let u = self.sort_level_of_type(ty)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_refl(&u, ty, val))
    }

    // NOTE: mk_eq_symm and mk_eq_trans with incomplete args were removed.
    // The kernel requires fully explicit arguments: @Eq.symm.{u} α a b h (4 args)
    // and @Eq.trans.{u} α a b c h₁ h₂ (6 args). The old implementations only
    // supplied 1 and 2 args respectively, which the kernel type checker would reject.
    // All Symm/Trans proof terms are now built via step_span in build().
}
