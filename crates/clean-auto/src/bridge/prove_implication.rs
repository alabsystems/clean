// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closed equality-implication reconstruction for the SMT bridge.
//!
//! Root cause this addresses: a goal in *closed-implication* form
//! `H1 → … → Hn → (a = b)` is classified as `Implies`, so it is routed to the
//! propositional/lambda reconstruction path (`build_implies_proof`) rather than
//! the full equality machinery (`build_equality_proof`). The lambda path only
//! ever feeds *one* local assumption at a time into the equality chain search and
//! has no congruence step, so it cannot reconstruct
//!
//!   * multi-hop transitivity chains
//!     (`e0=e1 → e1=e2 → … → e_{k-1}=ek → e0=ek`), nor
//!   * congruence (`a=b → f(a)=f(b)`),
//!
//! even though the DPLL(T)/EUF core reaches UNSAT for the negated goal. The open
//! form `H1, …, Hn ⊢ a = b` (antecedents registered as `eq_hypothesis_canonical`
//! / equality-theory hypotheses) handles both, because `build_equality_proof`
//! has an E-graph proof trace, BFS transitivity, *and* congruence.
//!
//! This module bridges the gap: it introduces the antecedents as tracked
//! hypotheses on a fresh sub-bridge, proves the consequent with the open-form
//! machinery, and re-binds the antecedents as lambdas. The resulting closed
//! proof term is kernel-checked (`infer_type` + `is_def_eq`) against the original
//! implication goal before it is trusted — the bridge is on the search side, not
//! the TCB, so a malformed term is rejected here and downstream rather than
//! claimed as a proof.

use clean_kernel::{BinderInfo, Expr, FVarId, TypeChecker};

use super::expr_classifier::LogicalForm;
use super::result::{ProofMethod, SmtProofResult, SmtVerificationResult};
use super::SmtBridge;
use crate::proof::ProofStep;

impl<'env> SmtBridge<'env> {
    /// Peel the leading antecedents off a closed equality-implication goal.
    ///
    /// Returns `Some((antecedents, consequent))` only when `goal` is
    /// `H1 → … → Hn → C` (`n ≥ 1`) where every arrow is a genuine non-dependent
    /// implication and the final consequent `C` is an equality. Returns `None`
    /// otherwise so the caller falls through to the normal pipeline.
    pub(super) fn peel_equality_implication_goal(&self, goal: &Expr) -> Option<(Vec<Expr>, Expr)> {
        let mut antecedents: Vec<Expr> = Vec::new();
        let mut current = goal.clone();

        loop {
            match self.classify_prop(&current) {
                LogicalForm::Implies(antecedent, consequent) => {
                    // Only peel a genuine non-dependent arrow: the consequent must
                    // not reference the binder we are about to discard. (A dependent
                    // Pi would leave a loose bound variable in `consequent`.)
                    if consequent.has_loose_bvar(0) {
                        return None;
                    }
                    antecedents.push(antecedent);
                    current = consequent;
                }
                LogicalForm::Eq { .. } => {
                    if antecedents.is_empty() {
                        return None;
                    }
                    return Some((antecedents, current));
                }
                _ => return None,
            }
        }
    }

    /// Try to reconstruct a closed equality-implication proof.
    ///
    /// Introduces `antecedents` as tracked hypotheses on a fresh sub-bridge,
    /// proves `consequent` via the full equality machinery, re-binds the
    /// antecedents as lambdas, and kernel-checks the closed term against `goal`.
    /// Returns `Some(Verified)` only on a kernel-valid proof; `None` on any
    /// failure (so the caller falls through to the normal pipeline).
    pub(super) fn try_prove_equality_under_antecedents(
        &self,
        goal: &Expr,
        antecedents: &[Expr],
        consequent: &Expr,
    ) -> Option<SmtVerificationResult> {
        // Fresh sub-bridge so we never contaminate `self`'s solver/clause state:
        // on failure the caller re-runs the unchanged pipeline on the original
        // bridge. The antecedents become fvar-tracked hypotheses, exactly like a
        // local context, so the consequent reconstruction reuses the open-form
        // E-graph trace / transitivity / congruence paths.
        let mut sub = SmtBridge::new(self.env);
        sub.set_max_instantiation_rounds(self.max_instantiation_rounds);

        let mut fvars: Vec<FVarId> = Vec::with_capacity(antecedents.len());
        for (idx, antecedent) in antecedents.iter().enumerate() {
            // `goal` is closed and there is no local context (gated by the
            // caller), so sequential ids starting at 1 are guaranteed fresh.
            let fvar = FVarId::new(idx as u64 + 1);
            sub.add_hypothesis_with_fvar(antecedent, Some(fvar)).ok()?;
            fvars.push(fvar);
        }

        let proof = sub.prove_core(consequent).ok()?.verified()?;
        let closed = bind_antecedent_lambdas(proof.proof_term().clone(), antecedents, &fvars);

        // Soundness gate: the re-bound term must kernel-check against the original
        // implication goal. The sub-bridge is not in the TCB, so we verify here
        // rather than trust its reconstruction.
        let tc = TypeChecker::new(self.env);
        let inferred = tc.infer_type(&closed).ok()?;
        if !tc.is_def_eq(&inferred, goal) {
            return None;
        }

        Some(SmtVerificationResult::Verified(Box::new(
            SmtProofResult::new(
                ProofMethod::SmtUnsat,
                "SMT proved closed equality-implication via antecedent introduction",
                closed,
                ProofStep::Propositional("Implies.intro_eq".into()),
            ),
        )))
    }
}

/// Re-bind introduced antecedents as nested lambdas around a consequent proof.
///
/// Given `body : C` referencing the synthetic hypothesis fvars `fvars[i]` (for
/// antecedent `antecedents[i]`), produces the closed term
/// `fun (h1 : H1) … (hn : Hn) => body'`, where each `fvars[i]` is abstracted into
/// the matching lambda parameter. Built innermost-first so `abstract_fvar`'s
/// bound-variable shifting lines the de Bruijn indices up with the binders.
fn bind_antecedent_lambdas(mut body: Expr, antecedents: &[Expr], fvars: &[FVarId]) -> Expr {
    for (antecedent, fvar) in antecedents.iter().zip(fvars.iter()).rev() {
        let abstracted = body.abstract_fvar(*fvar);
        body = Expr::lam(BinderInfo::Default, antecedent.clone(), abstracted);
    }
    body
}
