// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal-structure proof wrappers for superposition reconstruction.
//!
//! Handles multi-clause goals that require structured proof wrappers
//! beyond a simple `Classical.byContradiction`:
//!
//! | Goal Shape | Wrapper                                              |
//! |------------|------------------------------------------------------|
//! | P ∨ Q      | Or.inl/Or.inr decomposition under byContradiction   |
//! | P → Q      | `fun p => byContradiction @Q (fun nq => ...)`       |
//! | P ↔ Q      | `Iff.intro (fun hp => byC @Q ...) (fun hq => byC @P ...)` |

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId};

use super::proof_helpers::{extract_or_disjuncts, mk_negation};
use super::{ReconstructionError, ReconstructionResult, SuperpositionReconstructor};

impl SuperpositionReconstructor<'_> {
    /// Build the lambda body for a multi-clause Or-goal.
    ///
    /// Given a `false_proof` that references FVar(fvar_base)..FVar(fvar_base+n-1)
    /// for the n goal clauses, and a disjunctive goal `P₁ ∨ ... ∨ Pₙ`,
    /// substitutes each FVar(fvar_base+i) with a derivation of `¬Pᵢ` from
    /// `h : ¬(P₁ ∨ ... ∨ Pₙ)`, then abstracts over h.
    ///
    /// Each derivation is: `fun xᵢ : Pᵢ => h (inject xᵢ at position i)`
    /// where `inject` builds the Or.inl/Or.inr chain.
    pub(super) fn build_multi_clause_body(
        &self,
        mut false_proof: Expr,
        goal: &Expr,
        num_goal_clauses: usize,
        fvar_base: u64,
    ) -> ReconstructionResult<Expr> {
        let disjuncts = extract_or_disjuncts(goal);
        if disjuncts.len() != num_goal_clauses {
            return Err(ReconstructionError::UnsupportedInference(format!(
                "multi-clause goal has {num_goal_clauses} clauses but goal expression \
                 has {} disjuncts (only Or-goals supported for multi-clause reconstruction)",
                disjuncts.len()
            )));
        }

        // Use a sentinel FVarId for h (¬goal hypothesis) that won't collide
        // with clause IDs or hypothesis IDs.
        let h_fvar_id = FVarId::new(u64::MAX);
        let h_fvar = Expr::fvar(h_fvar_id);

        // Substitute each clause hypothesis FVar(fvar_base+i) with its derivation from h.
        // derivation_i = fun xi : Pi => h (inject_into_or_chain(disjuncts, i, xi))
        for i in 0..num_goal_clauses {
            let pi = &disjuncts[i];
            let or_proof = Self::inject_into_or_chain(
                &disjuncts,
                i,
                Expr::bvar(0), // xi (the lambda parameter)
            );
            let derivation = Expr::lam(
                BinderInfo::Default,
                pi.clone(),
                Expr::app(h_fvar.clone(), or_proof),
            );
            let bridged = self.bridge_raw_prop_proof_to_clause_id(
                &mk_negation(pi),
                &derivation,
                i as u64,
                "multi-clause goal wrapper",
            )?;
            false_proof = false_proof.subst_fvar(FVarId::new(fvar_base + i as u64), &bridged);
        }

        // Abstract over h_fvar to produce the lambda body.
        // abstract_fvar replaces FVar(h_fvar_id) → BVar(0) at depth 0,
        // and correctly shifts existing BVars under binders.
        Ok(false_proof.abstract_fvar(h_fvar_id))
    }

    /// Build a proof for an Implies goal `P → Q`.
    ///
    /// Instead of the byContradiction wrapper used for simple goals, produces:
    ///
    /// ```text
    /// fun (p : P) =>
    ///   Classical.byContradiction @Q (fun (nq : ¬Q) =>
    ///     false_proof[clause_0 := p, clause_1 := nq])
    /// ```
    ///
    /// The clausifier negates `P → Q` to `P ∧ ¬Q`, producing 2 clauses:
    /// - Clause 0 (fvar_base): represents P (positive content)
    /// - Clause 1 (fvar_base+1): represents ¬Q (negative content)
    ///
    /// We bind `p : P` as a lambda parameter and `nq : ¬Q` via byContradiction,
    /// then substitute the clause FVars with these bindings.
    pub(super) fn build_implies_proof(
        &self,
        mut false_proof: Expr,
        _goal: &Expr,
        antecedent: &Expr,
        consequent: &Expr,
        fvar_base: u64,
    ) -> ReconstructionResult<(Expr, String)> {
        // Sentinel FVars for the two bindings
        let p_fvar_id = FVarId::new(u64::MAX - 1);
        let nq_fvar_id = FVarId::new(u64::MAX);

        let bridged_p = self.bridge_raw_prop_proof_to_clause_id(
            antecedent,
            &Expr::fvar(p_fvar_id),
            0,
            "implies goal wrapper antecedent",
        )?;
        false_proof = false_proof.subst_fvar(FVarId::new(fvar_base), &bridged_p);

        let neg_q = mk_negation(consequent);
        let bridged_nq = self.bridge_raw_prop_proof_to_clause_id(
            &neg_q,
            &Expr::fvar(nq_fvar_id),
            1,
            "implies goal wrapper consequent",
        )?;
        false_proof = false_proof.subst_fvar(FVarId::new(fvar_base + 1), &bridged_nq);

        // Abstract over nq (innermost lambda, BVar(0) inside byContradiction body)
        let body_nq = false_proof.abstract_fvar(nq_fvar_id);

        // fun (nq : ¬Q) => body_nq
        let nq_lambda = Expr::lam(BinderInfo::Default, neg_q, body_nq);

        // Classical.byContradiction @Q (fun nq : ¬Q => ...)
        let inner_proof = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                consequent.clone(),
            ),
            nq_lambda,
        );

        // Abstract over p (outermost lambda)
        let body_p = inner_proof.abstract_fvar(p_fvar_id);

        // fun (p : P) => Classical.byContradiction @Q (...)
        let result = Expr::lam(BinderInfo::Default, antecedent.clone(), body_p);

        let num_clauses = self.clause_map.len();
        let description = format!(
            "Superposition implies proof ({num_clauses} clauses, fun p => byContradiction)"
        );
        Ok((result, description))
    }

    /// Build a proof for an Iff goal `P ↔ Q`.
    ///
    /// Produces:
    ///
    /// ```text
    /// Iff.intro @P @Q
    ///   (fun (hp : P) => Classical.byContradiction @Q (fun (hnq : ¬Q) =>
    ///     false_proof[clause_fvars := forward derivations]))
    ///   (fun (hq : Q) => Classical.byContradiction @P (fun (hnp : ¬P) =>
    ///     false_proof[clause_fvars := backward derivations]))
    /// ```
    ///
    /// The clausifier negates `P ↔ Q` to `(P ∧ ¬Q) ∨ (¬P ∧ Q)`, which
    /// distributes to 4 CNF clauses:
    ///
    /// | Clause | Literals        | Forward (Or.inl)     | Backward (Or.inr)    |
    /// |--------|-----------------|----------------------|----------------------|
    /// | 0      | [P_lit, ¬P_lit] | Or.inl(hp)           | Or.inr(hnp)          |
    /// | 1      | [P_lit, Q_lit]  | Or.inl(hp)           | Or.inr(hq)           |
    /// | 2      | [¬Q_lit, ¬P_lit]| Or.inl(hnq)          | Or.inr(hnp)          |
    /// | 3      | [¬Q_lit, Q_lit] | Or.inl(hnq)          | Or.inr(hq)           |
    ///
    /// Clauses 0 and 3 are tautologies and typically eliminated by the prover.
    /// The false_proof uses the same refutation in both directions; the Or.inl/Or.inr
    /// substitution selects which branch of any Or.rec case analysis is taken.
    pub(super) fn build_iff_proof(
        &self,
        false_proof: Expr,
        _goal: &Expr,
        p: &Expr,
        q: &Expr,
        fvar_base: u64,
    ) -> ReconstructionResult<(Expr, String)> {
        // Sentinel FVars for the four bound variables
        let hp_fvar_id = FVarId::new(u64::MAX - 3);
        let hnq_fvar_id = FVarId::new(u64::MAX - 2);
        let hq_fvar_id = FVarId::new(u64::MAX - 1);
        let hnp_fvar_id = FVarId::new(u64::MAX);

        let mut fwd_proof = false_proof.clone();
        let mut bwd_proof = false_proof;

        // Substitute each goal clause FVar with the appropriate Or.inl/Or.inr derivation.
        // The CNF clause ordering from distribute_or is fixed:
        //   clause i has first literal from left conjunct (P ∧ ¬Q)
        //   and second literal from right conjunct (¬P ∧ Q).
        for i in 0..4u64 {
            let clause_id = i;
            let fvar_id = FVarId::new(fvar_base + i);

            // Skip if clause not in proof trace (prover eliminated the tautology)
            let Some(clause) = self.clause_map.get(&clause_id) else {
                continue;
            };

            // Only handle 2-literal clauses (expected for Iff CNF)
            if clause.literals.len() != 2 {
                continue;
            }

            let a_prop = self.literal_to_prop(&clause.literals[0])?;
            let b_prop = self.literal_to_prop(&clause.literals[1])?;

            // Forward direction: Or.inl with hypothesis from (P ∧ ¬Q)
            // Clauses 0,1 have first literal from P-side → use hp
            // Clauses 2,3 have first literal from ¬Q-side → use hnq
            let (fwd_raw_prop, fwd_raw_proof) = match i {
                0 | 1 => (p.clone(), Expr::fvar(hp_fvar_id)),
                2 | 3 => (mk_negation(q), Expr::fvar(hnq_fvar_id)),
                _ => unreachable!("clause index {i} outside 0..3"),
            };
            let fwd_branch =
                Self::bridge_raw_prop_proof_to_clause_prop(&fwd_raw_prop, &fwd_raw_proof, &a_prop)
                    .ok_or_else(|| {
                        ReconstructionError::UnsupportedInference(format!(
                            "iff goal wrapper: cannot bridge forward branch for clause {i}"
                        ))
                    })?;
            let fwd_sub = Self::mk_or_inl(&a_prop, &b_prop, &fwd_branch);
            fwd_proof = fwd_proof.subst_fvar(fvar_id, &fwd_sub);

            // Backward direction: Or.inr with hypothesis from (¬P ∧ Q)
            // Clauses 0,2 have second literal from ¬P-side → use hnp
            // Clauses 1,3 have second literal from Q-side → use hq
            let (bwd_raw_prop, bwd_raw_proof) = match i {
                0 | 2 => (mk_negation(p), Expr::fvar(hnp_fvar_id)),
                1 | 3 => (q.clone(), Expr::fvar(hq_fvar_id)),
                _ => unreachable!("clause index {i} outside 0..3"),
            };
            let bwd_branch =
                Self::bridge_raw_prop_proof_to_clause_prop(&bwd_raw_prop, &bwd_raw_proof, &b_prop)
                    .ok_or_else(|| {
                        ReconstructionError::UnsupportedInference(format!(
                            "iff goal wrapper: cannot bridge backward branch for clause {i}"
                        ))
                    })?;
            let bwd_sub = Self::mk_or_inr(&a_prop, &b_prop, &bwd_branch);
            bwd_proof = bwd_proof.subst_fvar(fvar_id, &bwd_sub);
        }

        let neg_q = mk_negation(q);
        let neg_p = mk_negation(p);

        // Forward: fun (hp : P) => byContradiction @Q (fun (hnq : ¬Q) => fwd_proof)
        let fwd_body_hnq = fwd_proof.abstract_fvar(hnq_fvar_id);
        let fwd_lam_hnq = Expr::lam(BinderInfo::Default, neg_q, fwd_body_hnq);
        let fwd_byc = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                q.clone(),
            ),
            fwd_lam_hnq,
        );
        let fwd_body_hp = fwd_byc.abstract_fvar(hp_fvar_id);
        let mp = Expr::lam(BinderInfo::Default, p.clone(), fwd_body_hp);

        // Backward: fun (hq : Q) => byContradiction @P (fun (hnp : ¬P) => bwd_proof)
        let bwd_body_hnp = bwd_proof.abstract_fvar(hnp_fvar_id);
        let bwd_lam_hnp = Expr::lam(BinderInfo::Default, neg_p, bwd_body_hnp);
        let bwd_byc = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                p.clone(),
            ),
            bwd_lam_hnp,
        );
        let bwd_body_hq = bwd_byc.abstract_fvar(hq_fvar_id);
        let mpr = Expr::lam(BinderInfo::Default, q.clone(), bwd_body_hq);

        // @Iff.intro P Q mp mpr : Iff P Q
        let result = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Iff.intro"), vec![]),
                        p.clone(),
                    ),
                    q.clone(),
                ),
                mp,
            ),
            mpr,
        );

        let num_clauses = self.clause_map.len();
        let description =
            format!("Superposition iff proof ({num_clauses} clauses, Iff.intro + byContradiction)");
        Ok((result, description))
    }
}
