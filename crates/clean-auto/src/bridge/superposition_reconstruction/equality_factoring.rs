// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality factoring proof reconstruction.
//!
//! From `C ∨ s₁=t₁ ∨ s₂=t₂` with `σ = mgu(s₁, s₂)`, derives
//! `(s₁=t₁ ∨ t₁≠t₂ ∨ C)σ` using `Or.rec` case analysis and
//! `Classical.em` for excluded middle.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::proof_helpers;
use super::{ReconstructionError, ReconstructionResult, SuperpositionReconstructor};

impl<'a> SuperpositionReconstructor<'a> {
    /// Reconstruct proof for equality factoring.
    ///
    /// Uses `Or.rec` for disjunction case analysis and `Classical.em` for
    /// excluded middle on `t₁ = t₂`:
    /// - Case `s=t₁`: inject directly into result via `Or.inl`
    /// - Case `s=t₂`: split on `Classical.em (Eq t₁ t₂)`:
    ///   - If `t₁=t₂`: derive `s=t₁` via `Eq.trans h₂ (Eq.symm heq)`
    ///   - If `t₁≠t₂`: inject the disequation into result
    /// - Case other literal `L`: inject `L` into its position in result
    pub(super) fn reconstruct_equality_factoring(
        &mut self,
        clause_id: u64,
        parent_id: u64,
    ) -> ReconstructionResult<Expr> {
        let result_clause = self
            .clause_map
            .get(&clause_id)
            .ok_or(ReconstructionError::MissingClause(clause_id))?;
        let result_lit_props: Vec<Expr> = result_clause
            .literals
            .iter()
            .map(|l| self.literal_to_prop(l))
            .collect::<Result<_, _>>()?;
        let result_prop = self.clause_to_prop(result_clause)?;

        let parent = self
            .clause_map
            .get(&parent_id)
            .ok_or(ReconstructionError::MissingClause(parent_id))?;

        let parent_lit_props: Vec<Expr> = parent
            .literals
            .iter()
            .map(|l| self.literal_to_prop(l))
            .collect::<Result<_, _>>()?;

        let pos_lits: Vec<(usize, &crate::superposition::Literal)> = parent
            .literals
            .iter()
            .enumerate()
            .filter(|(_, l)| l.positive)
            .collect();

        if pos_lits.len() < 2 {
            let parent_proof = self.reconstruct_clause(parent_id)?;
            return Ok(parent_proof);
        }

        // The two factored literals and their indices in the parent
        let (fi, lit1) = pos_lits[0];
        let (fj, _lit2) = pos_lits[1];

        let s_expr = self.symbol_map.term_to_expr(&lit1.lhs)?;
        let t1_expr = self.symbol_map.term_to_expr(&lit1.rhs)?;
        let t2_expr = self.symbol_map.term_to_expr(&pos_lits[1].1.rhs)?;
        let eq_type = self.symbol_map.term_type(&lit1.lhs)?;

        // Build Eq t₁ t₂ proposition (for Classical.em)
        let u = self.sort_level_of_type(&eq_type)?;
        let eq_t1_t2 = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![u]),
                    eq_type.clone(),
                ),
                t1_expr.clone(),
            ),
            t2_expr.clone(),
        );
        let not_eq_t1_t2 = Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            eq_t1_t2.clone(),
        );

        // Map parent literal index → result literal position.
        // Result order: [s=t₁ (pos 0), t₁≠t₂ (pos 1), remaining... (pos 2+)]
        let mut non_factored_offset = 2usize;
        let mut parent_idx_to_result_pos: Vec<Option<usize>> = Vec::new();
        for (k, _) in parent.literals.iter().enumerate() {
            if k == fi {
                parent_idx_to_result_pos.push(Some(0));
            } else if k == fj {
                parent_idx_to_result_pos.push(None); // factored out
            } else {
                parent_idx_to_result_pos.push(Some(non_factored_offset));
                non_factored_offset += 1;
            }
        }

        let parent_proof = self.reconstruct_clause(parent_id)?;

        // Build proof by recursive Or.rec case analysis on the parent clause.
        self.build_factoring_or_rec(
            &parent_lit_props,
            0,
            parent_proof,
            &result_prop,
            &result_lit_props,
            &parent_idx_to_result_pos,
            fj,
            &eq_type,
            &s_expr,
            &t1_expr,
            &t2_expr,
            &eq_t1_t2,
            &not_eq_t1_t2,
        )
    }

    /// Recursive helper: build Or.rec case analysis over parent literals.
    ///
    /// Each lambda in Or.rec binds a BVar(0) for its branch parameter.
    /// No depth tracking needed — the innermost lambda parameter is always BVar(0).
    #[allow(clippy::too_many_arguments)]
    fn build_factoring_or_rec(
        &self,
        parent_props: &[Expr],
        idx: usize,
        parent_proof: Expr,
        result_prop: &Expr,
        result_lit_props: &[Expr],
        idx_to_result_pos: &[Option<usize>],
        fj: usize,
        eq_type: &Expr,
        s: &Expr,
        t1: &Expr,
        t2: &Expr,
        eq_t1_t2: &Expr,
        not_eq_t1_t2: &Expr,
    ) -> ReconstructionResult<Expr> {
        let remaining = parent_props.len() - idx;

        if remaining == 1 {
            return self.factoring_single_case(
                idx,
                &parent_proof,
                result_prop,
                result_lit_props,
                idx_to_result_pos,
                fj,
                eq_type,
                s,
                t1,
                t2,
                eq_t1_t2,
                not_eq_t1_t2,
            );
        }

        // Multi-literal: parent_proof : Or P_idx (Or P_{idx+1} ...)
        let head_prop = &parent_props[idx];
        let tail_type = Self::or_chain_type(&parent_props[idx + 1..]);
        let motive = Self::mk_constant_or_motive(head_prop, &tail_type, result_prop);

        // Case inl: h_head : P_idx (head literal)
        // BVar(0) is always the innermost lambda's bound variable
        let case_inl_body = self.factoring_single_case(
            idx,
            &Expr::bvar(0),
            result_prop,
            result_lit_props,
            idx_to_result_pos,
            fj,
            eq_type,
            s,
            t1,
            t2,
            eq_t1_t2,
            not_eq_t1_t2,
        )?;
        let case_inl = Expr::lam(BinderInfo::Default, head_prop.clone(), case_inl_body);

        // Case inr: h_rest : Or P_{idx+1} ... (tail)
        // BVar(0) is always the innermost lambda's bound variable
        let case_inr_body = self.build_factoring_or_rec(
            parent_props,
            idx + 1,
            Expr::bvar(0),
            result_prop,
            result_lit_props,
            idx_to_result_pos,
            fj,
            eq_type,
            s,
            t1,
            t2,
            eq_t1_t2,
            not_eq_t1_t2,
        )?;
        let case_inr = Expr::lam(BinderInfo::Default, tail_type.clone(), case_inr_body);

        Ok(Self::mk_or_rec(
            head_prop,
            &tail_type,
            &motive,
            &case_inl,
            &case_inr,
            &parent_proof,
        ))
    }

    /// Handle a single parent literal case in equality factoring.
    ///
    /// Given a proof of parent literal P_idx, produce a proof of result_prop.
    #[allow(clippy::too_many_arguments)]
    fn factoring_single_case(
        &self,
        idx: usize,
        lit_proof: &Expr,
        result_prop: &Expr,
        result_lit_props: &[Expr],
        idx_to_result_pos: &[Option<usize>],
        fj: usize,
        eq_type: &Expr,
        s: &Expr,
        t1: &Expr,
        t2: &Expr,
        eq_t1_t2: &Expr,
        not_eq_t1_t2: &Expr,
    ) -> ReconstructionResult<Expr> {
        if idx == fj {
            // Second factored literal: lit_proof : Eq α s t₂
            // Use Classical.em (Eq t₁ t₂) to derive result.
            let em_motive = Self::mk_constant_or_motive(eq_t1_t2, not_eq_t1_t2, result_prop);

            // Inner case inl: fun (heq : Eq t₁ t₂) => ...
            // Inside this lambda: BVar(0) = heq, lit_proof lifted by 1 = h₂
            let heq = Expr::bvar(0);
            let h2_lifted = proof_helpers::lift_bvars(lit_proof, 1);
            let symm_heq = self.mk_eq_symm(eq_type, t1, t2, &heq)?;
            let s_eq_t1 = self.mk_eq_trans(eq_type, s, t2, t1, &h2_lifted, &symm_heq)?;
            let inner_inl_body = Self::inject_into_or_chain(result_lit_props, 0, s_eq_t1);
            let inner_case_inl = Expr::lam(BinderInfo::Default, eq_t1_t2.clone(), inner_inl_body);

            // Inner case inr: fun (hneq : Not (Eq t₁ t₂)) => ...
            let hneq = Expr::bvar(0);
            let inner_inr_body = Self::inject_into_or_chain(result_lit_props, 1, hneq);
            let inner_case_inr =
                Expr::lam(BinderInfo::Default, not_eq_t1_t2.clone(), inner_inr_body);

            let em = Self::mk_classical_em(eq_t1_t2);
            Ok(Self::mk_or_rec(
                eq_t1_t2,
                not_eq_t1_t2,
                &em_motive,
                &inner_case_inl,
                &inner_case_inr,
                &em,
            ))
        } else if let Some(result_pos) = idx_to_result_pos[idx] {
            // Non-factored literal or first factored literal: inject at result_pos
            Ok(Self::inject_into_or_chain(
                result_lit_props,
                result_pos,
                lit_proof.clone(),
            ))
        } else {
            Err(ReconstructionError::MalformedTrace(
                "equality factoring: unmapped parent literal".into(),
            ))
        }
    }
}
