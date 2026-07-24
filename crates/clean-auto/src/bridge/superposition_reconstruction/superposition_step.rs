// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Superposition (paramodulation) inference step reconstruction.
//!
//! Handles unit c1, multi-literal c1, and multi-literal c1+c2 cases.
//! Uses position-aware `Eq.subst` with `Or.rec` decomposition for
//! multi-literal equation clauses, and `weaken_or_chain` for multi-literal
//! rewrite targets.

use clean_kernel::{BinderInfo, Expr};

use super::types::ReconstructionResult;
use super::SuperpositionReconstructor;

impl<'a> SuperpositionReconstructor<'a> {
    /// Reconstruct proof for superposition (paramodulation).
    ///
    /// Rewrites a subterm in C2 using equation l=r from C1 via Eq.subst.
    ///
    /// **Unit c1** (single equation literal): Uses Eq.subst directly with a
    /// position-aware motive that diffs C2 against the result clause.
    ///
    /// **Multi-literal c1** (`l=r ∨ C₁`): Uses Or.rec to case-split on c1_proof.
    /// In the equation branch, applies Eq.subst with the extracted equation proof.
    /// In side literal branches, injects the literal into the result clause.
    pub(super) fn reconstruct_superposition(
        &mut self,
        clause_id: u64,
        c1_id: u64,
        c2_id: u64,
    ) -> ReconstructionResult<Expr> {
        // ---- Extract all immutable data before mutable reconstruct_clause calls ----
        let result = self
            .clause_map
            .get(&clause_id)
            .ok_or(super::ReconstructionError::MissingClause(clause_id))?;
        let result_lit_props: Vec<Expr> = result
            .literals
            .iter()
            .map(|l| self.literal_to_prop(l))
            .collect::<Result<_, _>>()?;
        let result_prop = self.clause_to_prop(result)?;
        let result_literals = result.literals.clone();

        let c1 = self
            .clause_map
            .get(&c1_id)
            .ok_or(super::ReconstructionError::MissingClause(c1_id))?;
        let eq_idx = c1.literals.iter().position(|l| l.positive).ok_or_else(|| {
            super::ReconstructionError::MalformedTrace(
                "superposition: c1 has no positive equation".into(),
            )
        })?;
        let eq_lit = c1.literals[eq_idx].clone();
        let c1_lit_props: Vec<Expr> = c1
            .literals
            .iter()
            .map(|l| self.literal_to_prop(l))
            .collect::<Result<_, _>>()?;
        let c1_len = c1.literals.len();
        let c1_literals = c1.literals.clone();

        let c2 = self
            .clause_map
            .get(&c2_id)
            .ok_or(super::ReconstructionError::MissingClause(c2_id))?;
        let c2_prop = self.clause_to_prop(c2)?;

        let lhs_expr = self.symbol_map.term_to_expr(&eq_lit.lhs)?;
        let rhs_expr = self.symbol_map.term_to_expr(&eq_lit.rhs)?;
        let eq_type = self.symbol_map.term_type(&eq_lit.lhs)?;

        if c1_len == 1 {
            // Unit c1: position-aware motive diffs c2_prop against result_prop.
            // The equation l=r may be used in either direction by the prover's
            // term ordering. Detect the actual direction by checking if the motive
            // body abstracts over BVar(0) (meaning the target was found).
            let motive_lr =
                self.build_motive_positional(&c2_prop, &result_prop, &lhs_expr, &eq_type);
            let lr_abstracts = match motive_lr.kind() {
                clean_kernel::ExprKind::Lam(_, _, body) => body.has_loose_bvars(),
                _ => false,
            };

            let c1_proof = self.reconstruct_clause(c1_id)?;
            let c2_proof = self.reconstruct_clause(c2_id)?;

            if lr_abstracts {
                // l → r direction: standard Eq.subst(α, motive, lhs, rhs, h, m)
                return self.mk_eq_subst(
                    &eq_type, &motive_lr, &lhs_expr, &rhs_expr, &c1_proof, &c2_proof,
                );
            } else {
                // r → l direction: swap a/b and symmetrize equation proof.
                // Eq.subst(α, motive, rhs, lhs, Eq.symm(h), m)
                let motive_rl =
                    self.build_motive_positional(&c2_prop, &result_prop, &rhs_expr, &eq_type);
                let c1_proof_sym = self.mk_eq_symm(&eq_type, &lhs_expr, &rhs_expr, &c1_proof)?;
                return self.mk_eq_subst(
                    &eq_type,
                    &motive_rl,
                    &rhs_expr,
                    &lhs_expr,
                    &c1_proof_sym,
                    &c2_proof,
                );
            }
        }

        // ---- Multi-literal c1: Or.rec decomposition ----

        // Build mapping: c1 side literal index → result position (structural matching).
        let mut c1_idx_to_result_pos: Vec<Option<usize>> = Vec::new();
        let mut used = vec![false; result_literals.len()];

        for (i, c1_lit) in c1_literals.iter().enumerate() {
            if i == eq_idx {
                c1_idx_to_result_pos.push(None);
            } else {
                let pos = result_literals.iter().enumerate().find_map(|(j, r_lit)| {
                    if !used[j]
                        && r_lit.lhs == c1_lit.lhs
                        && r_lit.rhs == c1_lit.rhs
                        && r_lit.positive == c1_lit.positive
                    {
                        Some(j)
                    } else {
                        None
                    }
                });
                match pos {
                    Some(j) => {
                        used[j] = true;
                        c1_idx_to_result_pos.push(Some(j));
                    }
                    None => {
                        return Err(super::ReconstructionError::MalformedTrace(
                            "superposition: c1 side literal not found in result".into(),
                        ));
                    }
                }
            }
        }

        // Remaining result positions are c2-derived (rewritten c2 literals).
        let c2_positions: Vec<usize> = (0..result_literals.len()).filter(|i| !used[*i]).collect();

        // Build c2_rewritten_prop for motive construction.
        let c2_rewritten_lit_props: Vec<Expr> = c2_positions
            .iter()
            .map(|&i| result_lit_props[i].clone())
            .collect();
        let c2_rewritten_prop = Self::or_chain_type(&c2_rewritten_lit_props);

        // Motive diffs c2_prop against c2_rewritten_prop (not full result_prop).
        // Detect rewrite direction (same as unit c1 case).
        let motive_lr =
            self.build_motive_positional(&c2_prop, &c2_rewritten_prop, &lhs_expr, &eq_type);
        let lr_abstracts = match motive_lr.kind() {
            clean_kernel::ExprKind::Lam(_, _, body) => body.has_loose_bvars(),
            _ => false,
        };
        let (motive, rewrite_a, rewrite_b, needs_symm) = if lr_abstracts {
            (motive_lr, lhs_expr.clone(), rhs_expr.clone(), false)
        } else {
            let motive_rl =
                self.build_motive_positional(&c2_prop, &c2_rewritten_prop, &rhs_expr, &eq_type);
            (motive_rl, rhs_expr.clone(), lhs_expr.clone(), true)
        };

        let c1_proof = self.reconstruct_clause(c1_id)?;
        let c1_proof = if needs_symm {
            self.mk_eq_symm(&eq_type, &lhs_expr, &rhs_expr, &c1_proof)?
        } else {
            c1_proof
        };
        let c2_proof = self.reconstruct_clause(c2_id)?;

        self.build_superposition_c1_or_rec(
            &c1_lit_props,
            0,
            c1_proof,
            &result_prop,
            &result_lit_props,
            &c1_idx_to_result_pos,
            eq_idx,
            &eq_type,
            &rewrite_a,
            &rewrite_b,
            &motive,
            &c2_proof,
            &c2_positions,
        )
    }

    /// Recursive Or.rec case analysis on c1's disjunction for superposition.
    ///
    /// Walks c1's right-associative Or chain. For the equation literal, applies
    /// Eq.subst to rewrite c2. For side literals, injects them into the result.
    #[allow(clippy::too_many_arguments)]
    fn build_superposition_c1_or_rec(
        &self,
        c1_props: &[Expr],
        idx: usize,
        c1_proof: Expr,
        result_prop: &Expr,
        result_lit_props: &[Expr],
        c1_idx_to_result: &[Option<usize>],
        eq_idx: usize,
        eq_type: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        motive: &Expr,
        c2_proof: &Expr,
        c2_positions: &[usize],
    ) -> ReconstructionResult<Expr> {
        let remaining = c1_props.len() - idx;

        if remaining == 1 {
            return self.superposition_single_c1_case(
                idx,
                &c1_proof,
                result_lit_props,
                c1_idx_to_result,
                eq_idx,
                eq_type,
                lhs,
                rhs,
                motive,
                c2_proof,
                c2_positions,
            );
        }

        let head = &c1_props[idx];
        let tail = Self::or_chain_type(&c1_props[idx + 1..]);
        let or_motive = Self::mk_constant_or_motive(head, &tail, result_prop);

        // Case inl: fun (h : head_prop) => handle single literal at idx
        let inl_body = self.superposition_single_c1_case(
            idx,
            &Expr::bvar(0),
            result_lit_props,
            c1_idx_to_result,
            eq_idx,
            eq_type,
            lhs,
            rhs,
            motive,
            c2_proof,
            c2_positions,
        )?;
        let case_inl = Expr::lam(BinderInfo::Default, head.clone(), inl_body);

        // Case inr: fun (h_rest : tail_type) => recurse on remaining
        let inr_body = self.build_superposition_c1_or_rec(
            c1_props,
            idx + 1,
            Expr::bvar(0),
            result_prop,
            result_lit_props,
            c1_idx_to_result,
            eq_idx,
            eq_type,
            lhs,
            rhs,
            motive,
            c2_proof,
            c2_positions,
        )?;
        let case_inr = Expr::lam(BinderInfo::Default, tail.clone(), inr_body);

        Ok(Self::mk_or_rec(
            head, &tail, &or_motive, &case_inl, &case_inr, &c1_proof,
        ))
    }

    /// Handle a single c1 literal case in superposition Or.rec decomposition.
    ///
    /// For the equation literal: Eq.subst rewrites c2, inject result into Or chain.
    /// For side literals: inject directly at the mapped result position.
    #[allow(clippy::too_many_arguments)]
    fn superposition_single_c1_case(
        &self,
        idx: usize,
        lit_proof: &Expr,
        result_lit_props: &[Expr],
        c1_idx_to_result: &[Option<usize>],
        eq_idx: usize,
        eq_type: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        motive: &Expr,
        c2_proof: &Expr,
        c2_positions: &[usize],
    ) -> ReconstructionResult<Expr> {
        if idx == eq_idx {
            // Equation literal: lit_proof : Eq α lhs rhs
            let subst_result = self.mk_eq_subst(eq_type, motive, lhs, rhs, lit_proof, c2_proof)?;

            if c2_positions.len() == 1 {
                // Single c2-derived result position: inject the literal proof.
                Ok(Self::inject_into_or_chain(
                    result_lit_props,
                    c2_positions[0],
                    subst_result,
                ))
            } else {
                // Multi-literal c2 + multi-literal c1: weaken the c2-derived
                // sub-disjunction into the full result Or chain via Or.rec
                // case analysis on the subst result.
                let result_prop = Self::or_chain_type(result_lit_props);
                let sub_props: Vec<Expr> = c2_positions
                    .iter()
                    .map(|&i| result_lit_props[i].clone())
                    .collect();
                Ok(Self::weaken_or_chain(
                    &sub_props,
                    subst_result,
                    result_lit_props,
                    &result_prop,
                    c2_positions,
                ))
            }
        } else if let Some(result_pos) = c1_idx_to_result[idx] {
            // Side literal: inject at mapped result position.
            Ok(Self::inject_into_or_chain(
                result_lit_props,
                result_pos,
                lit_proof.clone(),
            ))
        } else {
            Err(super::ReconstructionError::MalformedTrace(
                "superposition: unmapped c1 side literal".into(),
            ))
        }
    }
}
