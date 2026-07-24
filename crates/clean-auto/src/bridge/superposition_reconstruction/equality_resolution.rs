// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equality resolution proof reconstruction.
//!
//! From `(s ≠ t) ∨ C` with `mgu(s, t)`, derives `C` by:
//! - Single-literal parent (`s ≠ s`): `absurd (Eq.refl s) h`
//! - Multi-literal parent: `Or.rec` case analysis, using `absurd` on the
//!   resolved literal and `Or.inl`/`Or.inr` injection for remaining literals.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};

use super::proof_helpers::mk_eq_refl;
use super::{ReconstructionError, ReconstructionResult, SuperpositionReconstructor};

impl<'a> SuperpositionReconstructor<'a> {
    /// Reconstruct proof for equality resolution.
    ///
    /// Derives `C` from `(s ≠ t) ∨ C` when `mgu(s,t)` exists. For single-literal
    /// parents, uses `absurd` with `Eq.refl` directly. For multi-literal parents,
    /// uses `Or.rec` case analysis to decompose the disjunction.
    pub(super) fn reconstruct_equality_resolution(
        &mut self,
        clause_id: u64,
        parent_id: u64,
    ) -> ReconstructionResult<Expr> {
        // Extract all data from clause_map borrows upfront to avoid holding
        // immutable borrows across the mutable reconstruct_clause call.
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
        let result_is_empty = result_clause.literals.is_empty();

        let parent = self
            .clause_map
            .get(&parent_id)
            .ok_or(ReconstructionError::MissingClause(parent_id))?;

        // Find the resolved (negative) literal. After unification, the resolved
        // literal has lhs == rhs (s ≠ s), so prefer that. Falls back to the first
        // negative literal for single-literal parents where lhs == rhs is always true.
        let resolved_idx = parent
            .literals
            .iter()
            .position(|l| !l.positive && l.lhs == l.rhs)
            .or_else(|| parent.literals.iter().position(|l| !l.positive))
            .ok_or_else(|| {
                ReconstructionError::MalformedTrace(
                    "equality resolution parent has no negative literal".into(),
                )
            })?;
        let resolved_lit = parent.literals[resolved_idx].clone();
        let parent_len = parent.literals.len();
        let parent_lit_props: Vec<Expr> = parent
            .literals
            .iter()
            .map(|l| self.literal_to_prop(l))
            .collect::<Result<_, _>>()?;

        // After unification, lhs == rhs (both are sσ). Build Eq.refl sσ.
        let s_expr = self.symbol_map.term_to_expr(&resolved_lit.lhs)?;
        let s_type = self.symbol_map.term_type(&resolved_lit.lhs)?;
        let u = self.sort_level_of_type(&s_type)?;
        let refl_proof = mk_eq_refl(&u, &s_type, &s_expr);

        // Build `@Eq.{u} α s s` — the proposition that s = s
        let eq_prop = Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Eq"), vec![u]), s_type),
                s_expr.clone(),
            ),
            s_expr,
        );

        // Build parent index → result position mapping.
        let mut parent_to_result: Vec<Option<usize>> = Vec::new();
        let mut result_pos = 0;
        for i in 0..parent_len {
            if i == resolved_idx {
                parent_to_result.push(None);
            } else {
                parent_to_result.push(Some(result_pos));
                result_pos += 1;
            }
        }

        // Now safe to call &mut self — all clause_map borrows are dropped.
        let parent_proof = self.reconstruct_clause(parent_id)?;

        if parent_len == 1 {
            // Single-literal parent: parent_proof : Not (Eq s s)
            // absurd {Eq s s} {False} (Eq.refl s) (parent_proof) : False
            debug_assert!(
                result_is_empty,
                "single-literal equality resolution must produce empty clause"
            );
            let false_expr = Expr::const_(Name::from_string("False"), vec![]);
            Ok(Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
                            eq_prop,
                        ),
                        false_expr,
                    ),
                    refl_proof,
                ),
                parent_proof,
            ))
        } else {
            // Multi-literal parent: Or.rec case analysis
            self.build_resolution_or_rec(
                &parent_lit_props,
                0,
                parent_proof,
                &result_prop,
                &result_lit_props,
                &parent_to_result,
                resolved_idx,
                &eq_prop,
                &refl_proof,
            )
        }
    }

    /// Recursive Or.rec case analysis for equality resolution.
    ///
    /// Walks the parent's right-associative Or chain. For each literal:
    /// - Resolved literal: `absurd` produces `result_prop` from contradiction
    /// - Other literals: `inject_into_or_chain` places them in the result
    #[allow(clippy::too_many_arguments)]
    fn build_resolution_or_rec(
        &self,
        parent_props: &[Expr],
        idx: usize,
        parent_proof: Expr,
        result_prop: &Expr,
        result_lit_props: &[Expr],
        parent_to_result: &[Option<usize>],
        resolved_idx: usize,
        eq_prop: &Expr,
        refl_proof: &Expr,
    ) -> ReconstructionResult<Expr> {
        let remaining = parent_props.len() - idx;

        if remaining == 1 {
            return self.resolution_single_case(
                idx,
                &parent_proof,
                result_prop,
                result_lit_props,
                parent_to_result,
                resolved_idx,
                eq_prop,
                refl_proof,
            );
        }

        let head_prop = &parent_props[idx];
        let tail_type = Self::or_chain_type(&parent_props[idx + 1..]);
        let motive = Self::mk_constant_or_motive(head_prop, &tail_type, result_prop);

        // Case inl: fun (h : head_prop) => ...
        // BVar(0) is always the innermost lambda's bound variable
        let case_inl_body = self.resolution_single_case(
            idx,
            &Expr::bvar(0),
            result_prop,
            result_lit_props,
            parent_to_result,
            resolved_idx,
            eq_prop,
            refl_proof,
        )?;
        let case_inl = Expr::lam(BinderInfo::Default, head_prop.clone(), case_inl_body);

        // Case inr: fun (h_rest : tail_type) => ...
        let case_inr_body = self.build_resolution_or_rec(
            parent_props,
            idx + 1,
            Expr::bvar(0),
            result_prop,
            result_lit_props,
            parent_to_result,
            resolved_idx,
            eq_prop,
            refl_proof,
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

    /// Handle a single parent literal case in equality resolution.
    ///
    /// For the resolved literal: `absurd {Eq s s} {result_prop} (Eq.refl s) h`
    /// For other literals: inject into result_prop at the mapped position.
    #[allow(clippy::too_many_arguments)]
    fn resolution_single_case(
        &self,
        idx: usize,
        lit_proof: &Expr,
        result_prop: &Expr,
        result_lit_props: &[Expr],
        parent_to_result: &[Option<usize>],
        resolved_idx: usize,
        eq_prop: &Expr,
        refl_proof: &Expr,
    ) -> ReconstructionResult<Expr> {
        if idx == resolved_idx {
            // Resolved literal: lit_proof : Not (Eq s s) = (Eq s s → False)
            // absurd : {a : Prop} → {b : Sort u} → a → ¬a → b
            // absurd {Eq s s} {result_prop} (Eq.refl s) lit_proof : result_prop
            Ok(Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
                            eq_prop.clone(),
                        ),
                        result_prop.clone(),
                    ),
                    refl_proof.clone(),
                ),
                lit_proof.clone(),
            ))
        } else if let Some(result_pos) = parent_to_result[idx] {
            // Non-resolved literal: inject into result at correct position
            Ok(Self::inject_into_or_chain(
                result_lit_props,
                result_pos,
                lit_proof.clone(),
            ))
        } else {
            Err(ReconstructionError::MalformedTrace(
                "equality resolution: unmapped parent literal".into(),
            ))
        }
    }
}
