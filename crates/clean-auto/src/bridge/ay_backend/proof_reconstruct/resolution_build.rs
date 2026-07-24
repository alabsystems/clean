// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolution proof builder: recursive `Or.rec` synthesis from a
//! [`ResolutionPlan`](super::resolution_plan::ResolutionPlan).
//!
//! Extracted from `resolution.rs` (#2508). Replaces the mirrored
//! `or_rec_walk_c1` / `or_rec_walk_c2` pair with a single side-generic
//! walker.

use clean_kernel::{BinderInfo, Expr};

use super::resolution_plan::{ClausePlan, ResolutionPlan};
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

/// Which side of the binary resolution we are walking.
#[derive(Debug, Clone, Copy)]
pub(super) enum ResolutionSide {
    /// Clause 1 (contains the positive pivot).
    Left,
    /// Clause 2 (contains the negated pivot).
    Right,
}

/// Proof term builder for a single resolution step.
///
/// Borrows the reconstruction context (read-only) and a pre-built plan.
/// All mutable state was consumed during plan construction.
pub(super) struct ResolutionBuilder<'ctx, 'plan, 'a> {
    ctx: &'ctx ReconstructionContext<'a>,
    plan: &'plan ResolutionPlan,
}

impl<'ctx, 'plan, 'a> ResolutionBuilder<'ctx, 'plan, 'a> {
    pub(super) fn new(ctx: &'ctx ReconstructionContext<'a>, plan: &'plan ResolutionPlan) -> Self {
        Self { ctx, plan }
    }

    /// Build the full resolution proof term from the two premise proofs.
    pub(super) fn build(&self, h1: &Expr, h2: &Expr) -> ReconstructResult<Expr> {
        if self.plan.left.props.len() == 1 {
            // Unit clause1: the sole literal IS the pivot proof.
            self.resolve_against_right(h1, h2)
        } else {
            self.walk_side(ResolutionSide::Left, 0, h1, h2)
        }
    }

    /// Walk a clause via nested `Or.rec`, producing proof term branches.
    ///
    /// Generic over Left/Right. The key behavioral difference between sides:
    /// - Left: `other_proof` is the full clause2 proof (no lifting needed).
    /// - Right: `other_proof` is the pivot proof from clause1 (must be
    ///   lifted by 1 at each binder crossing to maintain de Bruijn indices).
    fn walk_side(
        &self,
        side: ResolutionSide,
        idx: usize,
        side_proof: &Expr,
        other_proof: &Expr,
    ) -> ReconstructResult<Expr> {
        let clause = self.clause_plan(side);
        let remaining = clause.props.len() - idx;

        if remaining == 1 {
            return self.single_literal_case(side, idx, side_proof, other_proof);
        }

        let head = &clause.props[idx];
        let tail = &clause.suffixes[idx + 1];
        let motive = disjunction::mk_constant_or_motive(head, tail, &self.plan.target);

        // Right side: pivot_proof is captured from the enclosing c1 branch,
        // so crossing the new binder must shift its loose de Bruijn indices.
        let lifted_other = match side {
            ResolutionSide::Left => other_proof.clone(),
            ResolutionSide::Right => other_proof.lift(1),
        };

        let case_inl_body = self.single_literal_case(side, idx, &Expr::bvar(0), &lifted_other)?;
        let case_inl = Expr::lam(BinderInfo::Default, head.clone(), case_inl_body);

        let case_inr_body = self.walk_side(side, idx + 1, &Expr::bvar(0), &lifted_other)?;
        let case_inr = Expr::lam(BinderInfo::Default, tail.clone(), case_inr_body);

        Ok(disjunction::mk_or_rec(
            head, tail, &motive, &case_inl, &case_inr, side_proof,
        ))
    }

    /// Handle a single literal from either clause.
    ///
    /// At the pivot index: Left triggers resolution against clause2,
    /// Right triggers absurd discharge. At non-pivot indices: inject
    /// the literal proof into the resolvent.
    fn single_literal_case(
        &self,
        side: ResolutionSide,
        idx: usize,
        lit_proof: &Expr,
        other_proof: &Expr,
    ) -> ReconstructResult<Expr> {
        let clause = self.clause_plan(side);

        if idx == clause.pivot_idx {
            match side {
                ResolutionSide::Left => {
                    // At c1's pivot: resolve against clause2.
                    self.resolve_against_right(lit_proof, other_proof)
                }
                ResolutionSide::Right => {
                    // At c2's pivot: discharge via absurd.
                    self.mk_resolution_absurd(other_proof, lit_proof)
                }
            }
        } else {
            let resolvent_pos =
                clause.to_resolvent[idx].ok_or(ReconstructionError::MissingResolventPosition {
                    literal_index: idx,
                    step_id: self.plan.step_id.0,
                })?;
            if self.plan.resolvent_props.is_empty() {
                Ok(lit_proof.clone())
            } else {
                Ok(disjunction::inject_into_or_chain_with_suffixes(
                    &self.plan.resolvent_props,
                    &self.plan.resolvent_suffixes,
                    resolvent_pos,
                    lit_proof.clone(),
                ))
            }
        }
    }

    /// Resolve against clause2: either directly (unit) or via `Or.rec` walk.
    fn resolve_against_right(&self, pivot_proof: &Expr, h2: &Expr) -> ReconstructResult<Expr> {
        if self.plan.right.props.len() == 1 {
            self.mk_resolution_absurd(pivot_proof, h2)
        } else {
            self.walk_side(ResolutionSide::Right, 0, h2, pivot_proof)
        }
    }

    /// Build `absurd` for the resolution pivot, handling polarity.
    ///
    /// The `positive_prop` argument to `absurd` must be a proposition (type),
    /// not a proof term (value). Returns an error if the proposition is not
    /// in the term cache — preferable to silently producing an ill-typed
    /// proof term (see #2414).
    fn mk_resolution_absurd(
        &self,
        c1_pivot_proof: &Expr,
        c2_pivot_proof: &Expr,
    ) -> ReconstructResult<Expr> {
        let pivot = self.plan.pivot;
        let target = &self.plan.target;
        let step_id = self.plan.step_id;

        if self.plan.pivot_is_negation {
            let positive_prop = match self.ctx.trace().as_not(pivot) {
                Some(inner) => self.ctx.term_cache.get(&inner).cloned().ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description:
                            "positive proposition not in term cache for absurd (negated pivot)"
                                .to_string(),
                    }
                })?,
                None => self.ctx.term_cache.get(&pivot).cloned().ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description:
                            "pivot proposition not in term cache for absurd (non-Not pivot)"
                                .to_string(),
                    }
                })?,
            };
            Ok(disjunction::mk_absurd(
                &positive_prop,
                target,
                c2_pivot_proof,
                c1_pivot_proof,
            ))
        } else {
            let positive_prop = self.ctx.term_cache.get(&pivot).cloned().ok_or_else(|| {
                ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "pivot proposition not in term cache for absurd".to_string(),
                }
            })?;
            Ok(disjunction::mk_absurd(
                &positive_prop,
                target,
                c1_pivot_proof,
                c2_pivot_proof,
            ))
        }
    }

    /// Get the clause plan for the given side.
    fn clause_plan(&self, side: ResolutionSide) -> &ClausePlan {
        match side {
            ResolutionSide::Left => &self.plan.left,
            ResolutionSide::Right => &self.plan.right,
        }
    }
}
