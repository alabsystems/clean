// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolution step planning: clause validation, pivot orientation, and
//! resolvent position mapping.
//!
//! Extracted from `resolution.rs` (#2508) to separate planning from
//! recursive proof synthesis.

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;
use clean_kernel::name::Name;

/// Pre-computed metadata for one side of a binary resolution step.
pub(super) struct ClausePlan {
    pub(super) props: Vec<Expr>,
    pub(super) suffixes: Vec<Expr>,
    pub(super) pivot_idx: usize,
    pub(super) to_resolvent: Vec<Option<usize>>,
}

/// All metadata needed to build a resolution proof term.
///
/// Constructed once from the raw ay step data, then consumed by
/// [`ResolutionBuilder`](super::resolution_build::ResolutionBuilder).
pub(super) struct ResolutionPlan {
    pub(super) left: ClausePlan,
    pub(super) right: ClausePlan,
    pub(super) resolvent_props: Vec<Expr>,
    pub(super) resolvent_suffixes: Vec<Expr>,
    pub(super) target: Expr,
    pub(super) pivot: TermId,
    pub(super) pivot_is_negation: bool,
    pub(super) step_id: ProofId,
}

impl ResolutionPlan {
    /// Build a resolution plan from the raw step inputs.
    ///
    /// Performs bounds checking, clause translation, pivot orientation,
    /// position mapping, and suffix precomputation.
    pub(super) fn build(
        ctx: &mut ReconstructionContext<'_>,
        resolvent_clause: &[TermId],
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
        step_id: ProofId,
    ) -> ReconstructResult<Self> {
        let trace = ctx
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        // Bounds-check premise indices
        if clause1.0 as usize >= trace.step_count() {
            return Err(ReconstructionError::InvalidPremise {
                premise: clause1.0,
                from_step: step_id.0,
            });
        }
        if clause2.0 as usize >= trace.step_count() {
            return Err(ReconstructionError::InvalidPremise {
                premise: clause2.0,
                from_step: step_id.0,
            });
        }
        let c1_lits = trace.clause_of_step_by_id(clause1);
        let c2_lits = trace.clause_of_step_by_id(clause2);

        // Translate all literals to kernel propositions
        let c1_props = ctx.translate_clause_props(&c1_lits)?;
        let c2_props = ctx.translate_clause_props(&c2_lits)?;
        let resolvent_props = ctx.translate_clause_props(resolvent_clause)?;

        // Find pivot indices — try both orientations per ay checker convention
        let (pivot_idx_c1, pivot_idx_c2, pivot_swapped) =
            find_pivot_indices(ctx, &c1_lits, &c2_lits, pivot, step_id)?;

        // Build position mappings: non-pivot literals → resolvent positions
        let c1_to_resolvent =
            build_position_map(&c1_lits, resolvent_clause, pivot_idx_c1, step_id)?;
        let c2_to_resolvent =
            build_position_map(&c2_lits, resolvent_clause, pivot_idx_c2, step_id)?;

        // Determine target type (the resolvent Or-chain, or False if empty)
        let target = if resolvent_props.is_empty() {
            Expr::const_(Name::from_string("False"), vec![])
        } else {
            disjunction::or_chain_type(&resolvent_props)
        };

        // Determine pivot polarity
        let pivot_is_negation = if pivot_swapped {
            ctx.trace().as_not(pivot).is_none()
        } else {
            ctx.trace().as_not(pivot).is_some()
        };

        // Precompute suffix chain types for O(n) lookups
        let c1_suffixes = disjunction::precompute_or_chain_suffixes(&c1_props);
        let c2_suffixes = disjunction::precompute_or_chain_suffixes(&c2_props);
        let resolvent_suffixes = disjunction::precompute_or_chain_suffixes(&resolvent_props);

        Ok(ResolutionPlan {
            left: ClausePlan {
                props: c1_props,
                suffixes: c1_suffixes,
                pivot_idx: pivot_idx_c1,
                to_resolvent: c1_to_resolvent,
            },
            right: ClausePlan {
                props: c2_props,
                suffixes: c2_suffixes,
                pivot_idx: pivot_idx_c2,
                to_resolvent: c2_to_resolvent,
            },
            resolvent_props,
            resolvent_suffixes,
            target,
            pivot,
            pivot_is_negation,
            step_id,
        })
    }
}

/// Find pivot indices in both premise clauses, trying both orientations.
fn find_pivot_indices(
    ctx: &ReconstructionContext<'_>,
    c1_lits: &[TermId],
    c2_lits: &[TermId],
    pivot: TermId,
    step_id: ProofId,
) -> ReconstructResult<(usize, usize, bool)> {
    // Standard: c1 has pivot, c2 has ¬pivot
    if let (Some(c1_idx), Some(c2_idx)) = (
        c1_lits.iter().position(|&l| l == pivot),
        c2_lits.iter().position(|&l| ctx.is_negation_pair(l, pivot)),
    ) {
        return Ok((c1_idx, c2_idx, false));
    }

    // Swapped: c1 has ¬pivot, c2 has pivot
    if let (Some(c1_idx), Some(c2_idx)) = (
        c1_lits.iter().position(|&l| ctx.is_negation_pair(l, pivot)),
        c2_lits.iter().position(|&l| l == pivot),
    ) {
        return Ok((c1_idx, c2_idx, true));
    }

    Err(ReconstructionError::UnsupportedStep {
        step_index: step_id.0,
        description: "pivot not found in either premise clause".to_string(),
    })
}

/// Build position mapping from premise literal indices to resolvent indices.
///
/// Uses a pre-built index for O(P + R) instead of O(P * R) linear scans.
/// Keeps the first occurrence of each TermId to match `.position()` semantics.
fn build_position_map(
    premise_lits: &[TermId],
    resolvent_lits: &[TermId],
    pivot_idx: usize,
    step_id: ProofId,
) -> ReconstructResult<Vec<Option<usize>>> {
    let mut resolvent_index = std::collections::HashMap::with_capacity(resolvent_lits.len());
    for (i, &t) in resolvent_lits.iter().enumerate() {
        resolvent_index.entry(t).or_insert(i);
    }
    premise_lits
        .iter()
        .enumerate()
        .map(|(i, lit)| {
            if i == pivot_idx {
                Ok(None)
            } else {
                resolvent_index.get(lit).copied().map(Some).ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: format!(
                            "non-pivot literal at index {} not found in resolvent",
                            i
                        ),
                    }
                })
            }
        })
        .collect()
}
