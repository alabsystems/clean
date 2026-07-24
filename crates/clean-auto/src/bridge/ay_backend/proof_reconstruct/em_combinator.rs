// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generic Classical.em case-split combinator for theory-lemma reconstruction.
//!
//! Extracts the shared recursive case-splitting pattern from EUF transitivity,
//! EUF congruent, EUF congruent-pred, and LRA Farkas handlers into a single
//! parameterized combinator. Part of #2537.

use ay_core::{ProofId, TermId};
use clean_kernel::{BinderInfo, Expr};

use super::{ReconstructResult, ReconstructionContext};
use crate::bridge::disjunction;

/// An item to case-split on via Classical.em.
///
/// Each item identifies a negated literal in the clause whose inner proposition
/// will be case-split on. The `clause_idx` indexes into both the clause
/// (for the literal) and the props array (for the typed proposition).
pub(super) struct EmSplitItem {
    /// Index into the clause (for props[] lookup and inject_into_or_chain).
    pub(super) clause_idx: usize,
}

impl<'a> ReconstructionContext<'a> {
    /// Generic Classical.em recursive case-splitting combinator.
    ///
    /// Eliminates a disjunction `¬A₁ ∨ ¬A₂ ∨ ... ∨ ¬Aₙ ∨ C` by case-splitting
    /// on each Aᵢ using `Classical.em`, then calling `base_case` when all Aᵢ are
    /// assumed to hold (as BVar references at known depths).
    ///
    /// At the base case, `depth` equals `items.len()` — the number of lambdas
    /// bound so far. BVar(0) is the innermost (most recently bound) assumption,
    /// and BVar(depth - 1) is the outermost.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_em_case_split(
        &self,
        clause: &[TermId],
        props: &[Expr],
        target: &Expr,
        items: &[EmSplitItem],
        step_id: ProofId,
        idx: usize,
        base_case: &dyn Fn(usize) -> ReconstructResult<Expr>,
    ) -> ReconstructResult<Expr> {
        if idx >= items.len() {
            return base_case(items.len());
        }

        let item = &items[idx];
        let neg_lit = clause[item.clause_idx];
        let inner = self.unwrap_not(neg_lit, step_id)?;
        let prop = self.cached_term(inner, step_id, "em split")?;
        let not_prop = &props[item.clause_idx];

        let em = disjunction::mk_classical_em(&prop);
        let motive = disjunction::mk_constant_or_motive(&prop, not_prop, target);

        let pos_body =
            self.build_em_case_split(clause, props, target, items, step_id, idx + 1, base_case)?;
        let case_pos = Expr::lam(BinderInfo::Default, prop.clone(), pos_body);

        let neg_body = disjunction::inject_into_or_chain(props, item.clause_idx, Expr::bvar(0));
        let case_neg = Expr::lam(BinderInfo::Default, not_prop.clone(), neg_body);

        Ok(disjunction::mk_or_rec(
            &prop, not_prop, &motive, &case_pos, &case_neg, &em,
        ))
    }
}
