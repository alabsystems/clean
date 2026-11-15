// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tactic-mode match dispatch follows actual elaborator hole identities.

use std::collections::HashSet;
use std::sync::Arc;

use super::registry::{CompoundTacticEntry, RefinePendingGoal};
use super::TacticError;
use clean_kernel::Name;
use clean_parser::{
    Span, SurfaceArg, SurfaceExpr, SurfaceMatchArm, SurfaceName, SurfaceTactic, TacticMatchArm,
};

/// Every source arm owns a generated named hole. Recursor reordering, aliases,
/// column splitting and repeated wildcard branches may change the number and
/// order of pending goals; actual hole tags retain the source-arm relation.
/// No constructor display, guessed order or unrelated fresh metavariable can
/// choose which tactic body runs for a pending goal.
pub(crate) fn compound_match() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "match".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Match(span, hyp, discrs, arms) = tac else {
                return Err(invalid_match("unexpected syntax variant"));
            };
            if arms.is_empty() {
                return if ps.goals.is_empty() {
                    Ok(())
                } else {
                    Err(invalid_match("no arms provided"))
                };
            }
            if discrs.is_empty() {
                return Err(invalid_match("no discriminants provided"));
            }
            if hyp.is_some() && discrs.len() != 1 {
                return Err(invalid_match(
                    "an annotated (`h : e`) discriminant must be the only one",
                ));
            }
            // `match h : e with`: Lean's `matchDiscr` generalizes `e` in the
            // goal with `h : e = x`, matches on `x`, and every arm's goal has
            // `h : e = <the arm's pattern>` (Lean 4.8 `Lean/Elab/Match.lean`,
            // the `h :` discriminant). The same generalization `cases h : e`
            // performs (`target_equation`): the equation stays a binder of the
            // target while the fresh variable is matched, and is introduced
            // as `h` in every arm goal the match produced.
            let generalized;
            let discrs: &[SurfaceExpr] = match hyp {
                Some(eq_name) => {
                    super::pattern::names::require_binding_name(eq_name, "match")?;
                    let scrutinee = eval.elaborate_no_expected(&discrs[0])?;
                    let var = super::target_equation::generalize_annotated_target(
                        ps, scrutinee, "match",
                    )?;
                    generalized = [SurfaceExpr::Ident(discrs[0].span(), var)];
                    &generalized
                }
                None => discrs,
            };
            let match_expr = build_tactic_match_expr(*span, discrs, arms);
            let refined = eval.elaborate_refine(ps, &match_expr)?;
            let case_order = pending_arm_order(&refined.pending_goals, arms.len())?;
            let tags: Vec<Option<SurfaceName>> = refined
                .pending_goals
                .iter()
                .map(|pending| Some(match_goal_tag(pending.meta_id.as_u64())))
                .collect();
            super::term_close::refine_eliminator_from_pending_with_tags(
                ps,
                refined.term,
                eval.metas(),
                &refined.pending_goals,
                &tags,
            )?;
            if let Some(eq_name) = hyp {
                super::target_equation::intro_in_leading_goals(
                    ps,
                    tags.len(),
                    std::slice::from_ref(eq_name),
                    "match",
                )?;
            }

            // Each arm goal is its own lambda chain (`PendingLocalIds::ByDepth`
            // numbered the pattern variables from the shared base), so a
            // tactic of one arm must allocate from THAT arm's binder base —
            // the per-branch reset `cases` and `·` perform. The import left
            // `next_fvar` past the deepest arm's binders; a hypothesis an
            // earlier, shallower arm minted from there (`rw [e] at hk`) sat
            // above its binder depth, and `close_fvars` refused the assembled
            // proof ("tactic block completed but no proof term produced").
            let outer_next_fvar = ps.next_fvar;
            for (tag, arm_idx) in tags.into_iter().zip(case_order) {
                let tag = tag.ok_or_else(|| invalid_match("missing generated case tag"))?;
                if let Some(base) = ps
                    .goals
                    .iter()
                    .find(|goal| goal.tag.as_ref() == Some(&tag))
                    .map(|goal| ps.goal_binder_base(goal))
                {
                    ps.next_fvar = base;
                }
                let case_tactic = SurfaceTactic::Case(
                    arms[arm_idx].span,
                    tag,
                    Vec::new(),
                    arms[arm_idx].tactics.clone(),
                );
                let outcome = eval.eval(ps, &case_tactic);
                ps.next_fvar = ps.next_fvar.max(outer_next_fvar);
                outcome?;
            }
            Ok(())
        }),
    }
}

fn invalid_match(detail: impl Into<String>) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "match".into(),
        detail: detail.into(),
    }
}

fn match_arm_tag(index: usize) -> SurfaceName {
    SurfaceName::from_name(Name::anon().num(0x544d_4152).num(index as u64))
}

fn match_goal_tag(meta_id: u64) -> SurfaceName {
    SurfaceName::from_name(Name::anon().num(0x544d_474c).num(meta_id))
}

/// Validate the actual pending-goal census before modifying proof state.
/// Distinct goals may belong to one arm; one meta may not appear twice.
fn pending_arm_order(
    pending: &[RefinePendingGoal],
    arm_count: usize,
) -> Result<Vec<usize>, TacticError> {
    let arm_tags: Vec<_> = (0..arm_count).map(match_arm_tag).collect();
    let mut seen = HashSet::new();
    pending.iter().map(|goal| {
        if !seen.insert(goal.meta_id) {
            return Err(invalid_match(format!("duplicate pending match goal {:?}", goal.meta_id)));
        }
        let tag = goal.tag.as_ref().ok_or_else(|| invalid_match(format!(
            "pending match goal {:?} has no source-arm identity; resolve its open elaboration goal before tactic dispatch", goal.meta_id
        )))?;
        arm_tags.iter().position(|expected| expected.same_syntax(tag)).ok_or_else(|| invalid_match(format!(
            "pending match goal {:?} has an unknown source-arm identity {tag}", goal.meta_id
        )))
    }).collect()
}

/// The term `match discrs with | pat => ?armᵢ …` whose holes the arms'
/// tactics fill — Lean's own expansion of the tactic `match` (a `refine` of
/// that term). An annotated discriminant was generalized by the caller.
fn build_tactic_match_expr(
    span: Span,
    discrs: &[SurfaceExpr],
    arms: &[TacticMatchArm],
) -> SurfaceExpr {
    // RIGHT-nested tuple agrees with the parser's multi-pattern representation.
    let scrutinee = discrs
        .iter()
        .cloned()
        .rev()
        .reduce(|acc, expr| {
            let pair_span = expr.span().merge(acc.span());
            SurfaceExpr::App(
                pair_span,
                Box::new(SurfaceExpr::Ident(
                    pair_span,
                    SurfaceName::global_path("Prod.mk"),
                )),
                vec![SurfaceArg::positional(expr), SurfaceArg::positional(acc)],
            )
        })
        .expect("caller requires a discriminant");
    let arms = arms
        .iter()
        .enumerate()
        .map(|(index, arm)| SurfaceMatchArm {
            span: arm.span,
            pattern: arm.pattern.clone(),
            body: SurfaceExpr::NamedHole(arm.span, match_arm_tag(index)),
        })
        .collect();
    SurfaceExpr::Match(span, None, Box::new(scrutinee), arms)
}

#[cfg(test)]
mod tests;
