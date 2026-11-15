// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Typed rcases patterns: `rcases h with ⟨f, rfl : r = _⟩`, `obtain ⟨x, hx :
//! p x⟩ := e`, `rintro (h : t)`.
//!
//! Lean's grammar is `rcasesPatLo := rcasesPatMed (" : " term)?`, used inside
//! `⟨…⟩` and `(…)` and after `rcases … with` (`Init/RCases.lean:70,86,88`),
//! and `rcasesCore`'s `.typed` case (`Lean/Elab/Tactic/RCases.lean:290-298`)
//! elaborates the type, `isDefEq`s it with the component's type (which solves
//! its `_`), replaces the local's type by it (`replaceLocalDeclDefEq`), and
//! continues with the inner pattern. Measured before: the pattern readers had
//! no `: term`, so `rcases … with ⟨f, rfl : r = _⟩` (Mathlib
//! `Logic/Function/Basic.lean:1044`) died "expected Comma, got Colon".
//!
//! The parser carries each written type beside the pattern text (a
//! `pattern_types` vector the text refers to as `p : #k`). The destructuring
//! engine has no elaborator, so a typed component is destructured under a
//! fresh name first, and its type is applied here, afterwards, in every goal
//! the destructure left it in — the components are all bound by the same
//! `cases`, so the order does not change what they are.

use clean_parser::{SurfaceExpr, SurfaceName};

use super::registry::TacticEval;
use super::{ProofState, RIntroPattern, TacticError, TacticResult};
use crate::unify::{MetaId, Unifier, UnifyResult};

/// Destructure the hypothesis `hyp_name` by `pattern`, applying every typed
/// sub-pattern `p : #k` with the elaborated type `types[k]`.
pub(crate) fn destruct_with_types(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    hyp_name: &SurfaceName,
    pattern: RIntroPattern,
    types: &[SurfaceExpr],
) -> TacticResult {
    if let RIntroPattern::Typed(inner, k) = pattern {
        ascribe_hypothesis(eval, ps, hyp_name, types, k)?;
        return destruct_with_types(eval, ps, hyp_name, *inner, types);
    }
    let mut deferred = Vec::new();
    let lowered = lower_typed(ps, pattern, &mut deferred);
    super::pattern::destruct_named_hypothesis_pattern(ps, hyp_name, lowered)?;
    for (fresh, inner, k) in deferred {
        let carriers: Vec<MetaId> = ps
            .goals
            .iter()
            .filter(|goal| goal.local_ctx.iter().any(|decl| decl.name == fresh))
            .map(|goal| goal.meta_id)
            .collect();
        // Last carrier first: each processed goal's results land at the
        // front, so the carriers' results keep their order.
        for meta in carriers.into_iter().rev() {
            let Some(pos) = ps.goals.iter().position(|goal| goal.meta_id == meta) else {
                continue;
            };
            if let Some(goal) = ps.goals.remove(pos) {
                ps.goals.push_front(goal);
            }
            let typed = RIntroPattern::Typed(Box::new(inner.clone()), k);
            destruct_with_types(eval, ps, &fresh, typed, types)?;
        }
    }
    Ok(())
}

/// Replace every typed sub-pattern of `pattern` (outside other typed ones) by
/// a fresh name, recording `(name, inner pattern, type index)`.
fn lower_typed(
    ps: &ProofState,
    pattern: RIntroPattern,
    deferred: &mut Vec<(SurfaceName, RIntroPattern, usize)>,
) -> RIntroPattern {
    match pattern {
        RIntroPattern::Typed(inner, k) => {
            let fresh = fresh_name(ps, deferred);
            deferred.push((fresh.clone(), *inner, k));
            RIntroPattern::Name(fresh)
        }
        RIntroPattern::Tuple(sub) => RIntroPattern::Tuple(
            sub.into_iter()
                .map(|p| lower_typed(ps, p, deferred))
                .collect(),
        ),
        RIntroPattern::Anonymous(sub) => RIntroPattern::Anonymous(
            sub.into_iter()
                .map(|p| lower_typed(ps, p, deferred))
                .collect(),
        ),
        RIntroPattern::Or(alts) => RIntroPattern::Or(
            alts.into_iter()
                .map(|p| lower_typed(ps, p, deferred))
                .collect(),
        ),
        RIntroPattern::Explicit(inner) => {
            RIntroPattern::Explicit(Box::new(lower_typed(ps, *inner, deferred)))
        }
        other => other,
    }
}

/// A name no goal uses and no pending component took. It is compiler-authored
/// (a numeric frame no identifier token can spell), so user code cannot reach
/// it.
fn fresh_name(ps: &ProofState, deferred: &[(SurfaceName, RIntroPattern, usize)]) -> SurfaceName {
    let spell = |n: u64| {
        SurfaceName::from_name(
            clean_kernel::Name::anon()
                .num(0x5441_4354)
                .str("rcases_typed")
                .num(n),
        )
    };
    let taken = |name: &SurfaceName| {
        deferred.iter().any(|(other, _, _)| other == name)
            || ps
                .goals
                .iter()
                .any(|goal| goal.local_ctx.iter().any(|decl| &decl.name == name))
    };
    (ps.next_fvar..)
        .map(spell)
        .find(|name| !taken(name))
        .unwrap_or_else(|| spell(u64::MAX))
}

/// `rcasesCore`'s `.typed` step on the current goal's `hyp_name`.
fn ascribe_hypothesis(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    hyp_name: &SurfaceName,
    types: &[SurfaceExpr],
    k: usize,
) -> TacticResult {
    let written = types.get(k).ok_or_else(|| TacticError::InvalidTarget {
        tactic: "rcases".into(),
        detail: format!("typed pattern #{k} carries no type"),
    })?;
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, hyp_name))
        .cloned()
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    // `Term.elabType ty`, its `_` imported as tactic metavariables.
    let refined = eval.elaborate_open(ps, written)?;
    let (ty, holes) = super::term_close::import_open_term(
        ps,
        refined.term,
        eval.metas(),
        &refined.pending_goals,
    )?;
    // `isDefEq etype expected`, which is what solves the `_`.
    let actual = ps.metas.instantiate(&decl.ty);
    let ctx = ps.build_local_ctx(&goal);
    let verdict = {
        let (metas, env) = ps.metas_and_env();
        Unifier::with_env(metas, env, ctx).unify(&ty, &actual)
    };
    if !matches!(verdict, UnifyResult::Success) {
        return Err(TacticError::TypeMismatch {
            expected: format!("{actual}"),
            actual: format!("{ty}"),
        });
    }
    let unsolved = holes.iter().any(|hole| {
        ps.metas
            .get(hole.meta_id)
            .is_some_and(|meta| meta.assignment.is_none())
    });
    let ty = ps.metas.instantiate(&ty);
    if unsolved || super::contains_unassigned_meta(&ty) {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: format!(
                "the type written for '{hyp_name}' leaves a placeholder that its \
                 component's type does not determine"
            ),
        });
    }
    // `replaceLocalDeclDefEq`: re-checked definitionally equal before the swap.
    ps.replace_local_decl_def_eq(decl.fvar, ty)
}
