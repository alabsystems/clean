// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The annotated elimination target `h : e` of `cases` and the tactic
//! `match` — Lean 4.8's `casesTarget := atomic(ident " : ")? term`
//! (`Init/Tactics.lean`) and `matchDiscr` — and the machinery they share.
//!
//! Lean generalizes such a target unconditionally (`elabCasesTargets`:
//! `shouldGeneralizeTarget e <||> pure arg.hName?.isSome`): `e` is
//! abstracted in the target to a fresh variable `x`, `h : e = x` is
//! recorded, `x` is eliminated, and in every resulting goal `h` reads `e =
//! <that goal's instance of x>`. Here the equation stays a binder of the
//! target while `x` is eliminated (`generalize_eq_pending`), so the
//! eliminator's motive carries it, and it is introduced as `h` once the
//! elimination produced its goals. Hypotheses that mention `e` are not
//! rewritten, exactly as in Lean.

use std::collections::{HashSet, VecDeque};

use clean_parser::SurfaceName;

use super::{ProofState, TacticError};
use crate::unify::MetaId;

/// The inaccessible variable an annotated target is generalized to.
///
/// Its name has no surface spelling ([`SurfaceName::unspellable`]), so the
/// elimination acts on IT even when the context already holds a local the
/// user could name `h` or `x`, and no source identifier can refer to it —
/// Lean's `x✝`. A desugared term (the tactic `match`'s discriminant) still
/// resolves it, as the pattern-lambda desugaring resolves its own binder.
pub(crate) fn generalized_target_var(ps: &ProofState, tactic: &str) -> SurfaceName {
    SurfaceName::unspellable(&format!("_{tactic}_target"), ps.next_fvar)
}

/// Introduce exactly the requested user name. Older locals keep their names;
/// by-name lookup selects the newest matching local currently in the context.
/// Clearing that local therefore makes an older matching name visible again.
pub(crate) fn intro_shadowing(ps: &mut ProofState, name: &SurfaceName) -> Result<(), TacticError> {
    super::intro(ps, name)?;
    // The low-level primitive chooses a fresh name. The surface introduction
    // keeps the requested spelling and hygiene marks, including when repeated.
    if let Some(introduced) = ps
        .current_goal_mut()
        .and_then(|goal| goal.local_ctx.last_mut())
    {
        introduced.name = name.clone();
    }
    Ok(())
}

/// Give an elimination field its requested user name without changing any
/// other local, fvar, or context index. A newer matching local may shadow it.
pub(crate) fn name_local_shadowing(goal: &mut super::Goal, index: usize, name: &SurfaceName) {
    if let Some(decl) = goal.local_ctx.get_mut(index) {
        decl.name = name.clone();
    }
}

/// Generalize `scrutinee` in the current goal to a fresh inaccessible
/// variable, leaving `scrutinee = x → target[x]` with only `x` introduced.
/// Returns `x`'s name, for the caller to eliminate.
pub(crate) fn generalize_annotated_target(
    ps: &mut ProofState,
    scrutinee: clean_kernel::Expr,
    tactic: &str,
) -> Result<SurfaceName, TacticError> {
    let var = generalized_target_var(ps, tactic);
    super::generalize::generalize_eq_pending(ps, scrutinee, &var)?;
    Ok(var)
}

/// Introduce `names` (in the order given) at the front of each of the first
/// `count` goals, keeping each goal's case tag.
///
/// Each goal is a case of one elimination, so its proof sits at its OWN
/// binder depth: the base is that goal's `goal_binder_base` — scope-aware, so
/// a binder the case's context no longer lists (the eliminated major
/// premise) is never handed out again — not the global counter.
pub(crate) fn intro_in_leading_goals(
    ps: &mut ProofState,
    count: usize,
    names: &[SurfaceName],
    tactic: &str,
) -> Result<(), TacticError> {
    for index in 0..count {
        let case_tag = ps.goals().get(index).and_then(|g| g.tag.clone());
        let branch_base = ps
            .goals()
            .get(index)
            .map_or(ps.fvar_base, |g| ps.goal_binder_base(g));
        ps.next_fvar = ps.next_fvar.max(branch_base);
        let outcome = ps.focus_goal(index, |st| {
            for name in names {
                intro_shadowing(st, name)?;
            }
            Ok(())
        });
        match outcome {
            Some(res) => res?,
            None => {
                return Err(TacticError::InvalidTarget {
                    tactic: tactic.into(),
                    detail: "re-introduction: goal index out of range".into(),
                })
            }
        }
        if let Some(goal) = ps.goals.get_mut(index) {
            goal.tag = case_tag;
        }
    }
    Ok(())
}

/// The goals behind the main one — the ones an elimination of the main goal
/// must leave alone — by identity.
pub(crate) fn goals_behind_main(ps: &ProofState) -> HashSet<MetaId> {
    ps.goals().iter().skip(1).map(|goal| goal.meta_id).collect()
}

/// Move the goals an elimination produced — every goal not in `behind` — to
/// the front, in their order, ahead of `behind`'s goals, and return how many
/// there are. That is Lean's `replaceMainGoal` (`cases`, `induction`): the
/// eliminators append their cases after the goals already pending, so with a
/// goal behind the main one the cases sat AFTER it, and `cases … with`
/// matched its alternatives against the wrong goal (`case right` of a
/// `constructor`: "Alternative `right` has not been provided").
pub(crate) fn front_produced_goals(ps: &mut ProofState, behind: &HashSet<MetaId>) -> usize {
    let goals = std::mem::take(&mut ps.goals);
    let (produced, rest): (VecDeque<_>, VecDeque<_>) = goals
        .into_iter()
        .partition(|goal| !behind.contains(&goal.meta_id));
    let count = produced.len();
    ps.goals = produced;
    ps.goals.extend(rest);
    count
}
