// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rcases casesTarget,* (with rcasesPatLo)?` — Lean 4.8's `RCases.rcases`
//! (`Lean/Elab/Tactic/RCases.lean`), each `casesTarget := (ident " : ")?
//! term`.
//!
//! Lean elaborates every target, then generalizes them all at once
//! (`generalizeExceptFVar`): a target that is a local hypothesis WITHOUT `h :`
//! is used as is; any other target is abstracted in the goal's target to a
//! fresh variable `x`, and a target with `h :` also records `h : e = x`. The
//! pattern is distributed over the targets (`processConstructor` on the
//! pattern's tuple components), and the targets are destructured left to
//! right, each in every goal the previous one produced (`rcasesContinue`).
//! The equations then read `h : e = <that goal's instance of x>`, and
//! `finish` clears the `-` components last, with their dependents.
//!
//! Here every target that is not a bare local — named or not — is generalized
//! in ONE step by `generalize_eqs_pending` (Lean's `generalizeCore`: every
//! term abstracted out of the goal's target, each equation built from the
//! ORIGINAL term), which keeps the equations binders of the target while the
//! variables are destructured, so the eliminators' motives carry them; they
//! are introduced as `h` in every produced goal before the `-` components are
//! cleared. Each later target is destructured in one produced goal at a time,
//! isolated from its siblings. An unnamed non-local target used to become a
//! `have` instead, which left the goal's occurrences of the term in place:
//! `rcases look n with _ | v` then `exact h` with `h : P (look n)` was accepted
//! against the goal `P none` that pinned Lean has. Without a `with` clause the
//! pattern is `⟨⟩`, which splits a single target one level (`rcases_empty`).

use clean_kernel::Expr;
use clean_parser::{SurfaceName, SurfaceRCasesTarget, SurfaceTactic};

use super::registry::{CompoundTacticEntry, TacticEval};
use super::{ProofState, RIntroPattern, TacticError};
use std::sync::Arc;

/// `rcases h with ⟨hp, hq⟩`, `rcases h : e with _ | x`, `rcases a, b with
/// ⟨p, q⟩`.
///
/// SOUNDNESS: the goal is only ever transformed by the kernel-checked
/// `generalize_eqs_pending` (`Eq.refl` instances close the abstraction),
/// `intro` and the `cases`-based pattern engine; no raw FVars are
/// pushed and no new trust surface is introduced. A pattern that does not
/// match a target's structure surfaces as a `TacticError`, and the assembled
/// proof term is rechecked by `add_decl`.
pub(super) fn compound_rcases() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rcases".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::RCases {
                targets,
                pattern,
                pattern_types,
                pattern_binders,
                ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rcases".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let parsed = RIntroPattern::parse(pattern)?.with_binders(pattern_binders);
            let patterns = distribute_pattern(parsed, targets.len());
            let behind = super::target_equation::goals_behind_main(ps);

            // Elaborate every target first, in order (`RCases.rcases`).
            let mut elaborated = Vec::with_capacity(targets.len());
            for (target, pattern) in targets.iter().zip(&patterns) {
                elaborated.push(elaborate_target(eval, target, pattern, pattern_types)?);
            }
            // `generalizeExceptFVar`: a local WITHOUT `h :` is used as is;
            // every other target is generalized, all of them TOGETHER
            // (`MVarId.generalize`): each is abstracted out of the goal's
            // target, and a named one's equation states its ORIGINAL term, so
            // no target's abstraction rewrites another's equation.
            let mut names = vec![None; targets.len()];
            let mut generalized = Vec::new();
            for (index, (target, term)) in targets.iter().zip(elaborated).enumerate() {
                if let Some(eq_name) = &target.eq_name {
                    super::pattern::names::require_binding_name(eq_name, "rcases")?;
                } else if let Some(local) = local_target(ps, &term)? {
                    names[index] = Some(local);
                    continue;
                } else {
                    refuse_unresolved_type(eval, ps, &term)?;
                }
                generalized.push((index, term, target.eq_name.is_some()));
            }
            let base = ps.next_fvar;
            let vars: Vec<SurfaceName> = (0..generalized.len() as u64)
                .map(|offset| SurfaceName::unspellable("_rcases_target", base + offset))
                .collect();
            let terms: Vec<Expr> = generalized.iter().map(|(_, t, _)| t.clone()).collect();
            let with_eq: Vec<bool> = generalized.iter().map(|(_, _, eq)| *eq).collect();
            super::generalize_many::generalize_eqs_pending(ps, &terms, &vars, &with_eq)?;
            for ((index, _, _), var) in generalized.iter().zip(vars) {
                names[*index] = Some(var);
            }
            let items: Vec<(SurfaceName, RIntroPattern)> =
                names.into_iter().flatten().zip(patterns).collect();
            destruct_targets(eval, ps, &items, pattern_types)?;

            let equations: Vec<SurfaceName> = targets
                .iter()
                .filter_map(|target| target.eq_name.clone())
                .collect();
            if !equations.is_empty() {
                let produced = super::target_equation::front_produced_goals(ps, &behind);
                super::target_equation::intro_in_leading_goals(ps, produced, &equations, "rcases")?;
            }
            // `RCases.finish`: the `-` components go once everything has run.
            super::pattern::finish_rcases_clears(ps);
            Ok(())
        }),
    }
}

/// Elaborate one target as Lean's `RCases.rcases` does: with no expected
/// type (`Term.elabTerm tgt none`), or, when its pattern is typed (`rcases h
/// : 0 with (x : Int)`), against that type (`Term.elabTerm tgt ty`; the
/// pattern's own ascription then plays `ensureHasType`). The enclosing term
/// elaboration's expected type never reaches a target.
fn elaborate_target(
    eval: &mut dyn TacticEval,
    target: &SurfaceRCasesTarget,
    pattern: &RIntroPattern,
    pattern_types: &[clean_parser::SurfaceExpr],
) -> Result<Expr, TacticError> {
    if let RIntroPattern::Typed(_, k) = pattern {
        let expected = pattern_types
            .get(*k)
            .and_then(|written| eval.elaborate_no_expected(written).ok())
            .filter(|ty| !super::contains_unassigned_meta(ty));
        if let Some(expected) = expected {
            return eval.elaborate_expected(&target.term, &expected);
        }
    }
    eval.elaborate_no_expected(&target.term)
}

/// The name of the local an unnamed target IS, or `None` for a term that is
/// not a local (which is generalized).
fn local_target(ps: &ProofState, term: &Expr) -> Result<Option<SurfaceName>, TacticError> {
    let is_local_hyp = matches!(term.kind(), clean_kernel::ExprKind::FVar(id)
        if ps.current_goal().is_some_and(|g| g.local_ctx.iter().any(|d| d.fvar == *id)));
    if is_local_hyp {
        return super::builtins::expr_to_hyp_name(ps, term).map(Some);
    }
    Ok(None)
}

/// An unnamed target that is not a local cannot be generalized while its
/// type still holds an unresolved metavariable (`rcases Classical.em _`).
fn refuse_unresolved_type(
    eval: &mut dyn TacticEval,
    ps: &ProofState,
    term: &Expr,
) -> Result<(), TacticError> {
    let ty = eval.infer_type(term)?;
    if super::contains_unassigned_meta(&ps.metas.instantiate(&ty)) {
        return Err(TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: "cannot destructure: the scrutinee's type still contains an unresolved \
                     metavariable"
                .into(),
        });
    }
    Ok(())
}

/// Destructure the first target by its pattern, then the rest in every goal
/// that produced (`rcasesContinue`). The goals behind the main one are left
/// alone.
fn destruct_targets(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    items: &[(SurfaceName, RIntroPattern)],
    pattern_types: &[clean_parser::SurfaceExpr],
) -> Result<(), TacticError> {
    let Some(((name, pattern), rest)) = items.split_first() else {
        return Ok(());
    };
    let behind = super::target_equation::goals_behind_main(ps);
    super::builtins_phase3d_elab::destruct_parsed_pattern(
        eval,
        ps,
        name,
        pattern.clone(),
        pattern_types,
    )?;
    if rest.is_empty() {
        return Ok(());
    }
    let produced = super::target_equation::front_produced_goals(ps, &behind);
    let mut index = 0;
    for _ in 0..produced {
        let branch_base = ps
            .goals()
            .get(index)
            .map_or(ps.fvar_base, |g| ps.goal_binder_base(g));
        ps.next_fvar = ps.next_fvar.max(branch_base);
        // The branch is destructured ALONE: the eliminators append their
        // cases at the back of the goal list, so with its sibling branches
        // still queued behind it the cases landed after them, and the next
        // branch processed was one of these cases instead of the sibling
        // (`rcases h₁, h₂ with ⟨x | x, y | y⟩` on two `Or`s: "could not find
        // hypothesis to case-split").
        let mut made = 0;
        ps.focus_goal(index, |st| {
            let siblings = st.goals.split_off(1);
            let outcome = destruct_targets(eval, st, rest, pattern_types);
            made = st.goals.len();
            st.goals.extend(siblings);
            outcome
        })
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "rcases".into(),
            detail: "a produced goal is out of range".into(),
        })??;
        index += made;
    }
    Ok(())
}

/// The pattern of each of `count` targets (`RCases.rcases`): one target
/// takes the whole pattern; several take the components of its tuple
/// (`RCasesPatt.asTuple`) by `processConstructor`, a missing one being `_`
/// and the last target taking the tuple of any surplus.
fn distribute_pattern(pattern: RIntroPattern, count: usize) -> Vec<RIntroPattern> {
    if count <= 1 {
        return vec![pattern];
    }
    let mut components = as_tuple(pattern);
    let mut out = Vec::with_capacity(count);
    for _ in 0..count - 1 {
        out.push(if components.is_empty() {
            RIntroPattern::Wildcard
        } else {
            components.remove(0)
        });
    }
    out.push(match components.len() {
        0 => RIntroPattern::Wildcard,
        1 => components.remove(0),
        _ => RIntroPattern::Tuple(components),
    });
    out
}

/// `RCasesPatt.asTuple(..).2`: a tuple's components (an explicit tuple's
/// too), any other pattern alone.
fn as_tuple(pattern: RIntroPattern) -> Vec<RIntroPattern> {
    match pattern {
        RIntroPattern::Tuple(components) | RIntroPattern::Anonymous(components) => components,
        RIntroPattern::Explicit(inner) => as_tuple(*inner),
        other => vec![other],
    }
}

#[cfg(test)]
mod tests {
    use super::{distribute_pattern, RIntroPattern};

    /// `distribute_pattern` of `text` over `count` targets, each component
    /// compared by its debug rendering against the parse of `expected`
    /// (`_` standing for the padding wildcard).
    fn assert_distributes(text: &str, count: usize, expected: &[&str]) {
        let parse = |t: &str| RIntroPattern::parse(t).expect("pattern parses");
        let got: Vec<String> = distribute_pattern(parse(text), count)
            .iter()
            .map(|p| format!("{p:?}"))
            .collect();
        let want: Vec<String> = expected.iter().map(|t| format!("{:?}", parse(t))).collect();
        assert_eq!(got, want, "{text} over {count} targets");
    }

    #[test]
    fn test_distribute_pattern_single_target_keeps_the_whole_pattern() {
        assert_distributes("⟨a, b⟩", 1, &["⟨a, b⟩"]);
        assert_distributes("_ | v", 1, &["_ | v"]);
    }

    #[test]
    fn test_distribute_pattern_splits_tuple_pads_and_regroups_surplus() {
        assert_distributes("⟨a, b⟩", 2, &["a", "b"]);
        assert_distributes("⟨a⟩", 3, &["a", "_", "_"]);
        assert_distributes("⟨a, b, c⟩", 2, &["a", "⟨b, c⟩"]);
        assert_distributes("@⟨a, b⟩", 2, &["a", "b"]);
        // A non-tuple pattern goes to the first target.
        assert_distributes("h | g", 2, &["h | g", "_"]);
    }
}
