// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 4: cases/induction tactic registrations.
//!
//! Migrates `Cases` and `Induction` from hardcoded `eval_intro_elim_tactic`
//! dispatch to registry-based compound handlers (#2440).
//!
//! These handlers use `TacticEval::eval()` for recursive sub-tactic
//! evaluation within with-clause alternatives.

use std::collections::VecDeque;
use std::sync::Arc;

use super::registry::{CompoundTacticEntry, TacticEval, TacticRegistry};
use super::{ProofState, TacticError};
use clean_parser::{Projection, SurfaceExpr, SurfaceInductionAlt, SurfaceTactic};

/// Register cases/induction compound tactics into the registry.
/// ENSURES: `registry` contains compound handlers for `cases` and `induction`.
/// ENSURES: Existing compound entries with those names are replaced.
pub(crate) fn register_phase3d_intro(registry: &mut TacticRegistry) {
    registry.register_compound(compound_cases());
    registry.register_compound(compound_induction());
}

/// `cases target with | alt1 => ... | alt2 => ...`
fn compound_cases() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "cases".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Cases(_, target, alts) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "cases".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            if let Some(hyp_name) = surface_expr_to_hyp_name(target) {
                super::cases(ps, &hyp_name)?;
            } else {
                let scrutinee = eval.elaborate(target)?;
                super::proof_manipulation::cases_expr(ps, scrutinee)?;
            }
            eval_induction_alts("cases", eval, ps, alts)
        }),
    }
}

fn surface_expr_to_hyp_name(expr: &SurfaceExpr) -> Option<String> {
    match expr {
        SurfaceExpr::Ident(_, name) => Some(name.clone()),
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            Some(format!("{}.{}", surface_expr_to_hyp_name(base)?, field))
        }
        SurfaceExpr::Paren(_, inner) => surface_expr_to_hyp_name(inner),
        _ => None,
    }
}

/// `induction target (using r)? (generalizing x y …)? with | alt1 => … | …`
///
/// - `using r` runs the named recursor `r` instead of the type's default `.rec`.
///   The name is resolved and handed to [`super::induction_using`], which looks
///   it up like the default recursor (fail-closed if unregistered) and lets the
///   kernel re-check the assembled proof term.
/// - `generalizing x y …` reverts the listed hypotheses (and their dependents)
///   into the goal target *before* running the recursor, so the induction motive
///   quantifies over them and each induction hypothesis becomes `∀ x y, …`; the
///   reverted variables are re-introduced with their original names in every
///   produced case goal, keeping the case bodies (and the final proof term)
///   well-typed and kernel-checkable.
fn compound_induction() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "induction".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Induction {
                target,
                using_recursor,
                generalizing,
                alts,
                ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "induction".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let hyp_name = super::builtins::surface_expr_to_name(target);

            // Resolve an optional `using <recursor>` override to a Name. Only a
            // (possibly-qualified) constant name is a valid recursor; anything
            // else is rejected up front so it cannot be silently ignored.
            let rec_override = match using_recursor {
                None => None,
                Some(expr) => Some(surface_expr_to_recursor_name(expr).ok_or_else(|| {
                    TacticError::InvalidTarget {
                        tactic: "induction".into(),
                        detail: format!("`using` expects a recursor name, got {expr:?}"),
                    }
                })?),
            };

            // `generalizing x y …`: revert the listed hypotheses (dependents
            // first) into the goal so the recursor generalizes over them. The
            // reverted names are re-introduced per case after induction.
            let reverted = revert_generalizing(ps, generalizing)?;

            super::induction_using(ps, &hyp_name, rec_override.as_ref())?;

            // The generalized variables are re-introduced per branch (inside
            // `eval_induction_alts`, after that branch's `next_fvar` reset) so
            // their fresh FVar IDs stay contiguous within the branch's proof
            // subtree — the invariant `close_fvars` relies on. See the re-intro
            // block in `eval_induction_alts`.
            eval_induction_alts_generalizing("induction", eval, ps, alts, &reverted)
        }),
    }
}

/// Resolve a surface `using <term>` expression to a recursor `Name`.
///
/// A valid recursor is a (possibly-qualified) constant, so only identifier /
/// dotted-projection / parenthesized forms are accepted. Returns `None` for any
/// other expression shape (lambda, application, literal, …), so the caller can
/// reject it before touching the proof state.
fn surface_expr_to_recursor_name(expr: &SurfaceExpr) -> Option<clean_kernel::Name> {
    match expr {
        SurfaceExpr::Ident(_, name) => Some(clean_kernel::Name::from_string(name)),
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            let base_name = surface_expr_to_recursor_name(base)?;
            Some(clean_kernel::Name::from_string(&format!(
                "{base_name}.{field}"
            )))
        }
        SurfaceExpr::Paren(_, inner) => surface_expr_to_recursor_name(inner),
        _ => None,
    }
}

/// Revert each `generalizing` hypothesis (with its transitive dependents) into
/// the current goal, returning the reverted names in revert order.
///
/// Reverting is delegated to [`super::specialize_generalize::revert_with_deps`],
/// which computes the dependency closure and reverts dependents before their
/// dependencies, so each resulting goal is well-formed (no dangling FVar). A
/// name that is not a hypothesis in the current goal fails closed
/// (`HypothesisNotFound`). Names already reverted as a dependent of an earlier
/// entry are skipped (they are no longer in context).
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, every named hypothesis (and its dependents) is a Pi binder in
///   the goal target and removed from context.
fn revert_generalizing(
    state: &mut ProofState,
    names: &[String],
) -> Result<Vec<String>, TacticError> {
    let mut reverted: Vec<String> = Vec::new();
    for name in names {
        // Skip names already reverted as a dependent of an earlier entry: they
        // are no longer in the local context. Guarding here keeps `generalizing
        // x y` well-behaved when `y`'s type mentions `x`.
        if reverted.iter().any(|r| r == name) {
            continue;
        }
        let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
        if !goal.local_ctx.iter().any(|d| &d.name == name) {
            return Err(TacticError::HypothesisNotFound(format!(
                "induction … generalizing: '{name}' is not a hypothesis in the current goal"
            )));
        }
        let just_reverted = super::specialize_generalize::revert_with_deps(state, name)?;
        for r in just_reverted {
            if !reverted.iter().any(|existing| existing == &r) {
                reverted.push(r);
            }
        }
    }
    Ok(reverted)
}

/// Dispatch induction/cases with-clause alternatives to their tagged goals.
///
/// After `cases`/`induction` produce tagged subgoals, each alternative's
/// tactic sequence is matched by constructor name to the goal tag and
/// evaluated in a focused state. User-supplied variable names from
/// `alt.args` are applied to auto-generated hypotheses. Unmatched goals
/// are left in place unless a wildcard (`_`) alternative is present.
/// REQUIRES: `ps.goals` contains the post-`cases`/`induction` tagged subgoals to dispatch.
/// REQUIRES: Alternative names correspond to goal tags when the caller expects those goals to be consumed.
/// ENSURES: On Ok, each matched goal is evaluated in a focused state with user names applied positionally.
/// ENSURES: Goals without a matching alternative remain in `ps.goals` unless covered by a wildcard arm.
fn eval_induction_alts(
    tactic_name: &str,
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    alts: &[SurfaceInductionAlt],
) -> Result<(), TacticError> {
    eval_induction_alts_generalizing(tactic_name, eval, ps, alts, &[])
}

/// Like [`eval_induction_alts`], but re-introduces the `generalizing` variables
/// (`reverted`, in revert order — outermost Pi last) at the start of each branch.
///
/// The re-intro runs *after* the branch's `next_fvar` reset and *before* the
/// alternative's tactics, so the re-introduced FVar IDs are contiguous within
/// the branch's proof subtree — the ordering `close_fvars` requires to convert
/// them back to bound variables. Reverting then re-introducing (rather than
/// leaving the branch goal as `∀ x y, …`) is what makes each induction
/// hypothesis usable as `∀ x y, …` while keeping the assembled recursor proof
/// term well-typed and kernel-checkable. When `reverted` is empty this is
/// exactly the plain `cases`/`induction` dispatch.
fn eval_induction_alts_generalizing(
    tactic_name: &str,
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    alts: &[SurfaceInductionAlt],
    reverted: &[String],
) -> Result<(), TacticError> {
    if alts.is_empty() {
        // No `with` block: still re-introduce the generalized variables into
        // each open case goal so the resulting goals are usable and the proof
        // term stays closeable. Focus each goal, reset its FVar base, re-intro.
        if !reverted.is_empty() {
            let num_goals = ps.goals().len();
            for index in 0..num_goals {
                let case_tag = ps.goals().get(index).and_then(|g| g.tag.clone());
                let branch_base = ps
                    .goals()
                    .get(index)
                    .map(|g| {
                        g.local_ctx
                            .iter()
                            .map(|d| d.fvar.as_u64())
                            .max()
                            .map_or(ps.fvar_base, |m| m + 1)
                    })
                    .unwrap_or(ps.fvar_base);
                ps.next_fvar = ps.next_fvar.max(branch_base);
                let outcome = ps.focus_goal(index, |st| {
                    for name in reverted.iter().rev() {
                        super::intro(st, name)?;
                    }
                    Ok(())
                });
                match outcome {
                    Some(res) => res?,
                    None => {
                        return Err(TacticError::InvalidTarget {
                            tactic: tactic_name.into(),
                            detail: "generalizing: goal index out of range".into(),
                        })
                    }
                }
                if let Some(goal) = ps.goals.get_mut(index) {
                    goal.tag = case_tag;
                }
            }
        }
        return Ok(());
    }

    // Separate wildcard alternative from named alternatives
    let wildcard_alt = alts.iter().find(|a| a.name == "_");

    // Snapshot the goals so we can process them by tag
    let goals = std::mem::take(&mut ps.goals);
    let mut remaining_goals = VecDeque::new();

    // #3528: Track max next_fvar across per-branch tactic evaluation.
    // Each branch resets next_fvar to the branch goal's max FVar + 1, so
    // tactics running inside a branch (including nested `cases`) allocate
    // FVars that fit the branch's binder depth. Without this, nested cases
    // in later branches accumulate FVar IDs that exceed what close_fvars
    // can convert given the proof tree's depth, producing "Declaration
    // contains free variables" or debug_assert panics.
    let mut outer_fvar_max = ps.next_fvar;

    for mut goal in goals {
        let tag = goal.tag.as_deref().unwrap_or("");
        // Find a matching alternative: exact name match first, then wildcard
        let matched_alt = alts
            .iter()
            .find(|a| a.name != "_" && a.name == tag)
            .or(wildcard_alt);
        if let Some(alt) = matched_alt {
            // Rename auto-generated hypotheses to user-supplied names.
            // cases/induction generate names like `{tag}_0`, `{tag}_1` for
            // fields and `ih_{tag}_0`, `ih_{tag}_1` for IH hypotheses.
            // alt.args maps positionally to the combined field+IH sequence.
            if !alt.args.is_empty() {
                let tag_prefix = format!("{tag}_");
                let ih_prefix = format!("ih_{tag}_");
                let mut auto_hyp_indices: Vec<usize> = Vec::new();
                // Fields first (in order)
                for (i, decl) in goal.local_ctx.iter().enumerate() {
                    if decl.name.starts_with(&tag_prefix) {
                        auto_hyp_indices.push(i);
                    }
                }
                // Then IH hypotheses (in order)
                for (i, decl) in goal.local_ctx.iter().enumerate() {
                    if decl.name.starts_with(&ih_prefix) {
                        auto_hyp_indices.push(i);
                    }
                }
                // Apply user names positionally
                for (arg_idx, user_name) in alt.args.iter().enumerate() {
                    if arg_idx < auto_hyp_indices.len() {
                        goal.local_ctx[auto_hyp_indices[arg_idx]].name = user_name.clone();
                    }
                }
            }
            // #3528: Reset next_fvar to this branch goal's max FVar + 1 so
            // the branch's tactics allocate IDs that fit its binder depth.
            // Each branch's proof subtree is self-contained; FVars
            // allocated during one branch do not appear in sibling
            // branches' proofs. close_fvars traverses the full proof tree
            // once at the end with depth tracking; each subtree just needs
            // its own FVars to satisfy `(n - base) < depth_within_subtree`.
            let branch_base = goal
                .local_ctx
                .iter()
                .map(|d| d.fvar.as_u64())
                .max()
                .map_or(ps.fvar_base, |m| m + 1);
            ps.next_fvar = branch_base;
            // Focus on this single goal and run the alternative's tactics
            let branch_tag = goal.tag.clone();
            ps.goals = VecDeque::from([goal]);
            // Re-introduce the `generalizing` variables now — after the branch's
            // FVar base is reset and while this branch's goal is the sole focused
            // goal — so their fresh IDs are allocated contiguously within this
            // branch's proof subtree (the invariant `close_fvars` relies on).
            // `intro` builds its subgoal with `tag: None`, so restore the
            // constructor tag afterwards for any downstream `case`-style logic.
            if !reverted.is_empty() {
                for name in reverted.iter().rev() {
                    super::intro(ps, name)?;
                }
                if let Some(front) = ps.current_goal_mut() {
                    front.tag = branch_tag;
                }
            }
            for tac in &alt.tactics {
                eval.eval(ps, tac)?;
            }
            // Track max FVar used across branches so post-loop state is
            // monotonically advanced (safety net for any future consumer
            // that assumes `next_fvar` only increases).
            outer_fvar_max = outer_fvar_max.max(ps.next_fvar);
            // Collect any leftover goals (e.g., from partial proofs)
            remaining_goals.append(&mut ps.goals);
        } else {
            return Err(TacticError::InvalidTarget {
                tactic: tactic_name.into(),
                detail: format!("Alternative `{tag}` has not been provided"),
            });
        }
    }

    // Restore next_fvar to the max used so future allocations are unique.
    ps.next_fvar = outer_fvar_max;

    ps.goals = remaining_goals;
    Ok(())
}
