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

use clean_parser::SurfaceName;

use std::collections::{HashSet, VecDeque};
use std::sync::Arc;

use crate::unify::MetaId;

use super::registry::{CompoundTacticEntry, TacticEval, TacticRegistry};
use super::{ProofState, TacticError};
use clean_parser::{SurfaceExpr, SurfaceInductionAlt, SurfaceTactic};

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
            let SurfaceTactic::Cases(_, hyp, target, alts) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "cases".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // `cases` acts on the main goal; the goals behind it are not its
            // cases and no alternative is matched against them.
            let behind = super::target_equation::goals_behind_main(ps);
            if let Some(eq_name) = hyp {
                return cases_with_equation(eval, ps, eq_name, target, alts, &behind);
            }
            // A name `cases` reads as a HYPOTHESIS only when one of the goal
            // matches it; otherwise it is a term, as for Lean, which
            // elaborates every target (`elabCasesTargets`): a global constant,
            // or a notation template's free name (which never denotes a
            // use-site hypothesis, `local_name_matches`), is a scrutinee term.
            if let Some(hyp_name) =
                surface_expr_to_hyp_name(target).filter(|name| goal_has_hypothesis(ps, name))
            {
                let carried = revert_case_dependents(ps, &hyp_name)?;
                let named =
                    super::proof_manipulation::cases_with_alternatives(ps, &hyp_name, alts)?;
                return eval_induction_alts_generalizing(
                    "cases", eval, ps, alts, &carried, &behind, named,
                );
            }
            // Lean elaborates a cases scrutinee with no expected type.
            let scrutinee = eval.elaborate_no_expected(target)?;
            let named = super::proof_manipulation::cases_expr(ps, scrutinee, alts)?;
            eval_induction_alts_generalizing("cases", eval, ps, alts, &[], &behind, named)
        }),
    }
}

/// `cases h : e with …`.
///
/// Lean 4.8 `elabCasesTargets` (`Lean/Elab/Tactic/Induction.lean`): a target
/// that carries `h :` is ALWAYS generalized (`shouldGeneralizeTarget e <||>
/// pure arg.hName?.isSome`), through `MVarId.generalize`, which abstracts `e`
/// in the TARGET to a fresh inaccessible variable `x` and adds `h : e = x`.
/// `cases x` then eliminates `x`; `h` depends on it, so it is reverted and
/// re-introduced in every branch, where it reads `h : e = cᵢ fields`.
/// Hypotheses that mention `e` are not rewritten, exactly as in Lean.
///
/// The equation is never a hypothesis before the split: the goal is built as
/// `e = x → T[x]` with only `x` introduced (`target_equation`), so the
/// eliminator's motive carries it and every branch's goal reads `e = cᵢ
/// fields → T[cᵢ fields]`. The variable's name is inaccessible and unique, so
/// the elimination acts on it even when the context already holds an `h`;
/// the user's `h` is the name each branch introduces, after the
/// alternative's field names are applied.
fn cases_with_equation(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    eq_name: &SurfaceName,
    target: &SurfaceExpr,
    alts: &[SurfaceInductionAlt],
    behind: &HashSet<MetaId>,
) -> Result<(), TacticError> {
    super::pattern::names::require_binding_name(eq_name, "cases")?;
    let scrutinee = eval.elaborate_no_expected(target)?;
    let var = super::target_equation::generalize_annotated_target(ps, scrutinee, "cases")?;
    let named = super::proof_manipulation::cases_with_alternatives(ps, &var, alts)?;
    eval_induction_alts_generalizing(
        "cases",
        eval,
        ps,
        alts,
        std::slice::from_ref(eq_name),
        behind,
        named,
    )
}

fn surface_expr_to_hyp_name(expr: &SurfaceExpr) -> Option<SurfaceName> {
    super::builtins::surface_expr_to_name(expr).ok()
}

/// Whether the current goal has a hypothesis `name` denotes.
fn goal_has_hypothesis(ps: &ProofState, name: &SurfaceName) -> bool {
    ps.current_goal().is_some_and(|goal| {
        goal.local_ctx
            .iter()
            .any(|decl| super::pattern::names::local_name_matches(&decl.name, name))
    })
}

/// Revert the hypotheses that mention the local `cases` is about to eliminate,
/// so that every case re-introduces them with that local replaced by the
/// case's constructor.
///
/// Lean's `cases x` reaches that context through `generalizeTargetsEq` and
/// `unifyEqs`, whose `subst` rewrites `x` everywhere: `cases b` under
/// `h : b = true` leaves `h : false = true` in the `false` case. Without this
/// step the hypothesis stays in each case still naming `x`, which the case no
/// longer has. Clean takes the route `induction … generalizing` and
/// `cases h : e` already take: revert, eliminate, and re-introduce in every
/// case (`eval_induction_alts_generalizing`).
///
/// Nothing is reverted, and the elimination runs as before, when
/// - no other local mentions `x`;
/// - `x`'s type is `Eq` or `HEq`: `cases` hands those to `subst` and
///   `HEq.ndrec`, which deal with the context themselves;
/// - `x`'s type is not an inductive family: `cases` refuses it, and the
///   refusal should not show a goal this step rewrote;
/// - a `let`-bound local is among the dependents: `revert` would turn it into
///   a plain binder and lose its value.
///
/// Locals are reverted by identity, last first, so a shadowed name cannot send
/// the revert to a different local. Returns their names in revert order.
fn revert_case_dependents(
    ps: &mut ProofState,
    hyp_name: &SurfaceName,
) -> Result<Vec<SurfaceName>, TacticError> {
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    // The local `cases` resolves the name to: the innermost one carrying it.
    let Some((hyp_idx, hyp_decl)) = goal
        .local_ctx
        .iter()
        .enumerate()
        .rev()
        .find(|(_, decl)| super::pattern::names::local_name_matches(&decl.name, hyp_name))
    else {
        return Ok(Vec::new());
    };
    let hyp_ty = ps.whnf(&goal, &ps.metas.instantiate(&hyp_decl.ty));
    let clean_kernel::ExprKind::Const(head, _) = hyp_ty.get_app_fn().kind() else {
        return Ok(Vec::new());
    };
    let routed_elsewhere = *head == clean_kernel::Name::from_string("Eq")
        || *head == clean_kernel::Name::from_string("HEq");
    if routed_elsewhere || ps.env.get_inductive(head).is_none() {
        return Ok(Vec::new());
    }

    // Telescope dependencies include genuine let values and keep marked
    // have proofs opaque. One pass in context order closes the set.
    let mut mentioned: HashSet<clean_kernel::FVarId> = HashSet::from([hyp_decl.fvar]);
    let mut dependents = Vec::new();
    for (idx, decl) in goal.local_ctx.iter().enumerate() {
        if idx == hyp_idx {
            continue;
        }
        if super::major_dependents::generalizing_depends_on(ps, decl, &mentioned) {
            if decl.value.is_some() {
                return Ok(Vec::new());
            }
            dependents.push((decl.fvar, decl.name.clone()));
            mentioned.insert(decl.fvar);
        }
    }

    // `revert` starts the replacement goal untagged; the cases take their
    // tags from this goal's (`some.cons` under `some`), so keep it.
    let tag = goal.tag.clone();
    let mut reverted = Vec::with_capacity(dependents.len());
    for (fvar, name) in dependents.into_iter().rev() {
        super::congr_obtain::revert_fvar(ps, fvar)?;
        reverted.push(name);
    }
    if !reverted.is_empty() {
        if let Some(front) = ps.current_goal_mut() {
            front.tag = tag;
        }
    }
    Ok(reverted)
}

/// The hypothesis `induction` works on. Lean elaborates each target and
/// generalizes one that is not a plain binder (`evalInduction`,
/// `shouldGeneralizeTarget`): a named value-bearing local is generalized too;
/// a target naming an ordinary hypothesis is that hypothesis; any other
/// target — a global constant, a compound term, or a notation template's free
/// name, which never denotes a use-site hypothesis — is elaborated and
/// generalized to a fresh variable no source can name.
fn induction_target(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    target: &SurfaceExpr,
) -> Result<SurfaceName, TacticError> {
    if let Some(name) = surface_expr_to_hyp_name(target) {
        let local = ps.current_goal().and_then(|goal| {
            goal.local_ctx
                .iter()
                .rev()
                .find(|decl| super::pattern::names::local_name_matches(&decl.name, &name))
        });
        // Lean's shouldGeneralizeTarget tests hasValue, including opaque
        // nondependent haves. Generalize that original target before computing
        // the generalizing forbidden set; a plain binder is already a major.
        if local.is_some_and(|decl| decl.value.is_none()) {
            return Ok(name);
        }
    }
    let term = eval.elaborate_no_expected(target)?;
    let fresh = SurfaceName::from_name(
        clean_kernel::Name::anon()
            .num(0x5441_4354)
            .str("induction")
            .num(ps.next_fvar),
    );
    super::generalize(ps, term, &fresh)?;
    Ok(fresh)
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
            // The goals behind the main one are not its cases (see `cases`).
            let behind = super::target_equation::goals_behind_main(ps);
            let hyp_name = induction_target(eval, ps, target)?;

            // Resolve an optional `using <recursor>` override to a Name. Only a
            // (possibly-qualified) constant name is a valid recursor; anything
            // else is rejected up front so it cannot be silently ignored.
            let rec_override = match using_recursor {
                None => None,
                Some(expr) => Some(surface_expr_to_recursor_name(eval, expr)?),
            };

            // `generalizing x y …`, plus every hypothesis that mentions the
            // target (G22): reverted into the goal in context order so the
            // recursor generalizes over them, and re-introduced per case
            // after induction (Lean's `generalizeVars`).
            let reverted = super::major_dependents::generalize_for_induction(
                ps,
                &hyp_name,
                generalizing,
                rec_override.as_ref(),
            )?;

            // `with`-block alternative names, in source order. Only the custom
            // (non-recursor) eliminator path reads them: Clean's kernel `Pi`
            // carries no binder name, so an `@[elab_as_elim]` eliminator's
            // alternative tags are taken positionally from here. See
            // `tactic::induction_elim`.
            let alt_names: Vec<SurfaceName> = alts.iter().map(|a| a.name.clone()).collect();
            super::induction_using_alts(ps, &hyp_name, rec_override.as_ref(), &alt_names)?;

            // The generalized variables are re-introduced per branch (inside
            // `eval_induction_alts_generalizing`, after that branch's `next_fvar` reset) so
            // their fresh FVar IDs stay contiguous within the branch's proof
            // subtree — the invariant `close_fvars` relies on. See the re-intro
            // block in `eval_induction_alts`.
            eval_induction_alts_generalizing("induction", eval, ps, alts, &reverted, &behind, false)
        }),
    }
}

/// Resolve a surface `using <term>` expression to a recursor `Name`.
///
/// A valid recursor is a (possibly-qualified) constant, so only identifier /
/// dotted-projection / parenthesized forms are accepted. Returns `None` for any
/// other expression shape (lambda, application, literal, …), so the caller can
/// reject it before touching the proof state.
fn surface_expr_to_recursor_name(
    eval: &mut dyn TacticEval,
    expr: &SurfaceExpr,
) -> Result<clean_kernel::Name, TacticError> {
    super::builtins::surface_expr_to_name(expr).map_err(|_| TacticError::InvalidTarget {
        tactic: "induction".into(),
        detail: format!(
            "`using` expects a recursor name, got {}",
            crate::error_render::shape(expr)
        ),
    })?;
    // Source qualification and aliases are resolved by the actual elaborator.
    // A local expression must not select a same-spelled global recursor.
    match eval.elaborate(expr)?.kind() {
        clean_kernel::ExprKind::Const(name, _) => Ok(name.clone()),
        _ => Err(TacticError::InvalidTarget {
            tactic: "induction".into(),
            detail: "`using` expects a global recursor constant".into(),
        }),
    }
}

/// Dispatch induction/cases with-clause alternatives to their tagged goals.
///
/// After `cases`/`induction` produce tagged subgoals, each alternative's
/// tactic sequence is matched by constructor name to the goal tag and
/// evaluated in a focused state. User-supplied variable names from
/// `alt.args` are applied to auto-generated hypotheses. A case no
/// alternative covers, a misplaced or repeated alternative, and a named
/// alternative that covers no case are refused, as Lean refuses them; a
/// wildcard that covers no case goal is not (`tactic::induction_alt_check`
/// says why).
/// REQUIRES: `ps.goals` contains the post-`cases`/`induction` tagged subgoals to dispatch.
/// REQUIRES: Alternative names correspond to goal tags when the caller expects those goals to be consumed.
/// ENSURES: On Ok, each matched goal is evaluated in a focused state with user names applied positionally.
/// ENSURES: On Ok, every case goal was covered by an alternative and every named alternative covered a case.
///
/// Re-introduces the generalizing variables in each branch (outermost Pi last).
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
    reverted: &[SurfaceName],
    behind: &HashSet<MetaId>,
    fields_already_named: bool,
) -> Result<(), TacticError> {
    // The elimination replaced the main goal with its cases; they go to the
    // front, and the `behind` goals after them are not cases of it (Lean's
    // `replaceMainGoal`): no alternative is matched against them and no
    // generalized variable is re-introduced into them.
    let produced = super::target_equation::front_produced_goals(ps, behind);
    if alts.is_empty() {
        // No `with` block: still re-introduce the generalized variables into
        // each case goal so the resulting goals are usable and the proof
        // term stays closeable.
        if !reverted.is_empty() {
            let names: Vec<SurfaceName> = reverted.iter().rev().cloned().collect();
            super::target_equation::intro_in_leading_goals(ps, produced, &names, tactic_name)?;
        }
        return Ok(());
    }

    // Lean's `checkAltNames`: the wildcard is last, no name is repeated.
    super::induction_alt_check::check_alt_names(tactic_name, alts)?;

    // Snapshot the case goals so we can process them by tag
    let rest = ps.goals.split_off(produced.min(ps.goals.len()));
    let goals = std::mem::take(&mut ps.goals);
    // Which alternative covers each case; every alternative must cover one.
    let assignment = super::induction_alt_check::assign_alternatives(tactic_name, alts, &goals)?;
    let mut remaining_goals = VecDeque::new();

    // #3528: Track max next_fvar across per-branch tactic evaluation.
    // Each branch resets next_fvar to the branch goal's max FVar + 1, so
    // tactics running inside a branch (including nested `cases`) allocate
    // FVars that fit the branch's binder depth. Without this, nested cases
    // in later branches accumulate FVar IDs that exceed what close_fvars
    // can convert given the proof tree's depth, producing "Declaration
    // contains free variables" or debug_assert panics.
    let mut outer_fvar_max = ps.next_fvar;

    for (mut goal, alt_index) in goals.into_iter().zip(assignment) {
        let matched_alt = alt_index.and_then(|index| alts.get(index));
        if let Some(alt) = matched_alt {
            // The eliminator records exact case fields followed by IH FVars.
            // Names and successor goal MetaIds cannot confer that ownership.
            if !fields_already_named {
                super::builtins_compound::name_alternative_fields(tactic_name, &mut goal, alt)?;
            }
            // #3528: Reset next_fvar to this branch goal's binder base so
            // the branch's tactics allocate IDs that fit its binder depth.
            // Each branch's proof subtree is self-contained; FVars
            // allocated during one branch do not appear in sibling
            // branches' proofs. close_fvars traverses the full proof tree
            // once at the end with depth tracking; each subtree just needs
            // its own FVars to satisfy `(n - base) < depth_within_subtree`.
            //
            // The base is `goal_binder_base`, not one past the context's max:
            // the case's proof sits under the eliminated major's binder, which
            // its context no longer lists but its scope does
            // (`fresh_case_meta`). A context-only base handed a field-less
            // case's first `intro` the major's own id (capture).
            let branch_base = ps.goal_binder_base(&goal);
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
                    super::target_equation::intro_shadowing(ps, name)?;
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
            let tag = goal
                .tag
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<untagged>".into());
            return Err(TacticError::InvalidTarget {
                tactic: tactic_name.into(),
                detail: format!("Alternative `{tag}` has not been provided"),
            });
        }
    }

    // Restore next_fvar to the max used so future allocations are unique.
    ps.next_fvar = outer_fvar_max;

    ps.goals = remaining_goals;
    ps.goals.extend(rest);
    Ok(())
}
