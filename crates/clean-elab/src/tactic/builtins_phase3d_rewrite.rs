// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 3: rewrite/simplification tactic registrations.
//!
//! Migrates `Rw`, `Simp`, `SimpRw`, `Simpa` from hardcoded `eval_rewrite_tactic`
//! dispatch to registry-based compound handlers (#2440).
//!
//! Most handlers operate entirely on `ProofState`. The `simp`/`simp_rw`/
//! `simpa` handlers do need `TacticEval`: a lemma-list element that is not a
//! resolvable name is Lean's `simpArg` TERM and is elaborated through
//! `simp::args::resolve_simp_args` (the same `elaborate_open` +
//! `import_open_term` bridge `rw` uses).

use clean_parser::SurfaceName;

use std::sync::Arc;

use super::conv_proof::{
    build_conv_rewrite_eq_proof, chain_conv_focus_eq_proofs, ConvRewriteProofInputs,
};
use super::equality::{contains_expr, match_equality, replace_expr, resolve_env_rewrite_parts};
use super::registry::{CompoundTacticEntry, TacticEval, TacticRegistry};
use super::{ProofState, SimpConfig, TacticError, TacticResult};
use clean_kernel::{Expr, ExprKind, FVarId, Level, Name};
use clean_parser::{
    Projection, SurfaceExpr, SurfaceRwRule, SurfaceSimpArg, SurfaceTactic, SurfaceTacticLocation,
};

/// A rw rule term resolves to a *name* (local hypothesis or environment
/// constant) iff it is a bare identifier, a dotted projection chain
/// (`Nat.testBit_and`), or such a term wrapped in parentheses. Anything else —
/// an application (`lem x y h`), a `show A = B from rfl` ascription, a lambda,
/// etc. — must be elaborated as a *proof term* instead, because reducing it to
/// a `format!`-derived string (as `surface_expr_to_name` does for unhandled
/// variants) would never match a real declaration.
pub(crate) fn rw_rule_is_name(term: &SurfaceExpr) -> bool {
    match term {
        SurfaceExpr::Ident(..) => true,
        SurfaceExpr::Proj(_, base, Projection::Named(_)) => rw_rule_is_name(base),
        SurfaceExpr::Paren(_, inner) => rw_rule_is_name(inner),
        _ => false,
    }
}

/// Does a NAME-shaped rw rule name something the name path can use — a local
/// hypothesis or a (possibly aliased) global constant? Lean's
/// `withRWRulesSeq` takes an identifier as a local or a resolvable global and
/// otherwise elaborates it as a term; `h₂.comp_eq_id` (generalized field
/// notation on a local, `Function.LeftInverse.eq_rightInverse`) names
/// neither and must reach the term path (measured 2026-09-12).
pub(crate) fn rw_name_resolves(ps: &ProofState, term: &SurfaceExpr) -> bool {
    // A rule that is not name-shaped at all belongs to the term path.
    let Ok(name) = super::builtins::surface_expr_to_name(term) else {
        return false;
    };
    let is_local = |n: &SurfaceName| {
        ps.current_goal().is_some_and(|g| {
            g.local_ctx
                .iter()
                .any(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, n))
        })
    };
    if is_local(&name) {
        return true;
    }
    // A dotted name headed by a LOCAL that is not itself a global is field
    // notation on that local (Lean resolves the local first,
    // `isLocalIdent?`): only the term elaborator can read it.
    let dotted_on_local = name
        .split_first()
        .is_some_and(|(head, rest)| !rest.is_anonymous() && is_local(&head))
        && super::core::resolve_global_name(ps, &name)
            .ok()
            .and_then(|global| ps.env().get_const(&global))
            .is_none();
    !dotted_on_local
}

/// Register rewrite/simp compound tactics into the registry.
/// ENSURES: `registry` contains handlers for `rw`, `rewrite`, `rwa`, `simp`, `simp_rw`, and `simpa`.
/// ENSURES: Existing compound entries with those names are replaced.
pub(crate) fn register_phase3d_rewrite(registry: &mut TacticRegistry) {
    registry.register_compound(compound_rw());
    registry.register_compound(compound_rewrite());
    registry.register_compound(compound_rwa());
    registry.register_compound(compound_simp("simp"));
    registry.register_compound(compound_simp("simp_all"));
    registry.register_compound(compound_simp_rw());
    registry.register_compound(compound_simpa());
}

/// Whether a rewrite ends by trying to close the main goal.
///
/// Lean 4.8.0 (`Init/Tactics.lean`): `rewrite` is the rewrite alone at every
/// location, and `rw` is the macro `rewrite …; with_annotate_state … (try
/// (with_reducible rfl))` — the closing step is a REDUCIBLE `rfl`, tried
/// whatever the location. Clean's goal path used to close with a
/// full-transparency `rfl`, so `rw [h]` leaving `ff 1 = 2` (`def ff x := x +
/// 1`), `b + 0 = b` or `[] ++ [1] = [1]` was accepted where pinned Lean says
/// "unsolved goals", and `rewrite` (parsed as `rw`) closed `b = b`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RewriteClose {
    /// `rw`: `try (with_reducible rfl)` on the main goal.
    ReducibleRfl,
    /// `rewrite`: nothing.
    Nothing,
}

/// `rw [rules] (at loc)?` — Lean's macro over `rewrite`.
fn compound_rw() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rw".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Rw(_, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rw".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            run_rewrite(eval, ps, rules, location, RewriteClose::ReducibleRfl)
        }),
    }
}

/// `rwa [rules] (at h)?` — focus the rewrite and its required closing step.
fn compound_rwa() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rwa".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Rwa(span, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rwa".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let invalid_location = || TacticError::InvalidTarget {
                tactic: "rwa".into(),
                detail: "expected the goal or one hypothesis".into(),
            };
            let closing_hypothesis = match location {
                SurfaceTacticLocation::Goal => None,
                SurfaceTacticLocation::Hyps(hyps) => {
                    let [name] = hyps.as_slice() else {
                        return Err(invalid_location());
                    };
                    Some(name.clone())
                }
                _ => return Err(invalid_location()),
            };

            super::builtins_compound::with_focused_goal(eval, ps, |eval, ps| {
                let rewritten_hypothesis = match &closing_hypothesis {
                    None => {
                        run_rewrite(eval, ps, rules, location, RewriteClose::Nothing)?;
                        None
                    }
                    Some(name) => {
                        // Resolve the actual local once, suppressing implicit
                        // argument insertion as Lean's getFVarId does.
                        let target = SurfaceExpr::Explicit(
                            *span,
                            Box::new(SurfaceExpr::Ident(*span, name.clone())),
                        );
                        let resolved = eval.elaborate_open(ps, &target)?;
                        let ExprKind::FVar(fvar) = resolved.term.kind() else {
                            return Err(invalid_location());
                        };
                        if !resolved.pending_goals.is_empty()
                            || !ps
                                .current_goal()
                                .ok_or(TacticError::NoGoals)?
                                .local_ctx
                                .iter()
                                .any(|decl| decl.fvar == *fvar)
                        {
                            return Err(invalid_location());
                        }
                        Some(rw_hyp_rules_fvar(eval, ps, rules, *fvar)?)
                    }
                };
                // Closing the rewritten main goal must not consume a rewrite
                // side goal or a sibling that preceded this `rwa`.
                super::builtins_compound::with_focused_goal(eval, ps, |_eval, ps| {
                    if super::simp::try_reducible_rfl(ps) {
                        return Ok(());
                    }
                    match rewritten_hypothesis {
                        None => super::assumption(ps),
                        Some(fvar) => {
                            // Use the core FVar itself: source `exact h` may
                            // insert arguments or coercions that `rwa at h`
                            // does not authorize.
                            super::exact(ps, Expr::fvar(fvar))
                        }
                    }
                })?;

                // Lean tries reducible reflexivity and assumption on the
                // generated side goals, leaving any remaining ones visible.
                let generated = std::mem::take(&mut ps.goals);
                let mut residual = std::collections::VecDeque::new();
                for goal in generated {
                    ps.goals.push_back(goal);
                    if !super::simp::try_reducible_rfl(ps) {
                        let before = ps.clone();
                        if super::assumption(ps).is_err() {
                            *ps = before;
                        }
                    }
                    residual.append(&mut ps.goals);
                }
                ps.goals = residual;
                Ok(())
            })
        }),
    }
}

/// `rewrite [rules] (at loc)?` — the rewrite with no closing step.
fn compound_rewrite() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "rewrite".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Rewrite(_, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "rewrite".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            run_rewrite(eval, ps, rules, location, RewriteClose::Nothing)
        }),
    }
}

/// The rewrite at `location`, then the closing step `close` names.
fn run_rewrite(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
    location: &SurfaceTacticLocation,
    close: RewriteClose,
) -> Result<(), TacticError> {
    match location {
        SurfaceTacticLocation::Hyps(hyps) => rw_hyp_rules(eval, ps, rules, hyps)?,
        SurfaceTacticLocation::HypsAndGoal(hyps) => {
            rw_hyp_rules(eval, ps, rules, hyps)?;
            rw_goal_rules(eval, ps, rules)?;
        }
        SurfaceTacticLocation::Wildcard => {
            // rw [...] at * — rewrite in all hypotheses then goal.
            // Lean 4 semantics: skip hypotheses used as rewrite lemmas.
            let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
            let lemma_names: Vec<SurfaceName> = rules
                .iter()
                .map(|r| super::builtins::surface_expr_to_name(&r.term))
                .collect::<Result<_, _>>()?;
            for decl in &goal.local_ctx {
                if lemma_names.contains(&decl.name) {
                    continue;
                }
                for rule in rules {
                    let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
                    let _ = super::rewrite_at(ps, &lemma_name, &decl.name, rule.reverse);
                }
            }
            for rule in rules {
                let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
                if rule.reverse {
                    super::rewrite_rtl(ps, &lemma_name)?;
                } else {
                    super::rewrite_ltr(ps, &lemma_name)?;
                }
            }
        }
        SurfaceTacticLocation::Goal => rw_goal_rules(eval, ps, rules)?,
    }
    // Inside a `conv` focus, Lean's `rw` IS `rewrite` (`conv`'s own `rw`
    // macro has no `rfl`); the focused rewrite closes its own witness goal in
    // `rw_goal_rules`, so there is nothing to try here.
    if close == RewriteClose::ReducibleRfl && !in_conv_focus(ps) {
        // Lean's `rw` macro is `rewrite …; try (with_reducible rfl)` whatever
        // the location: after `rw [hab] at h` a main goal `3 = 3` is closed,
        // and a following `rfl` is "no goals to be solved" (review r4t j1).
        let _ = super::simp::try_reducible_rfl(ps);
    }
    Ok(())
}

/// Whether the proof state is focused on a `conv` sub-term.
fn in_conv_focus(ps: &ProofState) -> bool {
    ps.conv_nav
        .as_ref()
        .is_some_and(|(_, path)| !path.is_empty())
        // Multi-focus congr: a selected sub-focus is the focused (possibly
        // non-Prop) target; route to the structural conv rewrite (#2477 Phase 4).
        || (ps.conv_focus_tree.is_some() && ps.conv_congr_cursor.is_some())
}

/// `simp (only)? [lemmas] (at loc)?` — simplification with location dispatch.
fn compound_simp(name: &str) -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: name.into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Simp {
                all,
                only,
                lemmas,
                location,
                use_hypotheses,
                ..
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simp".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            let star = *use_hypotheses;
            if *all {
                let mut config = SimpConfig::new();
                config.only = *only;
                config.use_hypotheses = star;
                apply_simp_args(eval, ps, lemmas, &mut config)?;
                return super::simp_all_with_config(ps, config);
            }
            match location {
                SurfaceTacticLocation::Hyps(hyps) => {
                    simp_hyps(eval, ps, *only, lemmas, hyps, star).map(|_| ())
                }
                SurfaceTacticLocation::HypsAndGoal(hyps) => {
                    // A hypothesis simplified to `False` closed the goal:
                    // there is no `⊢` left to visit.
                    if simp_hyps(eval, ps, *only, lemmas, hyps, star)? == HypsOutcome::ClosedGoal {
                        return Ok(());
                    }
                    simp_goal_with_lemmas(eval, ps, *only, lemmas, star)
                }
                SurfaceTacticLocation::Wildcard => {
                    // The lemma list reaches `at *` too: Lean builds ONE
                    // `Simp.Context` and `simpLocation` hands it to every
                    // location. This arm used to call `simp_at_all` with no
                    // config at all, so `simp only [h] at *` ran the default
                    // simp set and never saw `h`.
                    let mut config = SimpConfig::new();
                    config.only = *only;
                    config.use_hypotheses = star;
                    config.assumption_closer = SURFACE_ASSUMPTION_CLOSER;
                    apply_simp_args(eval, ps, lemmas, &mut config)?;
                    super::simp::simp_at_all_with_config(ps, config)
                }
                SurfaceTacticLocation::Goal => simp_goal_with_lemmas(eval, ps, *only, lemmas, star),
            }
        }),
    }
}

/// Write a resolved simp lemma list into a [`SimpConfig`] — Lean's
/// `mkSimpContext`'s channels: the by-name set, the erasures, the
/// already-built rules (term arguments and every `←`-reversed one), and the
/// simprocs the call runs.
///
/// REQUIRES: `config.only` is already set — it decides what a named simproc
///   means (`lean_builtin_simprocs::simproc_scope`).
fn apply_simp_args(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    lemmas: &[SurfaceSimpArg],
    config: &mut SimpConfig,
) -> Result<(), TacticError> {
    let resolved = super::simp::args::resolve_simp_args(eval, ps, lemmas)?;
    let world = super::simp::lean_builtin_simprocs::source_world(eval, ps)?;
    config.simprocs =
        super::simp::lean_builtin_simprocs::simproc_scope(world, config.only, &resolved.simprocs)?;
    config.reduce_ctor_eq =
        super::simp::lean_builtin_simprocs::ctor_eq_enabled(world, config.only, &resolved.simprocs);
    config.legacy_ctor_closer = !super::simp::lean_builtin_simprocs::has_named_ctor_eq(world);
    config.extra_lemmas = resolved.extra_lemmas;
    config.exclude = resolved.exclude;
    config.aesop_simp_lemmas.extend(resolved.prebuilt);
    Ok(())
}

fn simp_goal_with_lemmas(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    only: bool,
    lemmas: &[SurfaceSimpArg],
    use_hypotheses: bool,
) -> Result<(), TacticError> {
    let mut config = SimpConfig::new();
    // `only` here reproduces `super::simp_only`, which sets exactly these two
    // fields; carrying `use_hypotheses` alongside is what makes `simp only [*]`
    // reachable.
    config.only = only;
    config.use_hypotheses = use_hypotheses;
    config.assumption_closer = SURFACE_ASSUMPTION_CLOSER;
    apply_simp_args(eval, ps, lemmas, &mut config)?;
    super::simp(ps, config)
}

/// The closer a SURFACE `simp` runs with (G49, ledger (119)): none.
///
/// Lean's `simp` closes a goal only when it simplifies to `True`; it never
/// runs `assumption`, so `h : n = 0 ⊢ n = 0` under a bare `simp` is "simp made
/// no progress". That holds under `[*]` too: there every hypothesis is a
/// rewrite rule, which closes a goal the hypothesis matches SYNTACTICALLY
/// (up to instances), but an `assumption` step would also close one it
/// matches only up to unfolding — `h : myid n = 0 ⊢ n = 0` with `def myid n
/// := n` is "simp made no progress" in pinned Lean 4.8.0 under `simp [*]`
/// (review r4t probe t1), and was accepted while `[*]` kept the closer on.
const SURFACE_ASSUMPTION_CLOSER: super::simp::AssumptionCloser = super::simp::AssumptionCloser::Off;

/// `simp_rw [rules] (at loc)?` — simp + rw combined.
fn compound_simp_rw() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "simp_rw".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::SimpRw(_, rules, location) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simp_rw".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // `parse_rw_rules` records each rule's `←`; this handler used to
            // map only `r.term` through `surface_expr_to_name` and drop the
            // flag, so `simp_rw [← h]` rewrote FORWARD. The rules go through
            // the same `simpArg` resolution `simp` uses, which carries the
            // direction and gives a term-shaped rule the term path.
            let args: Vec<SurfaceSimpArg> = rules
                .iter()
                .map(|r| SurfaceSimpArg {
                    span: r.span,
                    phase: None,
                    reverse: r.reverse,
                    erase: false,
                    term: r.term.clone(),
                })
                .collect();
            let resolved = super::simp::args::resolve_simp_args(eval, ps, &args)?;
            // Lean's `simp_rw [r]` is `simp only [r]`, so a simproc rule runs
            // that simproc alone; Clean's `simp_rw` passes are not `only`
            // passes and have no simproc channel, so such a rule is refused
            // by name rather than dropped.
            if let Some(simproc) = resolved
                .simprocs
                .added
                .first()
                .or(resolved.simprocs.erased.first())
            {
                return Err(TacticError::InvalidTarget {
                    tactic: "simp_rw".into(),
                    detail: format!("simproc rule `{simproc}` is not supported by Clean"),
                });
            }
            let names = resolved.extra_lemmas;
            let prebuilt = resolved.prebuilt;
            match location {
                SurfaceTacticLocation::Hyps(hyps) => {
                    simp_rw_hyps_outcome(ps, &names, &prebuilt, hyps).map(|_| ())
                }
                SurfaceTacticLocation::HypsAndGoal(hyps) => {
                    if simp_rw_hyps_outcome(ps, &names, &prebuilt, hyps)? == HypsOutcome::ClosedGoal
                    {
                        return Ok(());
                    }
                    super::simp::simp_rw_with_rules(ps, names, prebuilt)
                }
                SurfaceTacticLocation::Wildcard => {
                    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    let open = ps.goals.len();
                    for decl in &goal.local_ctx {
                        let name = decl.name.clone();
                        let _ = simp_rw_at_hyp(ps, &names, &prebuilt, &name);
                        if super::simp::simp_at_closed_goal(ps, open) {
                            return Ok(());
                        }
                    }
                    super::simp::simp_rw_with_rules(ps, names, prebuilt)
                }
                SurfaceTacticLocation::Goal => super::simp::simp_rw_with_rules(ps, names, prebuilt),
            }
        }),
    }
}

/// Apply `rw` rules to the current goal target.
///
/// When inside a navigated conv body (`ps.conv_nav` has a non-empty path), the
/// target is a focused sub-expression (possibly non-Prop). The generic `Eq.subst`
/// path requires a Prop-valued target, so we dispatch to `conv_focus_rewrite`
/// for structural replacement and let `eval_conv_goal` lift the proof (#2540).
fn rw_goal_rules(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
) -> Result<(), TacticError> {
    if in_conv_focus(ps) {
        // Conv navigation rewrites a (possibly non-Prop) focused sub-expression
        // through a structural witness; that path is name-keyed only. A
        // non-name rewrite term here is unsupported, so it still falls through
        // `surface_expr_to_name` (which yields a non-matching name → clear error).
        for rule in rules {
            let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
            conv_focus_rewrite(ps, &lemma_name, rule.reverse)?;
        }
        // The conv focus's own closing step, unchanged; the surface `rw`'s
        // reducible `rfl` is `run_rewrite`'s, never run under a conv focus.
        let _ = super::rfl(ps);
    } else {
        for rule in rules {
            if rw_rule_is_name(&rule.term) && rw_name_resolves(ps, &rule.term) {
                let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
                if rule.reverse {
                    super::rewrite_rtl(ps, &lemma_name)?;
                } else {
                    super::rewrite_ltr(ps, &lemma_name)?;
                }
            } else {
                // Non-identifier rule term: elaborate it as a proof term and
                // rewrite by its inferred equality type (`rw [show A = B from
                // rfl]`, `rw [lem x y h]`, …).
                let (proof, side_goals) = elaborate_rw_rule(eval, ps, &rule.term)?;
                super::rewrite_with_proof(ps, proof, rule.reverse)?;
                push_unsolved_side_goals(ps, side_goals);
            }
        }
    }
    Ok(())
}

/// Elaborate a non-identifier `rw` rule with no expected type and import the
/// metavariables its elaboration left open into the proof state, so the
/// rewrite can solve them against the goal (`term_rewrite_equation`). A lemma
/// whose implicit arguments are fixed only by its statement —
/// `forall_update_iff f fun a b ↦ ¬p a b`, `{a} {b}` — used to reach the
/// rewriter with elaborator-scope metavariables the proof state could not
/// even type (`Unknown free variable`), or, where it could, treated as rigid
/// locals by the syntactic search (measured 2026-09-11). Returns the term
/// and the goals of the imported metavariables, for
/// [`push_unsolved_side_goals`] after the rewrite.
fn elaborate_rw_rule(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    term: &SurfaceExpr,
) -> Result<(Expr, Vec<super::Goal>), TacticError> {
    let refined = eval.elaborate_open(ps, term)?;
    super::term_close::import_open_term(ps, refined.term, eval.metas(), &refined.pending_goals)
}

/// After a `rw`, the imported metavariables the rewrite did not solve become
/// side goals AFTER the main goal — Lean's `rw` does the same with the
/// hypotheses of a conditional rule (`rw [h]` with `h : p → a = b` leaves
/// `⊢ p`). A solved one is dropped.
fn push_unsolved_side_goals(ps: &mut ProofState, side_goals: Vec<super::Goal>) {
    for goal in side_goals {
        let unsolved = ps
            .metas
            .get(goal.meta_id)
            .is_some_and(|meta| meta.assignment.is_none());
        if unsolved {
            ps.goals.push_back(goal);
        }
    }
}

/// Thread the checked replacement local through every rule, including delta
/// unfolding and elaborated proof terms. Names never select a later target.
fn rw_hyp_rules_fvar(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
    mut target: FVarId,
) -> Result<FVarId, TacticError> {
    for rule in rules {
        if rw_rule_is_name(&rule.term) && rw_name_resolves(ps, &rule.term) {
            let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
            target = super::equality::rewrite_at_fvar(ps, &lemma_name, target, rule.reverse)?;
        } else {
            let (proof, side_goals) = elaborate_rw_rule(eval, ps, &rule.term)?;
            target = super::equality::rewrite_at_fvar_with_proof(ps, proof, target, rule.reverse)?;
            push_unsolved_side_goals(ps, side_goals);
        }
    }
    Ok(target)
}

fn rw_hyp_rules(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    rules: &[SurfaceRwRule],
    hyps: &[SurfaceName],
) -> Result<(), TacticError> {
    for hyp in hyps {
        for rule in rules {
            if rw_rule_is_name(&rule.term) && rw_name_resolves(ps, &rule.term) {
                let lemma_name = super::builtins::surface_expr_to_name(&rule.term)?;
                super::rewrite_at(ps, &lemma_name, hyp, rule.reverse)?;
            } else {
                // `rw [<term>] at h`: elaborate the rule as a proof term and
                // rewrite the hypothesis by its inferred equality type
                // (`rw [Nat.add_comm a b] at h`, `rw [lem x y] at h`, …).
                let (proof, side_goals) = elaborate_rw_rule(eval, ps, &rule.term)?;
                super::rewrite_at_with_proof(ps, proof, hyp, rule.reverse)?;
                push_unsolved_side_goals(ps, side_goals);
            }
        }
    }
    Ok(())
}

/// `simp (only)? [lemmas] at h₁ … hₙ`. `only` reaches the config here as it
/// does on the goal (`simp_goal_with_lemmas`) and at `*`: Lean builds one
/// `Simp.Context` for every location, so `simp only [] at h` starts from
/// `simpOnlyBuiltins` and never sees a `@[simp]` lemma. This path used to drop
/// the flag, so `simp only [] at hc` on `hc : c ∈ [1, 2]` rewrote by the
/// default set's `List.mem_cons` where pinned Lean 4.8.0 says "simp made no
/// progress" (trust-ir G25 review, ledger class (94)).
/// It also showed once the default set gained Lean's `not_true_eq_false`
/// (G39): `simp only [e] at h` with `h : ¬e` turned `h` into `False` where
/// pinned Lean leaves `¬True`.
fn simp_hyps(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    only: bool,
    lemmas: &[SurfaceSimpArg],
    hyps: &[SurfaceName],
    use_hypotheses: bool,
) -> Result<HypsOutcome, TacticError> {
    let mut config = SimpConfig::new();
    // `simp only [..] at h` runs the named rules only, as at `⊢` and `at *`.
    // Before `apply_simp_args`: it reads `only` to scope named simprocs.
    config.only = only;
    config.use_hypotheses = use_hypotheses;
    apply_simp_args(eval, ps, lemmas, &mut config)?;
    require_hypotheses(ps, hyps)?;
    let open = ps.goals.len();
    for hyp in hyps {
        // Lean's `simpGoal` removes the hypothesis being simplified from its
        // own set, so `simp [*] at h` cannot rewrite `h : P` to `True` by `h`.
        let mut hyp_config = config.clone();
        hyp_config.exclude_hypothesis = Some(hyp.clone());
        super::simp::simp_at_with_config(ps, hyp, hyp_config)?;
        if super::simp::simp_at_closed_goal(ps, open) {
            return Ok(HypsOutcome::ClosedGoal);
        }
    }
    Ok(HypsOutcome::GoalOpen)
}

/// Every location named must exist BEFORE any of them is visited.
///
/// Lean resolves the whole location list up front (`elabLocation`:
/// "Unknown identifier"), so `simp at h hmissing` is an error even when `h`
/// alone would close the goal. Since a closed goal ends the visit early, a
/// name checked only when its turn came would never be checked at all.
fn require_hypotheses(ps: &ProofState, hyps: &[SurfaceName]) -> Result<(), TacticError> {
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?;
    match hyps.iter().find(|hyp| {
        !goal
            .local_ctx
            .iter()
            .any(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, hyp))
    }) {
        Some(missing) => Err(TacticError::HypothesisNotFound(missing.to_string())),
        None => Ok(()),
    }
}

/// What visiting a list of hypothesis locations left behind.
///
/// Lean's `applySimpResult` closes the goal when a hypothesis simplifies to
/// `False` and visits no later location; the next hypothesis name would
/// otherwise be looked up in whatever goal came next.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HypsOutcome {
    /// Every hypothesis was rewritten and the goal is still open.
    GoalOpen,
    /// A hypothesis became `False` and closed the goal.
    ClosedGoal,
}

/// One `simp_rw` step at one hypothesis, carrying BOTH resolved channels.
///
/// `simp_only_at` takes only the by-NAME list, so routing the hypothesis
/// locations through it dropped every `←`-reversed and every term-shaped rule
/// with no diagnostic — a silent no-op where the pre-`simpArg` code at least
/// ran the rule (in the wrong direction for `←`, and refused a term outright).
/// The config is `simp_only_at`'s own (`SimpConfig::new()` plus the names;
/// note it does NOT set `only`) with `prebuilt` added on the channel
/// `resolve_simp_args` fills.
fn simp_rw_at_hyp(
    ps: &mut ProofState,
    names: &[SurfaceName],
    prebuilt: &[super::simp::types::SimpLemma],
    hyp: &SurfaceName,
) -> TacticResult {
    let mut config = SimpConfig::new();
    config.extra_lemmas = names.to_vec();
    config.aesop_simp_lemmas = prebuilt.to_vec();
    super::simp::simp_at_with_config(ps, hyp, config)
}

fn simp_rw_hyps_outcome(
    ps: &mut ProofState,
    names: &[SurfaceName],
    prebuilt: &[super::simp::types::SimpLemma],
    hyps: &[SurfaceName],
) -> Result<HypsOutcome, TacticError> {
    require_hypotheses(ps, hyps)?;
    let open = ps.goals.len();
    for hyp in hyps {
        simp_rw_at_hyp(ps, names, prebuilt, hyp)?;
        if super::simp::simp_at_closed_goal(ps, open) {
            return Ok(HypsOutcome::ClosedGoal);
        }
    }
    Ok(HypsOutcome::GoalOpen)
}

/// Structural focus-only rewrite for navigated conv mode.
///
/// When `rw` runs inside a navigated conv body (`ps.conv_nav` has a non-empty
/// path), the current goal target is the focused sub-expression, which may be
/// non-Prop (e.g., `x : Nat`). The generic `rewrite` path builds an `Eq.subst`
/// proof whose motive must be a type family `α → Prop`, which is ill-typed for
/// term-valued focuses.
///
/// This helper rewrites the focused target and records a checked equality
/// witness on the nested proof state. The outer `eval_conv_goal` /
/// `eval_conv_hyps` in `builtins_phase3d_conv.rs` lifts that focused witness
/// through the saved navigation path.
///
/// Part of #2555.
fn conv_focus_rewrite(
    ps: &mut ProofState,
    hyp_name: &SurfaceName,
    reverse: bool,
) -> Result<(), TacticError> {
    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = ps.metas.instantiate(&goal.target);

    // Resolve the rewrite rule to a concrete equation `base_proof : lhs = rhs`
    // (original orientation). A local hypothesis of the name shadows an
    // environment constant (Lean 4 resolution order). When no local hypothesis
    // exists, fall back to the environment: `resolve_env_rewrite_parts` peels
    // the constant's leading `∀` binders to metavariables and unifies its
    // `from` side against the focus `target` to solve them — the identical
    // resolution `rw [envLemma]` performs, here lifted through conv's
    // congruence proof (`build_conv_rewrite_eq_proof`) rather than
    // `finish_rewrite`. This is what lets `conv => …; rw [Nat.add_zero]` reach
    // an env lemma instead of failing `HypothesisNotFound`.
    let (eq_type, lhs, rhs, eq_levels, base_proof): (Expr, Expr, Expr, Vec<Level>, Expr) =
        match goal
            .local_ctx
            .iter()
            .rev()
            .find(|d| crate::tactic::pattern::names::hypothesis_named(&d.name, hyp_name))
        {
            Some(hyp_decl) => {
                let hyp_decl = hyp_decl.clone();
                let hyp_ty = ps.whnf(&goal, &hyp_decl.ty);
                let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty)?;
                (eq_type, lhs, rhs, eq_levels, Expr::fvar(hyp_decl.fvar))
            }
            None => resolve_env_rewrite_parts(ps, &goal, hyp_name, reverse, &target)?,
        };

    // Orient the (concrete) equation for the requested direction and build the
    // leaf equality proof. `base_proof : lhs = rhs`; a reverse rewrite flips the
    // sides and wraps the proof in `Eq.symm`. (For the env path, the metavars
    // were already solved against the correct — reverse-aware — `from` side, so
    // both `lhs` and `rhs` are concrete here.)
    let (from, to, leaf_eq_proof) = if reverse {
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels);
        let symm_proof = Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type.clone()), lhs.clone()),
                rhs.clone(),
            ),
            base_proof,
        );
        (rhs, lhs, symm_proof)
    } else {
        (lhs, rhs, base_proof)
    };

    if !contains_expr(&target, &from) {
        return Err(TacticError::no_progress("rw"));
    }

    let new_target = replace_expr(&target, &from, &to);
    let step_eq_proof = build_conv_rewrite_eq_proof(
        ps,
        &goal,
        ConvRewriteProofInputs {
            target: &target,
            path: &[],
            focus_before: &target,
            focus_after: &new_target,
            from: &from,
            to: &to,
            from_ty: &eq_type,
            leaf_eq_proof,
        },
    )?
    .ok_or_else(|| {
        TacticError::TypeCheckFailed("conv_rw: failed to build focus rewrite witness".into())
    })?;
    // Multi-focus congr tree active with a selected focus: write the rewrite
    // into that focus node instead of the global single-focus witness. The
    // per-focus equalities are recombined at the conv reconstruction boundary
    // (#2477 Phase 4).
    if let Some(cursor) = ps.conv_congr_cursor.clone() {
        let prev_eq = focus_eq_proof_at(ps, &cursor);
        let new_eq = match prev_eq {
            Some(existing) => chain_conv_focus_eq_proofs(ps, &goal, &existing, &step_eq_proof)?,
            None => step_eq_proof,
        };
        write_congr_focus_rewrite(ps, &cursor, new_target.clone(), new_eq)?;
        if let Some(g) = ps.current_goal_mut() {
            g.target = new_target;
        }
        return Ok(());
    }

    let accumulated_witness = match ps.conv_focus_witness.as_ref() {
        Some(existing) => super::core::ConvFocusWitness {
            before: existing.before.clone(),
            after: new_target.clone(),
            eq_proof: chain_conv_focus_eq_proofs(ps, &goal, &existing.eq_proof, &step_eq_proof)?,
        },
        None => super::core::ConvFocusWitness {
            before: target.clone(),
            after: new_target.clone(),
            eq_proof: step_eq_proof,
        },
    };
    ps.conv_focus_witness = Some(accumulated_witness);
    if let Some(g) = ps.current_goal_mut() {
        g.target = new_target;
    }
    Ok(())
}

/// The current accumulated `eq_proof` for the focus at the cursor path, if any.
fn focus_eq_proof_at(ps: &ProofState, cursor: &[usize]) -> Option<Expr> {
    ps.conv_focus_tree
        .as_ref()?
        .focus_at_path(cursor)?
        .eq_proof
        .clone()
}

/// Write a rewrite result (`after` + `before = after` proof) into the focus at
/// the cursor path of the active congr tree.
fn write_congr_focus_rewrite(
    ps: &mut ProofState,
    cursor: &[usize],
    after: Expr,
    eq_proof: Expr,
) -> Result<(), TacticError> {
    let tree = ps.conv_focus_tree.as_mut().ok_or_else(|| {
        TacticError::TypeCheckFailed("conv congr: rewrite outside an active focus tree".into())
    })?;
    let focus = tree.focus_at_path_mut(cursor).ok_or_else(|| {
        TacticError::TypeCheckFailed("conv congr: focus cursor out of range".into())
    })?;
    focus.after = after;
    focus.eq_proof = Some(eq_proof);
    Ok(())
}

/// Opt-in timing for the two passes of a source `simpa`. As with
/// `CLEAN_SIMP_MATCH_TRACE`, the value is a substring filter, read once. An
/// empty value traces every module. The surface span is the tactic keyword's
/// half-open UTF-8 byte range in the enclosing module.
struct SimpaTrace {
    module: Option<String>,
    span: clean_parser::Span,
    only: bool,
}

impl SimpaTrace {
    fn new(ps: &ProofState, span: clean_parser::Span, only: bool) -> Self {
        static FILTER: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
        let filter = FILTER.get_or_init(|| std::env::var("CLEAN_SIMPA_PHASE_TRACE").ok());
        let module = filter.as_ref().and_then(|filter| {
            let module = ps
                .namespace_state()
                .and_then(crate::namespace::NamespaceState::main_module)
                .map_or_else(|| "<unknown>".to_owned(), ToString::to_string);
            module.contains(filter).then_some(module)
        });
        Self { module, span, only }
    }

    fn phase<T>(&self, phase: &str, run: impl FnOnce() -> T) -> T {
        let Some(module) = &self.module else {
            return run();
        };
        let (start, end, only) = (self.span.start, self.span.end, self.only);
        eprintln!(
            "[simpa-phase] module={module} bytes={start}..{end} only={only} phase={phase} start"
        );
        let started = std::time::Instant::now();
        let result = run();
        let elapsed_us = started.elapsed().as_micros();
        eprintln!("[simpa-phase] module={module} bytes={start}..{end} only={only} phase={phase} end elapsed_us={elapsed_us}");
        result
    }
}

/// `simpa (only)? [lemmas] (using term)?` — simp the goal, then close it.
///
/// With `using term`, the goal is simplified (best effort) and then closed with
/// the elaborated `term` via `exact` (the term's type must be definitionally
/// equal to the simplified goal — the common `simpa using lemma_app` shape where
/// `simp` is a no-op and the lemma closes the goal directly). Without `using`,
/// it simplifies and falls back to `assumption`.
///
/// `simp` making no progress is *not* a failure here: `simpa` succeeds whenever
/// the closing step (the `using` term, or an assumption) discharges the
/// post-simplification goal, exactly as in Lean 4.
fn compound_simpa() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "simpa".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Simpa {
                only,
                lemmas,
                use_hypotheses,
                using_term,
                span,
            } = tac
            else {
                return Err(TacticError::InvalidTarget {
                    tactic: "simpa".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };

            // The one simp configuration `simpa` runs, used for BOTH the goal
            // and the `using` term's type — Lean simplifies them with the same
            // simp set, and using two would let them normalize apart.
            //
            // The lemma list is used with or without `only`, as Lean's
            // `mkSimpContext` does (`Lean/Elab/Tactic/Simpa.lean`); it used to
            // be read only under `only`, so `simpa [hx]` ran without `hx`
            // (`Function.Bijective.existsUnique_iff`, measured 2026-09-12).
            let mut config = SimpConfig::new();
            config.only = *only;
            // `simpa` runs Lean's `mkSimpContext` like `simp` does, so `[*]`
            // means "also every Prop hypothesis" here too. The parser bound
            // this flag to `_use_hypotheses` and dropped it, so `simpa [*]`
            // was a strictly weaker `simpa` — pinned v4.30.0-rc2 closes
            // `example (h : P) : P ∨ Q := by simpa [*] using True.intro`.
            config.use_hypotheses = *use_hypotheses;
            // Lean's `simpa` simplifies the goal with a plain `simp`, which
            // has no `assumption` step (G49): the closing step is `exact e`
            // with `using e` (pinned Lean 4.8.0 refuses `(hq : Q) (hp : P) :
            // P := by simpa using hq`, "type mismatch"), and `assumption`
            // below only without it. With the closer on, the goal's simp
            // closed it from `hp` and `e` was never checked (review r4t s1-s3).
            config.assumption_closer = SURFACE_ASSUMPTION_CLOSER;
            apply_simp_args(eval, ps, lemmas, &mut config)?;

            // Simplify the goal. A `NoProgress` result is tolerated: the closing
            // step below may still discharge the (unchanged) goal.
            let trace = SimpaTrace::new(ps, *span, *only);
            match trace.phase("goal", || super::simp(ps, config.clone())) {
                Ok(()) => {}
                Err(TacticError::NoProgress { .. }) | Err(TacticError::NoGoals) => {}
                Err(e) => return Err(e),
            }

            // If simp already closed the goal, we are done.
            if ps.current_goal().is_none() {
                return Ok(());
            }

            match using_term {
                Some(term) => trace.phase("using", || {
                    // Lean elaborates the using term with no expected type
                    // (`elabTerm stx none`), so a constant's leading implicit
                    // arguments become metavariables that the closing `exact`
                    // solves against the goal (`simpa [Pi.lt_def] using
                    // le_of_lt`, `Function.const_lt_const`, measured
                    // 2026-09-12). Open elaborator metavariables are imported
                    // into the proof state (the `rw` bridge).
                    let saved = ps.clone();
                    let (proof, _) = elaborate_rw_rule(eval, ps, term)?;
                    // Lean's `simpa … using e` simplifies `e`'s TYPE too and
                    // closes with the transported term. Running `exact` on the
                    // raw term made `simpa` work only where simp was a no-op on
                    // `e`. Transport is a no-op when nothing to transport.
                    let proof = super::simp::simp_proof_type(ps, config, proof);
                    // Lean's `simpGoal` on the noted `using` hypothesis: one
                    // simplified to `False` closes the goal, and there is no
                    // closing `exact` (`hyp_false`).
                    if super::simp::close_goal_by_proof_of_false(ps, &proof) {
                        return Ok(());
                    }
                    match super::exact(ps, proof) {
                        Ok(()) => Ok(()),
                        Err(transport_err) => {
                            // A term whose leading implicits only the goal can
                            // fix (`simpa using le_of_lt`) is elaborated
                            // against the simplified goal instead, as Lean's
                            // closing `exact` unifies them.
                            *ps = saved;
                            let target = ps
                                .current_goal()
                                .map(|g| ps.metas.instantiate(&g.target))
                                .ok_or(TacticError::NoGoals)?;
                            match eval.elaborate_expected(term, &target) {
                                Ok(p) => super::exact(ps, p).map_err(|_| transport_err),
                                Err(_) => Err(transport_err),
                            }
                        }
                    }
                }),
                None => super::assumption(ps),
            }
        }),
    }
}
