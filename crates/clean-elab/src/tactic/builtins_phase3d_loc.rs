// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 1: location-aware tactic registrations.
//!
//! Migrates `PushNeg`, `Unfold`, `Dsimp` from dedicated `SurfaceTactic`
//! variants to registry dispatch via `SurfaceTactic::Named` (#2440).
//!
//! These tactics accept an optional `at h1 h2`, `at h1 h2 ⊢`, or `at *`
//! location specifier. The parser encodes location as `SurfaceExpr::Ident`
//! args, and the `IdentList` pattern converts them to `Expr::Const(name)`
//! without elaboration. Handlers decode location from the arg names.

use std::collections::VecDeque;
use std::sync::Arc;

use super::builtins::expr_to_hyp_name;
use super::registry::{TacticArgPattern, TacticEntry, TacticRegistry};
use super::TacticError;
use crate::unify::MetaState;

#[derive(Clone)]
struct PushNegWildcardSnapshot {
    goals: VecDeque<super::Goal>,
    metas: MetaState,
    next_fvar: u64,
    trust_ledger: super::ProofTrustLedger,
}

impl PushNegWildcardSnapshot {
    fn capture(ps: &super::ProofState) -> Self {
        Self {
            goals: ps.goals.clone(),
            metas: ps.metas.clone(),
            next_fvar: ps.next_fvar,
            trust_ledger: ps.trust_ledger,
        }
    }

    fn restore(self, ps: &mut super::ProofState) {
        ps.goals = self.goals;
        ps.metas = self.metas;
        ps.next_fvar = self.next_fvar;
        ps.trust_ledger = self.trust_ledger;
        ps.invalidate_tc_cache();
    }
}

/// Location-dispatch combinator for tactics that accept `at h1 h2 | at * | (goal)`.
///
/// Eliminates the duplicated three-way dispatch (empty/wildcard/named) that was
/// previously copy-pasted across `push_neg`, `dsimp`, and `unfold` handlers.
///
/// # Arguments
/// - `ps` — mutable proof state
/// - `args` — elaborated location args from the parser (`IdentList` pattern)
/// - `on_goal` — action when no location is specified (or `⊢` is targeted)
/// - `on_hyp` — action for each named hypothesis
/// - `on_all` — action for the wildcard `*` location
///
/// REQUIRES: `on_goal`, `on_hyp`, and `on_all` leave `ps` unchanged on error.
/// ENSURES: For empty args, calls `on_goal`. For wildcard, calls `on_all`.
/// ENSURES: For named args, calls `on_hyp` per hypothesis, then `on_goal` if `⊢` is present.
pub(crate) fn with_location(
    ps: &mut super::ProofState,
    args: &[clean_kernel::Expr],
    on_goal: impl FnOnce(&mut super::ProofState) -> Result<(), TacticError>,
    on_hyp: impl Fn(&mut super::ProofState, &str) -> Result<(), TacticError>,
    on_all: impl FnOnce(&mut super::ProofState) -> Result<(), TacticError>,
) -> Result<(), TacticError> {
    if args.is_empty() {
        return on_goal(ps);
    }
    if is_wildcard_arg(ps, &args[0]) {
        return on_all(ps);
    }
    let (hyps, apply_goal) = decode_named_location_args(ps, args)?;
    for name in hyps {
        on_hyp(ps, &name)?;
    }
    if apply_goal {
        on_goal(ps)?;
    }
    Ok(())
}

/// Register location-aware tactics migrated in Phase 3D Wave 1.
/// ENSURES: `push_neg`, `dsimp`, and `unfold` are registered with handlers that decode optional location args.
/// ENSURES: Existing simple entries with those names are replaced.
pub(crate) fn register_phase3d_location(registry: &mut TacticRegistry) {
    // push_neg [at h1 h2 | at * | (goal)]
    registry.register(TacticEntry {
        name: "push_neg".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            with_location(
                ps,
                args,
                super::push_neg,
                super::push_neg_at,
                run_push_neg_wildcard,
            )
        }),
    });

    // dsimp [at h1 h2 | at * | (goal)]
    registry.register(TacticEntry {
        name: "dsimp".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            with_location(ps, args, super::dsimp, super::dsimp_at, super::dsimp_all)
        }),
    });

    // unfold <name> [at h1 h2 | at * | (goal)]
    // First arg is always the definition name; remaining args are location.
    registry.register(TacticEntry {
        name: "unfold".to_string(),
        pattern: TacticArgPattern::IdentList,
        handler: Arc::new(|ps, args| {
            let def_name = args
                .first()
                .map(|e| expr_to_hyp_name(ps, e))
                .transpose()?
                .ok_or_else(|| TacticError::MissingArgument {
                    tactic: "unfold".into(),
                    expected: "a definition name".into(),
                })?;
            let loc_args = &args[1..];
            with_location(
                ps,
                loc_args,
                |ps| super::unfold::unfold(ps, &def_name),
                |ps, hyp| super::unfold_at(ps, &def_name, hyp),
                |ps| {
                    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    for decl in &goal.local_ctx {
                        let _ = super::unfold_at(ps, &def_name, &decl.name);
                    }
                    super::unfold::unfold(ps, &def_name)
                },
            )
        }),
    });
}

/// Check if an arg represents the wildcard `*` location.
fn is_wildcard_arg(ps: &super::ProofState, arg: &clean_kernel::Expr) -> bool {
    expr_to_hyp_name(ps, arg).is_ok_and(|n| n == "*")
}

fn is_goal_arg(ps: &super::ProofState, arg: &clean_kernel::Expr) -> bool {
    expr_to_hyp_name(ps, arg).is_ok_and(|n| n == "⊢" || n == "|-")
}

fn decode_named_location_args(
    ps: &super::ProofState,
    args: &[clean_kernel::Expr],
) -> Result<(Vec<String>, bool), TacticError> {
    let mut hyps = Vec::new();
    let mut apply_goal = false;
    for arg in args {
        if is_goal_arg(ps, arg) {
            apply_goal = true;
        } else {
            hyps.push(expr_to_hyp_name(ps, arg)?);
        }
    }
    Ok((hyps, apply_goal))
}

fn run_push_neg_wildcard(ps: &mut super::ProofState) -> Result<(), TacticError> {
    let initial = PushNegWildcardSnapshot::capture(ps);

    // Match Lean's wildcard location semantics: try the target first, then
    // hypotheses, and only fail with `NoProgress` if none of the locations
    // actually changed the proof state.
    let mut worked = match try_push_neg_wildcard_step(ps, super::push_neg) {
        Ok(worked) => worked,
        Err(err) => {
            initial.restore(ps);
            return Err(err);
        }
    };

    let goal = ps.current_goal().ok_or(TacticError::NoGoals)?.clone();
    for decl in goal.local_ctx.iter().rev() {
        match try_push_neg_wildcard_step(ps, |ps| super::push_neg_at(ps, &decl.name)) {
            Ok(step_worked) => worked |= step_worked,
            Err(err) => {
                initial.restore(ps);
                return Err(err);
            }
        }
    }

    if worked {
        Ok(())
    } else {
        Err(TacticError::NoProgress {
            tactic: "push_neg".into(),
        })
    }
}

fn try_push_neg_wildcard_step<F>(ps: &mut super::ProofState, step: F) -> Result<bool, TacticError>
where
    F: FnOnce(&mut super::ProofState) -> Result<(), TacticError>,
{
    let snapshot = PushNegWildcardSnapshot::capture(ps);
    let before_goal_count = ps.goals.len();
    let before_goal = ps.current_goal().cloned();

    match step(ps) {
        Ok(()) => Ok(proof_state_changed(
            before_goal_count,
            before_goal.as_ref(),
            ps,
        )),
        Err(TacticError::NoProgress { .. }) => {
            snapshot.restore(ps);
            Ok(false)
        }
        Err(err) => {
            snapshot.restore(ps);
            Err(err)
        }
    }
}

fn proof_state_changed(
    before_goal_count: usize,
    before_goal: Option<&super::Goal>,
    ps: &super::ProofState,
) -> bool {
    if before_goal_count != ps.goals.len() {
        return true;
    }

    match (before_goal, ps.current_goal()) {
        (Some(before_goal), Some(after_goal)) => {
            before_goal.meta_id != after_goal.meta_id
                || before_goal.target != after_goal.target
                || before_goal.tag != after_goal.tag
                || before_goal.local_ctx.len() != after_goal.local_ctx.len()
                || before_goal.local_ctx.iter().zip(&after_goal.local_ctx).any(
                    |(before_decl, after_decl)| {
                        before_decl.fvar != after_decl.fvar
                            || before_decl.name != after_decl.name
                            || before_decl.ty != after_decl.ty
                            || before_decl.value != after_decl.value
                    },
                )
        }
        (None, None) => false,
        _ => true,
    }
}
