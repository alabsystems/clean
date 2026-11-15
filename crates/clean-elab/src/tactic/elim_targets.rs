// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Target resolution for `induction` with a non-recursor eliminator: Lean's
//! `addImplicitTargets` and `checkInductionTargets` for one user-supplied
//! target (see `induction_elim.rs`).

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};

use super::builtins_replace::mentions_fvar;
use super::core::{Goal, ProofState, TacticError};
use super::elim_info::{telescope, ElimInfo, ElimSolution};

fn unsupported(detail: String) -> TacticError {
    TacticError::InvalidTarget {
        tactic: "induction … using".into(),
        detail,
    }
}

/// Lean's `addImplicitTargets` count check for ONE user-supplied target: the
/// target binders that are explicit consume user targets, and every other
/// target binder is implicit. Returns the explicit target's telescope position.
pub(super) fn explicit_target(
    elim_type: &Expr,
    info: &ElimInfo,
    elim_name: &Name,
) -> Result<usize, TacticError> {
    let (binders, _) = telescope(elim_type);
    let explicit: Vec<usize> = info
        .targets_pos
        .iter()
        .copied()
        .filter(|&pos| {
            binders
                .get(pos)
                .is_some_and(|(binder, _)| *binder == BinderInfo::Default)
        })
        .collect();
    match explicit.as_slice() {
        [pos] => Ok(*pos),
        [] => Err(unsupported(format!("Too many targets for `{elim_name}`"))),
        _ => Err(unsupported(format!(
            "Insufficient number of targets for `{elim_name}`"
        ))),
    }
}

/// Every target's local, in target order: the major premise for the explicit
/// target, and for each implicit one the local that matching solved it to.
///
/// Fails closed, as Lean does (`addImplicitTargets`, `checkInductionTargets`),
/// when an implicit target is unsolved, is not a hypothesis of the goal, or
/// repeats another target. Also refuses a let-bound implicit target, and an
/// implicit target some other hypothesis depends on: Lean's `generalizeVars`
/// reverts such a hypothesis into the motive, which this path does not do.
pub(super) fn resolve_targets(
    state: &ProofState,
    goal: &Goal,
    info: &ElimInfo,
    solution: &ElimSolution,
    explicit_pos: usize,
    hyp_fvar: FVarId,
    elim_name: &Name,
) -> Result<Vec<FVarId>, TacticError> {
    let mut fvars: Vec<FVarId> = Vec::with_capacity(info.targets_pos.len());
    for &pos in &info.targets_pos {
        let fvar = if pos == explicit_pos {
            hyp_fvar
        } else {
            let value = solution.binder(pos).ok_or_else(|| {
                unsupported(format!(
                    "Failed to infer implicit target {pos} of `{elim_name}`"
                ))
            })?;
            let value = state.metas.instantiate(value);
            let local = match value.strip_mdata().kind() {
                ExprKind::FVar(id) => goal.local_ctx.iter().find(|d| d.fvar == *id),
                _ => None,
            };
            let Some(local) = local else {
                return Err(unsupported(format!(
                    "Invalid target: Index in target's type is not a variable (consider using \
                     the `cases` tactic instead): {}",
                    crate::error_render::term(&value)
                )));
            };
            if local.value.is_some() {
                return Err(unsupported(format!(
                    "implicit target `{}` of `{elim_name}` is a let-bound local; not supported",
                    local.name
                )));
            }
            local.fvar
        };
        if fvars.contains(&fvar) {
            return Err(unsupported(
                "Invalid target: Target (or one of its indices) occurs more than once".into(),
            ));
        }
        fvars.push(fvar);
    }
    for &implicit in fvars.iter().filter(|&&f| f != hyp_fvar) {
        let dependent = goal.local_ctx.iter().find(|d| {
            !fvars.contains(&d.fvar)
                && (mentions_fvar(&state.metas.instantiate(&d.ty), implicit)
                    || d.value
                        .as_ref()
                        .is_some_and(|v| mentions_fvar(&state.metas.instantiate(v), implicit)))
        });
        if let Some(dependent) = dependent {
            return Err(unsupported(format!(
                "hypothesis `{}` depends on an implicit target of `{elim_name}`; Lean reverts it \
                 into the motive, which is not supported here",
                dependent.name
            )));
        }
    }
    Ok(fvars)
}
