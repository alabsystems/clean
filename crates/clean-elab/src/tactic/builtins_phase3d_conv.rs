// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 4: conv tactic registrations.
//!
//! Migrates `Conv`, `ConvArg`, `ConvEnter` from hardcoded `eval_context_terminal_tactic`
//! dispatch to registry-based compound handlers (#2440).
//!
//! `Conv` needs `TacticEval::eval_seq` for running sub-tactic bodies.
//! `ConvArg` and `ConvEnter` only need `ProofState` but receive specialized
//! `SurfaceTactic` variant data (i64, Vec<ConvEnterArg>) that requires
//! pattern matching on the raw tactic.
//!
//! Goal-path and hypothesis-path orchestration live in child modules
//! to reduce churn on this hot registration file. Part of #2547.

use std::sync::Arc;

use super::conv::{ConvPosition, ConvState};
use super::registry::{CompoundTacticEntry, TacticRegistry};
use super::{ProofState, TacticError};
use clean_kernel::Expr;
use clean_parser::{ConvEnterArg, SurfaceTactic, SurfaceTacticLocation};

mod goal;
mod hyps;

fn require_conv_focus_witness(
    conv_ps: &ProofState,
    detail: &'static str,
) -> Result<super::core::ConvFocusWitness, TacticError> {
    conv_ps
        .conv_focus_witness
        .clone()
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "conv".into(),
            detail: detail.into(),
        })
}

/// Reconstruct the full target expression after conv body execution.
///
/// If conv navigation was used (stored in `conv_ps.conv_nav_original` /
/// `conv_ps.conv_nav_path`), replaces the sub-expression at the
/// navigated path with the current focus (`body_target`). Otherwise
/// returns `body_target` unchanged.
///
/// Part of #2477.
fn reconstruct_conv_target(conv_ps: &ProofState, body_target: &Expr) -> Expr {
    if let Some((ref original, ref path)) = conv_ps.conv_nav {
        if !path.is_empty() {
            // Navigation was used — reconstruct the full expression by
            // placing the (possibly rewritten) focus back into the original.
            return ConvState::replace_at_position(original, path, body_target)
                .unwrap_or_else(|| body_target.clone());
        }
    }
    body_target.clone()
}

/// Run a conv body, intercepting conv-mode-only spellings of tactics that
/// otherwise resolve to unrelated top-level tactics.
///
/// `congr` is the motivating case: at the top level `congr` is the Eq-goal
/// splitter (`f a = f b` -> `a = b`), but inside a `conv` block `congr` must
/// descend into the focused application so a following rewrite lifts through
/// `congrArg`. The parser is context-free and emits `Named { name: "congr" }`
/// in both positions, so the conv body evaluator is the only place that knows
/// it is in conversion mode. We intercept a bare `congr` (no args) here and
/// route it to the proof-carrying single-focus `conv_congr`; everything else
/// dispatches normally through `eval`.
///
/// SOUNDNESS: `conv_congr` only narrows the focus via the proven `conv_nav`
/// path; it never closes the goal. The whole-target equality is rebuilt and
/// kernel-type-checked by `eval_conv_goal`/`eval_conv_hyps` via
/// `lift_focus_eq_through_path` + `replace_target_eq`, exactly as for `arg`,
/// `enter`, and `rw`.
pub(super) fn run_conv_body(
    eval: &mut dyn super::registry::TacticEval,
    conv_ps: &mut ProofState,
    tacs: &[SurfaceTactic],
) -> Result<(), TacticError> {
    for tac in tacs {
        if let SurfaceTactic::Named { name, args, .. } = tac {
            if name == "congr" && args.is_empty() {
                super::conv_ext::conv_congr(conv_ps)?;
                continue;
            }
        }
        eval.eval(conv_ps, tac)?;
    }
    Ok(())
}

/// Register conv-related compound tactics into the registry.
/// ENSURES: `registry` contains compound handlers for `conv`, `conv_arg`, and `conv_enter`.
/// ENSURES: Existing compound entries with those names are replaced.
pub(crate) fn register_phase3d_conv(registry: &mut TacticRegistry) {
    registry.register_compound(compound_conv());
    registry.register_compound(compound_conv_arg());
    registry.register_compound(compound_conv_enter());
}

/// `conv (at h)? => body` — enter conversion mode.
///
/// Creates a focused sub-proof-state on the target (or hypothesis type),
/// runs the body tactics, then propagates the modified expression back.
fn compound_conv() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "conv".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Conv(_, loc, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "conv".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            match loc {
                SurfaceTacticLocation::Goal => goal::eval_conv_goal(eval, ps, tacs),
                SurfaceTacticLocation::Hyps(names) => hyps::eval_conv_hyps(eval, ps, names, tacs),
                SurfaceTacticLocation::HypsAndGoal(names) => {
                    hyps::eval_conv_hyps(eval, ps, names, tacs)?;
                    goal::eval_conv_goal(eval, ps, tacs)
                }
                SurfaceTacticLocation::Wildcard => {
                    goal::eval_conv_goal(eval, ps, tacs)?;
                    let hyp_names: Vec<String> = ps
                        .current_goal()
                        .map(|g| g.local_ctx.iter().map(|d| d.name.clone()).collect())
                        .unwrap_or_default();
                    if !hyp_names.is_empty() {
                        hyps::eval_conv_hyps(eval, ps, &hyp_names, tacs)?;
                    }
                    Ok(())
                }
            }
        }),
    }
}

/// `arg i` — conv navigation: focus on the i-th argument of an application.
///
/// Positive i counts from start, negative from end.
/// `arg -1` = last arg (= rhs), `arg -2` = second-to-last (= lhs).
fn compound_conv_arg() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "conv_arg".into(),
        handler: Arc::new(|_eval, ps, tac| {
            let SurfaceTactic::ConvArg(_, i) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "conv_arg".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // Inside an active congr'd conv body, `arg i` selects a sub-focus in
            // the multi-focus tree; otherwise fall back to single-focus nav.
            if super::conv_ext::conv_congr_select(ps, *i)? {
                return Ok(());
            }
            let pos = match i {
                -1 => ConvPosition::EqRhs,
                -2 => ConvPosition::EqLhs,
                0 => ConvPosition::AppFn,
                _ => ConvPosition::AppArg,
            };
            super::builtins::conv_nav(ps, pos)
        }),
    }
}

/// `enter [args]` — conv navigation: compact path into subexpression.
///
/// Part of #2477: stores navigation on `ps.conv_nav_original` /
/// `ps.conv_nav_path` for `eval_conv_goal` reconstruction, matching
/// the pattern in `conv_nav`.
fn compound_conv_enter() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "conv_enter".into(),
        handler: Arc::new(|_eval, ps, tac| {
            let SurfaceTactic::ConvEnter(_, args) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "conv_enter".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // Delegate each step to conv_nav so navigation state accumulates
            for arg in args {
                if let ConvEnterArg::Index(i) = arg {
                    // Inside an active congr tree, an index step selects a focus.
                    if super::conv_ext::conv_congr_select(ps, *i)? {
                        continue;
                    }
                }
                let pos = match arg {
                    ConvEnterArg::Index(i) => match i {
                        -1 => ConvPosition::EqRhs,
                        -2 => ConvPosition::EqLhs,
                        0 => ConvPosition::AppFn,
                        _ => ConvPosition::AppArg,
                    },
                    ConvEnterArg::Name(_) => ConvPosition::BinderBody,
                };
                super::builtins::conv_nav(ps, pos)?;
            }
            Ok(())
        }),
    }
}
