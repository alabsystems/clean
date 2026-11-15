// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `replace h : T := e` — `have`, then drop the hypothesis it supersedes.
//!
//! Port of Lean's `evalReplace` (`Lean/Elab/Tactic/BuiltinTactic.lean:
//! 631-642`, syntax `Init/Tactics.lean:1291`): the locals the declaration
//! introduces are looked up by user name in the ORIGINAL context (a `have`
//! with the same name shadows rather than replaces, so the lookup must happen
//! before it runs), `have` runs, and the older locals are then TRY-cleared —
//! kept when anything still depends on them. Measured before: `replace` had
//! no parser arm and no handler, so `replace h := @h … ?_` (Mathlib
//! `Logic/Function/Basic.lean:681`) died "unexpected token: ColonEq".

use std::sync::Arc;

use clean_kernel::{Expr, ExprVisitor, FVarId};
use clean_parser::{SurfaceName, SurfaceTactic};

use super::registry::CompoundTacticEntry;
use super::{ProofState, TacticError};

/// The compound handler for [`SurfaceTactic::Replace`].
pub(crate) fn compound_replace() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "replace".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Replace(_, inner) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "replace".into(),
                    detail: "unexpected syntax variant".into(),
                });
            };
            // The name `have` binds: its own, or `this` when anonymous (the
            // `have` handler's default, Lean's `haveIdLhs`).
            let introduced = match inner.as_ref() {
                SurfaceTactic::Have(_, name, _, _) => Some(
                    name.clone()
                        .unwrap_or_else(|| SurfaceName::generated_path("this")),
                ),
                _ => None,
            };
            // `origLCtx.findFromUserName?`: the MOST RECENT local of that name.
            let superseded = introduced.as_ref().and_then(|name| {
                ps.current_goal().and_then(|goal| {
                    goal.local_ctx
                        .iter()
                        .rev()
                        .find(|decl| {
                            crate::tactic::pattern::names::hypothesis_named(&decl.name, name)
                        })
                        .map(|decl| decl.fvar)
                })
            });
            eval.eval(ps, inner)?;
            if let (Some(old), Some(name)) = (superseded, introduced.as_ref()) {
                // The local `have` just bound: the most recent of that name.
                let new = ps.current_goal().and_then(|goal| {
                    goal.local_ctx
                        .iter()
                        .rev()
                        .find(|decl| {
                            crate::tactic::pattern::names::hypothesis_named(&decl.name, name)
                                && decl.fvar != old
                        })
                        .map(|decl| decl.fvar)
                });
                try_clear_local(ps, old, new);
            }
            Ok(())
        }),
    }
}

/// Lean's `MVarId.tryClear` on the main goal: remove the local `old` unless
/// the target or another local still mentions it; otherwise leave the goal
/// exactly as it is.
///
/// `new` is the local the `have` bound. Clean records a tactic `have h := e`
/// let-style, with `e` as the local's value, so that value mentions `old`
/// whenever the new proof uses the old hypothesis (`replace h := h h1`). A
/// Lean `have` carries NO value, so that mention is not a dependency there:
/// the value is dropped (the local becomes the opaque hypothesis Lean has)
/// and `old` is cleared. Measured before: the recorded value kept `old`
/// alive, and `assumption` still closed a goal with the superseded `h`,
/// which Lean refuses.
///
/// SOUNDNESS: this only hides a hypothesis from the goal's context and
/// forgets a let-value the proof term already binds (the `let` `have_`
/// emitted is untouched); the proof is assembled and kernel-rechecked as
/// before, and a local that the target or another type depends on is never
/// removed.
fn try_clear_local(ps: &mut ProofState, old: FVarId, new: Option<FVarId>) {
    let Some(goal) = ps.current_goal() else {
        return;
    };
    let Some(idx) = goal.local_ctx.iter().position(|decl| decl.fvar == old) else {
        return;
    };
    let instantiate = |e: &Expr| ps.metas.instantiate(e);
    if mentions_fvar(&instantiate(&goal.target), old) {
        return;
    }
    let depended_on = goal
        .local_ctx
        .iter()
        .filter(|decl| decl.fvar != old)
        .any(|decl| {
            mentions_fvar(&instantiate(&decl.ty), old)
                || (Some(decl.fvar) != new
                    && decl
                        .value
                        .as_ref()
                        .is_some_and(|v| mentions_fvar(&instantiate(v), old)))
        });
    if depended_on {
        return;
    }
    let forget_value = goal.local_ctx.iter().any(|decl| {
        Some(decl.fvar) == new
            && decl
                .value
                .as_ref()
                .is_some_and(|v| mentions_fvar(&instantiate(v), old))
    });
    if let (true, Some(new)) = (forget_value, new) {
        // Through the `local_ops.rs` boundary, like every other rewrite of an
        // inherited local declaration (the bypass ratchet counts direct ones).
        if ps.forget_local_decl_value(new).is_err() {
            return;
        }
    }
    if let Some(goal) = ps.current_goal_mut() {
        goal.local_ctx.remove(idx);
    }
}

/// Whether `expr` mentions the free variable `fvar`.
pub(crate) fn mentions_fvar(expr: &Expr, fvar: FVarId) -> bool {
    struct Finder {
        target: FVarId,
        found: bool,
    }
    impl ExprVisitor for Finder {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if id == self.target {
                self.found = true;
            }
        }
    }
    let mut finder = Finder {
        target: fvar,
        found: false,
    };
    finder.visit_expr(expr);
    finder.found
}
