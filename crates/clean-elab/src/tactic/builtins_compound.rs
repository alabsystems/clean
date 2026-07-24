// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3D Wave 5: compound tactic registrations.
//!
//! Migrates 10 control-flow/combinator tactics from hardcoded `eval_compound_tactic`
//! dispatch to registry-based compound handlers (#2440).
//!
//! These tactics contain sub-tactic sequences and need recursive tactic
//! evaluation via the [`TacticEval`] callback. They do NOT need expression
//! elaboration — tactics needing `elaborate()` (Have, Let, Suffices, Match)
//! remain hardcoded for now and will migrate in Wave 6.

use std::sync::Arc;

use super::registry::{CompoundTacticEntry, TacticRegistry};
use super::{ProofState, TacticError};
use clean_parser::SurfaceTactic;

/// Register compound combinator tactics into the registry.
///
/// These 10 tactics only need recursive `eval_tactic`/`eval_tactic_seq` —
/// they don't need expression elaboration.
/// ENSURES: `registry` contains compound handlers for `paren`, `try`, `focus`, `focus_block`,
/// `repeat`, `all_goals`, `any_goals`, `first`, `seq_focus`, and `case`.
pub(crate) fn register_compound_tactics(registry: &mut TacticRegistry) {
    registry.register_compound(compound_paren());
    registry.register_compound(compound_try());
    registry.register_compound(compound_focus());
    registry.register_compound(compound_focus_block());
    registry.register_compound(compound_repeat());
    registry.register_compound(compound_all_goals());
    registry.register_compound(compound_any_goals());
    registry.register_compound(compound_first());
    registry.register_compound(compound_seq_focus());
    registry.register_compound(compound_case());
}

/// Shared FVar base for a focus/bullet body over the first goal.
///
/// Consecutive `·` bullets (and `focus`/`{}` blocks) over the sibling goals
/// produced by one `constructor`/`apply`/`refine` are PARALLEL siblings: each
/// becomes its own proof lambda at the SAME nesting position in the assembled
/// term. `close_fvars` converts a tactic FVar `n` to a BVar only when
/// `(n - base) < depth`, i.e. it assumes an `intro`'d FVar's id equals its
/// binder *nesting* base. So every sibling's first `intro` must allocate the
/// SAME id.
///
/// Unlike `all_goals`/`seq_focus`, bullets are separate `FocusBlock`/`Focus`
/// items in the enclosing `eval_seq` — there is no per-sibling loop to reset
/// `next_fvar` against a shared base. But the correct shared base is a pure
/// function of the focused goal's own local context, so each bullet can recover
/// it independently: it is the max FVar id already bound in goal 0's context
/// (`fvar + 1`), floored at `fvar_base`. For siblings with identical contexts
/// (the `constructor`/`apply` case) this is identical across bullets, so the
/// first `intro` in each bullet allocates the same id and maps to the same BVar
/// at the same depth. A previous bullet leaving `next_fvar` advanced no longer
/// leaks into the next bullet's allocation.
fn focus_branch_fvar_base(ps: &ProofState) -> u64 {
    // Same quantity `intro` allocates from for the focused goal — factored onto
    // `ProofState` as `goal_fvar_base` so both paths share one definition
    // (#2533). Falls back to `fvar_base` when there is no focused goal.
    ps.goals
        .front()
        .map_or(ps.fvar_base, |goal| ps.goal_fvar_base(goal))
}

/// `(tacs)` — parenthesized tactic sequence, just runs the sequence.
fn compound_paren() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "paren".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Paren(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "paren".into(),
                    detail: "unexpected variant".into(),
                });
            };
            eval.eval_seq(ps, tacs)
        }),
    }
}

/// `try tacs` — run tactics, succeed even if they fail.
fn compound_try() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "try".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Try(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "try".into(),
                    detail: "unexpected variant".into(),
                });
            };
            let clone = ps.clone();
            if eval.eval_seq(ps, tacs).is_err() {
                *ps = clone;
            }
            Ok(())
        }),
    }
}

/// `focus tacs` — focus on the first goal and run tactics.
fn compound_focus() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "focus".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Focus(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "focus".into(),
                    detail: "unexpected variant".into(),
                });
            };
            if ps.goals.is_empty() {
                return Err(TacticError::NoGoals);
            }
            // PARALLEL sibling reset: run this bullet's body from the shared
            // base derived from goal 0's context, not from a `next_fvar` value
            // leaked by an earlier sibling bullet. See `focus_branch_fvar_base`.
            let branch_fvar_base = focus_branch_fvar_base(ps);
            ps.next_fvar = branch_fvar_base;
            let rest = ps.goals.split_off(1);
            let result = eval.eval_seq(ps, tacs);
            // If the focused goal fully closed, its FVars are consumed into the
            // proof term; restore `next_fvar` to the shared base so the next
            // sibling bullet allocates the same ids. If residual goals remain
            // (the `focus` keyword does not force closure), keep the advanced
            // value so later tactics don't collide with those goals' FVars.
            if result.is_ok() && ps.goals.is_empty() {
                ps.next_fvar = branch_fvar_base;
            }
            ps.goals.extend(rest);
            result
        }),
    }
}

/// `{ tacs }` — focus on the first goal, run tactics, require closure.
fn compound_focus_block() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "focus_block".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::FocusBlock(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "focus_block".into(),
                    detail: "unexpected variant".into(),
                });
            };
            if ps.goals.is_empty() {
                return Err(TacticError::NoGoals);
            }
            // PARALLEL sibling reset (the `·` bullet path). Consecutive bullets
            // over the sibling goals of one `constructor`/`apply` are separate
            // `FocusBlock` items in the enclosing sequence; without this, the
            // first bullet's `intro` leaves `next_fvar` advanced and the next
            // bullet's `intro` allocates an id too high for its binder depth,
            // so `close_fvars` cannot convert it and `closed_proof` fails-closed
            // (TacticFailed(ProofNotProduced)). Reset to the shared base derived
            // from goal 0's context. See `focus_branch_fvar_base`.
            let branch_fvar_base = focus_branch_fvar_base(ps);
            ps.next_fvar = branch_fvar_base;
            let rest = ps.goals.split_off(1);
            eval.eval_seq(ps, tacs)?;
            if !ps.goals.is_empty() {
                let remaining = ps.goals.len();
                ps.goals.extend(rest);
                return Err(TacticError::UnsolvedGoals {
                    count: remaining,
                    detail: String::new(),
                });
            }
            // The bullet closed goal 0; its FVars are now bound in the proof
            // term. Restore `next_fvar` to the shared base so the NEXT sibling
            // bullet's `intro` allocates the SAME id at the SAME binder depth.
            ps.next_fvar = branch_fvar_base;
            ps.goals.extend(rest);
            Ok(())
        }),
    }
}

/// `repeat tacs` — repeat tactics until failure.
fn compound_repeat() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "repeat".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Repeat(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "repeat".into(),
                    detail: "unexpected variant".into(),
                });
            };
            const REPEAT_FUEL: usize = 100_000;
            for _ in 0..REPEAT_FUEL {
                let clone = ps.clone();
                if eval.eval_seq(ps, tacs).is_err() {
                    *ps = clone;
                    break;
                }
                if ps.goals().is_empty() {
                    break;
                }
            }
            Ok(())
        }),
    }
}

/// `all_goals tacs` — apply tactics to every goal.
fn compound_all_goals() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "all_goals".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::AllGoals(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "all_goals".into(),
                    detail: "unexpected variant".into(),
                });
            };
            let goals: Vec<_> = ps.goals.drain(..).collect();
            // Reset `next_fvar` to a shared base before each PARALLEL sibling goal
            // so their binder FVars stay aligned with binder *nesting* depth — the
            // invariant `close_fvars` relies on. See `compound_seq_focus` for the
            // full rationale; same root cause, same per-branch reset.
            let branch_fvar_base = ps.next_fvar;
            let mut branch_fvar_max = branch_fvar_base;
            for goal in goals {
                ps.next_fvar = branch_fvar_base;
                let mut focused = ps.clone_with_goal(goal);
                eval.eval_seq(&mut focused, tacs)?;
                branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
                ps.merge_meta_state(&focused);
                ps.goals.append(&mut focused.goals);
            }
            ps.next_fvar = branch_fvar_max;
            Ok(())
        }),
    }
}

/// `any_goals tacs` — apply tactics to each goal, succeed if any works.
fn compound_any_goals() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "any_goals".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::AnyGoals(_, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "any_goals".into(),
                    detail: "unexpected variant".into(),
                });
            };
            let goals: Vec<_> = ps.goals.drain(..).collect();
            let mut any_succeeded = false;
            // Per-branch `next_fvar` reset: PARALLEL sibling goals must allocate
            // binder FVars from the same base to keep the id↔depth correspondence
            // `close_fvars` assumes. See `compound_seq_focus` for the rationale.
            let branch_fvar_base = ps.next_fvar;
            let mut branch_fvar_max = branch_fvar_base;
            for goal in goals {
                ps.next_fvar = branch_fvar_base;
                let mut focused = ps.clone_with_goal(goal.clone());
                let ok = tacs.iter().all(|t| eval.eval(&mut focused, t).is_ok());
                if ok {
                    any_succeeded = true;
                    branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
                    ps.merge_meta_state(&focused);
                    ps.goals.append(&mut focused.goals);
                } else {
                    ps.goals.push_back(goal);
                }
            }
            ps.next_fvar = branch_fvar_max;
            if any_succeeded {
                Ok(())
            } else {
                Err(TacticError::AllTacticsFailed {
                    combinator: "any_goals".into(),
                })
            }
        }),
    }
}

/// `first | tac1 | tac2 | ...` — try branches in order.
fn compound_first() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "first".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::First(_, branches) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "first".into(),
                    detail: "unexpected variant".into(),
                });
            };
            for (idx, branch) in branches.iter().enumerate() {
                if idx + 1 == branches.len() {
                    return eval.eval_seq(ps, branch);
                }

                let mut clone = ps.clone();
                match eval.eval_seq(&mut clone, branch) {
                    Ok(()) => {
                        *ps = clone;
                        return Ok(());
                    }
                    Err(err) if err.is_recoverable_first_failure() => continue,
                    Err(err) => return Err(err),
                }
            }
            Err(TacticError::AllTacticsFailed {
                combinator: "first".into(),
            })
        }),
    }
}

#[cfg(test)]
mod tests;

/// `tac1 <;> tac2` — run tac1, then apply tac2 to each resulting goal.
fn compound_seq_focus() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "seq_focus".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::SeqFocus(_, tac1, tac2) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "seq_focus".into(),
                    detail: "unexpected variant".into(),
                });
            };
            eval.eval(ps, tac1)?;
            let post_tac1 = ps.clone();
            let goals: Vec<_> = post_tac1.goals.iter().cloned().collect();
            let mut merged = post_tac1.clone();
            merged.goals.clear();
            // #close_fvars: the goals produced by `tac1` are PARALLEL siblings —
            // each becomes its own proof lambda at the same nesting position in
            // the assembled term (e.g. the two arms of `Iff.intro`). `close_fvars`
            // converts a tactic FVar `n` to a BVar only when `(n - base) < depth`,
            // i.e. it assumes FVar ids grow with binder *nesting* depth. If sibling
            // branches kept allocating from a monotonically-growing `next_fvar`,
            // branch N's first `intro` FVar would sit at offset N while its lambda
            // is only at depth 1 — `close_fvars` would then leave it unconverted
            // (residual FVar → debug_assert panic / "contains free variables").
            // Resetting `next_fvar` to the shared post-`tac1` base before each
            // branch makes every sibling allocate from the same id, restoring the
            // id↔depth correspondence. Safe because each branch's FVars live only
            // in that branch's own goal/lambda and never cross siblings; the
            // assembled term is still kernel-rechecked by add_decl. Mirrors the
            // per-branch reset in `proof_manipulation.rs` (#3528) and the shared
            // fvar in `existential.rs` (by_cases, #17).
            let branch_fvar_base = merged.next_fvar;
            let mut branch_fvar_max = branch_fvar_base;
            for goal in goals {
                merged.next_fvar = branch_fvar_base;
                let mut focused = merged.clone_with_goal(goal);
                if let Err(err) = eval.eval(&mut focused, tac2) {
                    // Lean 4 expands `<;>` to `focus tac1; all_goals tac2`.
                    // On failure it leaves the active focused-goal state visible
                    // instead of rolling back to the original post-`tac1` queue.
                    merged.merge_meta_state(&focused);
                    merged.goals = focused.goals;
                    *ps = merged;
                    return Err(err);
                }
                branch_fvar_max = branch_fvar_max.max(focused.next_fvar);
                merged.merge_meta_state(&focused);
                merged.goals.append(&mut focused.goals);
            }
            // Restore to the max id reserved by any branch so later allocations
            // don't collide with a branch's FVars.
            merged.next_fvar = branch_fvar_max;
            *ps = merged;
            Ok(())
        }),
    }
}

/// `case tag => tacs` — find goal by tag, focus, run tactics.
fn compound_case() -> CompoundTacticEntry {
    CompoundTacticEntry {
        name: "case".into(),
        handler: Arc::new(|eval, ps, tac| {
            let SurfaceTactic::Case(_, tag, binders, tacs) = tac else {
                return Err(TacticError::InvalidTarget {
                    tactic: "case".into(),
                    detail: "unexpected variant".into(),
                });
            };
            // An anonymous tag (`case _ =>` / `next =>`) focuses the FIRST
            // available goal regardless of its tag, matching Lean's anonymous
            // `binderIdent` case tag. Otherwise match by exact tag, then by
            // dot-suffix, then by prefix.
            let idx = if tag == "_" {
                (!ps.goals.is_empty()).then_some(0)
            } else {
                ps.goals
                    .iter()
                    .position(|g| g.tag.as_deref() == Some(tag.as_str()))
                    .or_else(|| {
                        ps.goals.iter().position(|g| {
                            g.tag.as_deref().is_some_and(|t| name_suffix_match(t, tag))
                        })
                    })
                    .or_else(|| {
                        ps.goals.iter().position(|g| {
                            g.tag.as_deref().is_some_and(|t| name_prefix_match(t, tag))
                        })
                    })
            };
            match idx {
                Some(i) => ps.goals.swap(0, i),
                None => {
                    return Err(TacticError::InvalidTarget {
                        tactic: "case".into(),
                        detail: format!("no goal with tag '{tag}'"),
                    });
                }
            }
            // Rename the case's auto-generated inaccessible hypotheses to the
            // user-supplied binder names (Lean: `case tag x₁ … xₙ => tac`).
            // `cases`/`induction` name constructor fields `{goal_tag}_{N}` and
            // induction hypotheses `ih_{goal_tag}_{N}`; binders map positionally
            // over fields first, then IH hypotheses. `_` leaves a hypothesis
            // unrenamed. This mirrors `eval_induction_alts`' renaming.
            if !binders.is_empty() {
                rename_case_binders(ps, binders);
            }
            // Focus the matched goal: run the case's tactics on it alone, then
            // require it to be solved (Lean's `case` fails if `tac` leaves the
            // focused goal open). Any goals left after `eval_seq` came from the
            // focused case and so signal an unsolved case — surface them as an
            // error rather than silently re-queuing.
            let remaining = ps.goals.split_off(1);
            eval.eval_seq(ps, tacs)?;
            if !ps.goals.is_empty() {
                let count = ps.goals.len();
                ps.goals.extend(remaining);
                return Err(TacticError::UnsolvedGoals {
                    count,
                    detail: format!("case '{tag}' was not closed by its tactics"),
                });
            }
            ps.goals.extend(remaining);
            Ok(())
        }),
    }
}

/// Check if `tag` is a dot-component suffix of `goal_tag`.
fn name_suffix_match(goal_tag: &str, tag: &str) -> bool {
    goal_tag.ends_with(tag)
        && (goal_tag.len() == tag.len()
            || goal_tag.as_bytes()[goal_tag.len() - tag.len() - 1] == b'.')
}

/// Check if `tag` is a dot-component prefix of `goal_tag`.
fn name_prefix_match(goal_tag: &str, tag: &str) -> bool {
    goal_tag.starts_with(tag)
        && (goal_tag.len() == tag.len() || goal_tag.as_bytes()[tag.len()] == b'.')
}

/// Rename the focused case's auto-generated inaccessible hypotheses positionally
/// to the user-supplied `binders` (the `case tag x₁ … xₙ => tac` form).
///
/// `cases`/`induction` name constructor fields `{goal_tag}_{N}` and induction
/// hypotheses `ih_{goal_tag}_{N}`. Binders map positionally over the fields (in
/// order) first, then the IH hypotheses (in order); a `_` binder leaves the
/// corresponding hypothesis unrenamed. Extra binders beyond the available
/// auto-generated hypotheses are ignored (matching the lenient positional
/// renaming used by `eval_induction_alts`). Operates on `ps.goals[0]` (the goal
/// already focused by the `case` handler); a no-op when there is no focused goal.
fn rename_case_binders(ps: &mut ProofState, binders: &[String]) {
    let Some(goal) = ps.goals.front_mut() else {
        return;
    };
    let goal_tag = goal.tag.clone().unwrap_or_default();
    let field_prefix = format!("{goal_tag}_");
    let ih_prefix = format!("ih_{goal_tag}_");

    // Collect indices of auto-generated hypotheses: fields first, then IHs.
    // The `ih_` hypotheses also start with `{goal_tag}_`-shaped substrings, so
    // exclude them from the field pass to keep the two groups disjoint.
    let mut auto_hyp_indices: Vec<usize> = Vec::new();
    for (i, decl) in goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&field_prefix) && !decl.name.starts_with(&ih_prefix) {
            auto_hyp_indices.push(i);
        }
    }
    for (i, decl) in goal.local_ctx.iter().enumerate() {
        if decl.name.starts_with(&ih_prefix) {
            auto_hyp_indices.push(i);
        }
    }

    for (binder, &hyp_idx) in binders.iter().zip(auto_hyp_indices.iter()) {
        if binder != "_" {
            goal.local_ctx[hyp_idx].name = binder.clone();
        }
    }
}
