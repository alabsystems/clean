// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Finite type case splitting tactic (`fin_cases`).
//!
//! Provides tactics for case splitting on finite types like `Bool`, `Fin n`,
//! `PUnit`. For integer interval splitting, see `interval_cases.rs`.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::{Goal, ProofState, TacticError, TacticResult};
use crate::stack_safe;

use super::finite_cases_proof::build_fin_cases_proof;

// ============================================================================
// fin_cases - Case split on finite types
// ============================================================================

/// Case split on a hypothesis of finite type.
///
/// `fin_cases` works on hypotheses whose type is a finite type (like Fin n,
/// Bool, or an enumeration). It creates a goal for each possible value.
///
/// # Algorithm
/// 1. Identify the hypothesis and its finite type
/// 2. Enumerate all inhabitants of the type
/// 3. Create a subgoal for each inhabitant with the hypothesis instantiated
///
/// # Example
/// ```text
/// -- h : Fin 3
/// -- Goal: P h
/// fin_cases h
/// -- Goal 1: P 0
/// -- Goal 2: P 1
/// -- Goal 3: P 2
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `HypNotFound` if the hypothesis is not found
/// - `Other` if the type is not finite
///
/// REQUIRES: `state` is a well-formed proof state
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal's context
///
/// ENSURES: on `Ok(())`, the original goal is closed via a case-split proof
/// and one sub-goal per inhabitant is prepended to `state.goals`
/// ENSURES: on `Err(NoGoals)`, `state` is unchanged
/// ENSURES: on `Err(HypothesisNotFound)`, `state` is unchanged
/// ENSURES: on `Err(InvalidTarget)`, `state` is unchanged
pub fn fin_cases(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the hypothesis
    let hyp = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check if the type is finite
    let inhabitants = get_finite_inhabitants(&hyp.ty)?;

    if inhabitants.is_empty() {
        return Err(TacticError::InvalidTarget {
            tactic: "fin_cases".into(),
            detail: format!("{hyp_name} has no inhabitants or is not a finite type"),
        });
    }

    // Create new goals for each case
    let mut new_goals = Vec::new();
    let preserve_dependent_target = uses_or_rec_fallback(&hyp.ty, inhabitants.len())
        && goal.target.abstract_fvar(hyp.fvar) != goal.target;

    for inhabitant in &inhabitants {
        // Create a new context where hyp is replaced with its value
        let mut new_ctx = goal.local_ctx.clone();

        // Find and update the hypothesis
        for decl in &mut new_ctx {
            if decl.name == hyp_name {
                decl.value = Some(inhabitant.clone());
            }
        }

        // Bool/PUnit use proper dependent recursors, so they can keep the
        // specialized target. The Or.rec fallback cannot manufacture the final
        // branch equality witness, so dependent targets must stay unspecialized
        // and use the branch-local equality proof instead.
        let new_target = if preserve_dependent_target {
            goal.target.clone()
        } else {
            substitute_fvar(&goal.target, hyp.fvar, inhabitant)
        };

        let new_meta_id = state.fresh_meta(new_target.clone());
        new_goals.push(Goal {
            meta_id: new_meta_id,
            target: new_target,
            local_ctx: new_ctx,
            tag: None,
        });
    }

    // SOUNDNESS FIX (#2232): Construct eliminator proof term linking original
    // goal meta to sub-goal metas before closing the goal. Previously, the goal
    // was popped without meta assignment, leaving an orphaned metavariable.
    let proof = build_fin_cases_proof(state, &goal, &hyp, &new_goals, &inhabitants)?;

    // Part of #2154 Wave 10: migrated from close_goal_unchecked.
    // For Bool: @Bool.casesOn with correct motive and constructor-ordered branches.
    // For PUnit: @PUnit.casesOn with correct motive and PUnit.unit minor.
    // For Fin n / other: Or.rec + Classical.em chain with all sub-goal metas linked.
    // Requires env with Bool/PUnit as proper inductives + Or.rec for Or chain path.
    state.close_goal(&goal, proof)?;

    for new_goal in new_goals.into_iter().rev() {
        state.goals.push_front(new_goal);
    }

    Ok(())
}

fn uses_or_rec_fallback(ty: &Expr, num_inhabitants: usize) -> bool {
    match ty.kind() {
        ExprKind::Const(name, _) => {
            let name = name.to_string();
            !((name == "Bool" && num_inhabitants == 2)
                || ((name == "Unit" || name == "unit" || name == "PUnit") && num_inhabitants == 1))
        }
        _ => true,
    }
}

/// Get inhabitants of a finite type
///
/// REQUIRES: `ty` is a well-formed Lean type expression
///
/// ENSURES: on `Ok(inhabitants)`, each element is a valid constructor/literal
/// for the given type
/// ENSURES: returns `Ok(vec![])` for `Empty`/`False` (vacuous case)
/// ENSURES: returns `Err(InvalidTarget)` for unrecognized finite types
pub(crate) fn get_finite_inhabitants(ty: &Expr) -> Result<Vec<Expr>, TacticError> {
    match ty.kind() {
        ExprKind::Const(name, levels) => {
            let name_str = name.to_string();

            // Bool has two inhabitants: true and false
            if name_str == "Bool" {
                return Ok(vec![
                    Expr::const_(Name::from_string("true"), vec![]),
                    Expr::const_(Name::from_string("false"), vec![]),
                ]);
            }

            // PUnit/Unit has one inhabitant.
            // Part of #2154: use correct constructor name + propagate universe levels
            // so close_goal type-checking can match PUnit.casesOn minor types.
            if name_str == "PUnit" {
                return Ok(vec![Expr::const_(
                    Name::from_string("PUnit.unit"),
                    levels.clone(),
                )]);
            }
            if name_str == "Unit" || name_str == "unit" {
                return Ok(vec![Expr::const_(Name::from_string("Unit.unit"), vec![])]);
            }

            // Empty/False has no inhabitants
            if name_str == "Empty" || name_str == "False" {
                return Ok(vec![]);
            }

            Err(TacticError::InvalidTarget {
                tactic: "fin_cases".into(),
                detail: format!("{name_str} is not a recognized finite type"),
            })
        }
        ExprKind::App(f, arg) => {
            // Check for Fin n
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Fin" {
                    // Try to extract n
                    if let Some(n) = extract_nat_literal(arg) {
                        let mut inhabitants = Vec::new();
                        for i in 0..n {
                            inhabitants.push(make_fin_literal(arg, n as u64, i as u64));
                        }
                        return Ok(inhabitants);
                    }
                }
            }
            Err(TacticError::InvalidTarget {
                tactic: "fin_cases".into(),
                detail: "not a recognized finite type".into(),
            })
        }
        _ => Err(TacticError::InvalidTarget {
            tactic: "fin_cases".into(),
            detail: "not a finite type".into(),
        }),
    }
}

/// Extract a natural number from an expression
///
/// REQUIRES: `expr` is a well-formed Lean expression
///
/// ENSURES: returns `Some(n)` when `expr` is a Nat literal, `Nat.zero`,
/// a numeric constant name, or a `Nat.succ` chain
/// ENSURES: returns `None` for non-Nat expressions
/// ENSURES: recursive descent runs under `stack_safe`
pub(crate) fn extract_nat_literal(expr: &Expr) -> Option<usize> {
    stack_safe(|| match expr.kind() {
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == "Nat.zero" {
                return Some(0);
            }
            // Try to parse as a number
            name_str.parse().ok()
        }
        ExprKind::Lit(lit) => {
            if let clean_kernel::expr::Literal::Nat(n) = lit {
                n.to_u64().and_then(|v| usize::try_from(v).ok())
            } else {
                None
            }
        }
        ExprKind::App(f, arg) => {
            // Check for Nat.succ
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    if let Some(n) = extract_nat_literal(arg) {
                        return Some(n + 1);
                    }
                }
            }
            None
        }
        _ => None,
    })
}

/// Make a natural number literal expression
///
/// REQUIRES: `n` is a non-negative natural number
///
/// ENSURES: returns `Nat.zero` for `n == 0`
/// ENSURES: returns a `Nat.succ` chain of depth `n` for `n > 0`
/// ENSURES: recursive descent runs under `stack_safe`
pub(crate) fn make_nat_literal(n: u64) -> Expr {
    stack_safe(|| {
        if n == 0 {
            Expr::const_(Name::from_string("Nat.zero"), vec![])
        } else {
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                make_nat_literal(n - 1),
            )
        }
    })
}

/// Make a `Fin n` inhabitant using the local `Fin.mk` encoding.
///
/// `Fin.mk : {n} → (val : Nat) → (isLt : Nat.lt val n) → Fin n` requires a
/// genuine proof of `val < n` in the `isLt` slot. `Nat.lt val n` is defeq
/// `Nat.le (val+1) n`, so we build a constructive `Nat.le.refl`/`Nat.le.step`
/// witness (no `sorryAx`). Because `isLt` is proof-irrelevant, the specific
/// witness does not matter for downstream defeq.
///
/// Previously this used `False` as a placeholder — fine for non-dependent splits
/// where the inhabitant is never kernel-checked, but ill-typed in dependent
/// positions (the inhabitant flows into the goal and `add_decl`/`verify_proof`
/// reject `False : Prop` where `Nat.lt val n` is required).
fn make_fin_literal(bound: &Expr, bound_val: u64, value: u64) -> Expr {
    let is_lt = crate::tactic::norm_num_ext::build_nat_le_witness(value + 1, bound_val);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Fin.mk"), vec![]),
                bound.clone(),
            ),
            make_nat_literal(value),
        ),
        is_lt,
    )
}

/// Substitute a free variable with an expression.
///
/// Delegates to the kernel's `Expr::subst_fvar` which uses `ExprFolderOpt`
/// to correctly handle all ExprKind variants (including Cubical, ZFC extensions)
/// with sharing-preserving traversal. Part of #2092.
///
/// REQUIRES: `expr`, `replacement` are well-formed Lean expressions
/// REQUIRES: `fvar` identifies the free variable to replace
///
/// ENSURES: every occurrence of `FVar(fvar)` in `expr` is replaced by
/// `replacement`; all other nodes are structurally preserved
pub(crate) fn substitute_fvar(expr: &Expr, fvar: FVarId, replacement: &Expr) -> Expr {
    expr.subst_fvar(fvar, replacement)
}
