// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simple search tactics: exact?, apply?, rw?

use std::collections::HashMap;

use crate::tactic::equality::{match_equality, rewrite};
use crate::tactic::{Goal, ProofState, TacticError};
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

// =============================================================================
// Search Result Types
// =============================================================================

/// Result of a search tactic, containing the suggestion and its proof
#[derive(Debug, Clone)]
pub struct SearchResult {
    /// Name of the constant that was found
    pub name: Name,
    /// The expression to use (instantiated with fresh metavariables for universe params)
    pub expr: Expr,
    /// Human-readable suggestion
    pub suggestion: String,
}

/// Extract the head constant name from an expression (pre-WHNF, syntactic only).
///
/// Peels the App spine to find the outermost function, then returns its
/// constant name if it is a `Const`. Returns `None` for non-constant heads
/// (FVar, Lambda, etc.) — callers must fall back to full def-eq checking.
///
/// **Limitation:** operates on syntactic structure without WHNF reduction.
/// A type alias like `MyAlias := @Eq Nat 0 0` has head `MyAlias`, not `Eq`.
/// The pre-filter may miss constants whose type head is a reducible definition.
/// This is acceptable for search tactics (best-effort suggestions); the full
/// discrimination tree (#2584) will do WHNF-based indexing.
fn head_const_name(expr: &Expr) -> Option<&Name> {
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        Some(name)
    } else {
        None
    }
}

/// Extract the head constant name from the return type of a (possibly Pi) type.
///
/// Peels Pi binders to expose the codomain, then extracts its head constant.
/// Used to pre-filter `apply_search` candidates by return-type head.
fn return_type_head(ty: &Expr) -> Option<&Name> {
    let mut current = ty;
    while let ExprKind::Pi(_, _, codomain) = current.kind() {
        current = codomain;
    }
    head_const_name(current)
}

/// `exact?` - search for a proof term that exactly matches the goal type
///
/// Searches through:
/// 1. Local hypotheses
/// 2. Constants in the environment (filtered by head-symbol index)
///
/// Returns a list of possible proofs.
///
/// # Example
/// ```text
/// -- goal: ∀ x y : Nat, x + y = y + x
/// exact?
/// -- suggests: Nat.add_comm
/// ```
/// REQUIRES: `state` is elaborating the active goal context whose local hypotheses and environment are in sync.
/// ENSURES: Returned list has length at most `max_results`.
/// ENSURES: Each returned expression is definitionally equal to the current goal target in that goal context.
/// ENSURES: Returns `Err(NoGoals)` iff there is no current goal to search.
pub fn exact_search(
    state: &mut ProofState,
    max_results: usize,
) -> Result<Vec<SearchResult>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();
    let local_ctx = goal.local_ctx.clone();

    let mut results = Vec::new();

    // 1. Search local hypotheses
    for decl in &local_ctx {
        // (#2229: use goal's local context so FVars resolve)
        if state.is_def_eq(goal, &decl.ty, &target) {
            results.push(SearchResult {
                name: Name::from_string(&decl.name),
                expr: Expr::fvar(decl.fvar),
                suggestion: format!("exact {}", decl.name),
            });
            if results.len() >= max_results {
                return Ok(results);
            }
        }
    }

    // 2. Search constants in environment, pre-filtered by head symbol.
    // If the target's head is a known constant (e.g. Eq, Nat, Bool), only
    // try constants whose type has the same head — avoids O(N) full def-eq
    // checks against every constant in the environment. Part of #1921 F3.
    let target_head = head_const_name(&target).cloned();

    // Build a head-symbol index: maps head constant name → list of constants.
    // Constants with non-constant heads go into the `None` bucket.
    let constants: Vec<_> = state.env().constants().cloned().collect();
    let mut head_index: HashMap<Option<Name>, Vec<usize>> = HashMap::new();
    for (i, c) in constants.iter().enumerate() {
        let head = head_const_name(&c.type_).cloned();
        head_index.entry(head).or_default().push(i);
    }

    // Candidates: constants matching the target head + constants with unknown heads
    let candidate_indices = match &target_head {
        Some(name) => {
            let mut indices = head_index.remove(&Some(name.clone())).unwrap_or_default();
            indices.extend(head_index.remove(&None).unwrap_or_default());
            indices
        }
        // Target head unknown — must check all constants
        None => (0..constants.len()).collect(),
    };

    for idx in candidate_indices {
        let constant = &constants[idx];
        let levels: Vec<Level> = constant
            .level_params
            .iter()
            .enumerate()
            .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
            .collect();

        let const_type = if levels.is_empty() {
            constant.type_.clone()
        } else {
            let subst: Vec<(Name, Level)> = constant
                .level_params
                .iter()
                .cloned()
                .zip(levels.iter().cloned())
                .collect();
            constant.type_.instantiate_level_params(&subst)
        };

        // (#2229: use goal's local context so FVars resolve)
        if types_unify(state, goal, &const_type, &target) {
            results.push(SearchResult {
                name: constant.name.clone(),
                expr: Expr::const_(constant.name.clone(), levels),
                suggestion: format!("exact {}", constant.name),
            });
            if results.len() >= max_results {
                return Ok(results);
            }
        }
    }

    Ok(results)
}

/// Check if two types can be unified (simple version using is_def_eq)
///
/// Uses the goal's local context so FVars resolve correctly (#2229).
/// REQUIRES: `goal` belongs to the same local context/environment that `state.is_def_eq` expects.
/// ENSURES: Returns exactly the result of `state.is_def_eq(goal, ty1, ty2)`.
pub(crate) fn types_unify(state: &ProofState, goal: &Goal, ty1: &Expr, ty2: &Expr) -> bool {
    state.is_def_eq(goal, ty1, ty2)
}

/// Check if a function type can be applied to produce the target type
/// Returns Some((arg_types, result)) if the function can produce the target
///
/// Uses the goal's local context so FVars resolve correctly (#2229).
/// REQUIRES: `func_type` and `target` are well-formed in `goal`'s local context.
/// REQUIRES: `max_args` bounds how many Pi binders callers are willing to peel.
/// ENSURES: On `Some(args)`, each element of `args` is a Pi-domain encountered before the remaining codomain matches `target`.
/// ENSURES: On `None`, no such match was found within `max_args` Pi binders.
pub(crate) fn can_apply_to_produce(
    state: &ProofState,
    goal: &Goal,
    func_type: &Expr,
    target: &Expr,
    max_args: usize,
) -> Option<Vec<Expr>> {
    let mut current = func_type.clone();
    let mut arg_types = Vec::new();

    for _ in 0..max_args {
        // Check if current type matches target
        if state.is_def_eq(goal, &current, target) {
            return Some(arg_types);
        }

        // If it's a Pi type, we can apply to it
        let whnf = state.whnf(goal, &current);
        if let ExprKind::Pi(_, domain, codomain) = whnf.kind() {
            arg_types.push(domain.as_ref().clone());
            // For dependent types, we'd need to substitute - for now, just continue with codomain
            current = codomain.as_ref().clone();
        } else {
            break;
        }
    }

    // Final check
    if state.is_def_eq(goal, &current, target) {
        Some(arg_types)
    } else {
        None
    }
}

/// `apply?` - search for a lemma that can be applied to make progress on the goal
///
/// Searches through:
/// 1. Local hypotheses (functions that return the target type)
/// 2. Constants in the environment
///
/// Returns a list of possible applications.
///
/// # Example
/// ```text
/// -- goal: P → Q
/// apply?
/// -- suggests: apply h (if h : P → Q exists)
/// ```
/// REQUIRES: `state` is elaborating the active goal context whose local hypotheses and environment are in sync.
/// ENSURES: Returned list has length at most `max_results`.
/// ENSURES: Each returned expression can produce the current goal target after peeling at most 10 Pi-binders.
/// ENSURES: Returns `Err(NoGoals)` iff there is no current goal to search.
pub fn apply_search(
    state: &mut ProofState,
    max_results: usize,
) -> Result<Vec<SearchResult>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();
    let local_ctx = goal.local_ctx.clone();

    let mut results = Vec::new();

    // 1. Search local hypotheses
    for decl in &local_ctx {
        if let Some(args) = can_apply_to_produce(state, goal, &decl.ty, &target, 10) {
            let arg_count = args.len();
            results.push(SearchResult {
                name: Name::from_string(&decl.name),
                expr: Expr::fvar(decl.fvar),
                suggestion: if arg_count == 0 {
                    format!("exact {}", decl.name)
                } else {
                    format!("apply {} ({} args)", decl.name, arg_count)
                },
            });
            if results.len() >= max_results {
                return Ok(results);
            }
        }
    }

    // 2. Search constants in environment, pre-filtered by return-type head.
    // For apply?, we peel Pi binders to find each constant's return type head,
    // then only try constants whose return-type head matches the target's head.
    // Part of #1921 F3.
    let target_head = head_const_name(&target).cloned();

    let constants: Vec<_> = state.env().constants().cloned().collect();
    let mut head_index: HashMap<Option<Name>, Vec<usize>> = HashMap::new();
    for (i, c) in constants.iter().enumerate() {
        let head = return_type_head(&c.type_).cloned();
        head_index.entry(head).or_default().push(i);
    }

    let candidate_indices = match &target_head {
        Some(name) => {
            let mut indices = head_index.remove(&Some(name.clone())).unwrap_or_default();
            indices.extend(head_index.remove(&None).unwrap_or_default());
            indices
        }
        None => (0..constants.len()).collect(),
    };

    for idx in candidate_indices {
        let constant = &constants[idx];
        let levels: Vec<Level> = constant
            .level_params
            .iter()
            .enumerate()
            .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
            .collect();

        let const_type = if levels.is_empty() {
            constant.type_.clone()
        } else {
            let subst: Vec<(Name, Level)> = constant
                .level_params
                .iter()
                .cloned()
                .zip(levels.iter().cloned())
                .collect();
            constant.type_.instantiate_level_params(&subst)
        };

        if let Some(args) = can_apply_to_produce(state, goal, &const_type, &target, 10) {
            let arg_count = args.len();
            results.push(SearchResult {
                name: constant.name.clone(),
                expr: Expr::const_(constant.name.clone(), levels),
                suggestion: if arg_count == 0 {
                    format!("exact {}", constant.name)
                } else {
                    format!("apply {} ({} args)", constant.name, arg_count)
                },
            });
            if results.len() >= max_results {
                return Ok(results);
            }
        }
    }

    Ok(results)
}

/// Return type of the equality head we look for when collecting `rw?` candidates.
///
/// `rw?` (interactive rewrite suggestion) searches for lemmas of the form
/// `lhs = rhs` whose left-hand side rewrites a subterm of the goal. We only
/// auto-apply `Eq`-shaped lemmas because the underlying [`rewrite`] tactic
/// builds its kernel-checked proof term via `Eq.subst` — an `Iff`-shaped lemma
/// would need a `propext`/`Iff.mpr` bridge that `rewrite` does not construct.
/// `Iff` lemmas are therefore reported as suggestions (so the user can convert
/// them) but never silently applied through a path `rewrite` cannot verify.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RewriteHead {
    /// `@Eq α lhs rhs` — directly rewritable via `rewrite`.
    Eq,
    /// `Iff p q` — suggested only, not auto-applied (see [`RewriteHead`]).
    Iff,
}

/// Peel leading Pi binders of `ty` and classify the codomain as an `Eq`/`Iff`
/// rewrite head.
///
/// Returns `Some(RewriteHead::Eq)` for an `@Eq α a b` codomain,
/// `Some(RewriteHead::Iff)` for an `Iff p q` codomain, and `None` otherwise.
/// This is only a cheap structural pre-filter that selects which constants/
/// hypotheses are worth a trial rewrite — the actual matching and proof term
/// are re-derived through [`rewrite`].
fn classify_rewrite_head(ty: &Expr) -> Option<RewriteHead> {
    let mut codomain = ty;
    while let ExprKind::Pi(_, _, body) = codomain.kind() {
        codomain = body;
    }
    if match_equality(codomain).is_ok() {
        return Some(RewriteHead::Eq);
    }
    let head = codomain.get_app_fn();
    let args = codomain.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Iff") && args.len() == 2 {
            return Some(RewriteHead::Iff);
        }
    }
    None
}

/// Does `expr` contain an unassigned metavariable (a meta-tagged `FVar`)?
///
/// Used to reject `rw?` candidates whose rewrite leaves unsolved metavariables
/// in the goal (see [`trial_rewrite_changes_goal`]). The input should already be
/// `MetaState::instantiate`d so that *assigned* metas are substituted away and
/// only genuinely-unsolved ones remain visible.
fn contains_meta_fvar(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => contains_meta_fvar(f) || contains_meta_fvar(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_meta_fvar(ty) || contains_meta_fvar(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_meta_fvar(ty) || contains_meta_fvar(val) || contains_meta_fvar(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            contains_meta_fvar(inner)
        }
        _ => false,
    }
}

/// Attempt a forward `rewrite` with `name` in a rolled-back scope and report
/// whether it would succeed, *actually change the goal*, and leave no unsolved
/// metavariables behind.
///
/// This is the faithfulness anchor for `rw?`: instead of re-implementing the
/// keyed equality-unification used by [`rewrite`], we run the real tactic on a
/// cloned goal stack inside a metavariable scope and discard every effect. A
/// candidate is reported by `rewrite_search` only if this trial succeeds, so a
/// suggested (and the auto-applied top) rewrite is guaranteed to go through the
/// identical kernel-checked `Eq.subst` proof term as an explicit `rw [name]`.
///
/// Two extra conditions match the spirit of Lean's `rw?` (surface rewrites that
/// make *useful* progress) and keep the auto-applied top hit well-formed:
///
/// 1. The rewritten target must *differ* from the original — a real environment
///    carries reflexivity-style lemmas (`Eq.refl ?a : ?a = ?a`) that rewrite a
///    subterm to itself.
/// 2. The rewritten target must contain no unsolved metavariables — congruence
///    and symmetry lemmas (`congrArg`, `Eq.symm`, `Eq.trans`, …) have a
///    metavariable left-hand side that unifies with any subterm but rewrites it
///    to a *fresh metavariable*, producing an under-determined goal that is not
///    a useful suggestion (and which an explicit `rw [name]` would leave with
///    open metavariable goals).
fn trial_rewrite_changes_goal(state: &mut ProofState, name: &str) -> bool {
    let saved_goals = state.goals.clone();
    let original_target = state.current_goal().map(|g| g.target.clone());
    let original_target = original_target.map(|t| state.metas.instantiate(&t));
    state.metas_mut().push_scope();
    let useful = match (rewrite(state, name, false), &original_target) {
        (Ok(()), Some(before)) => {
            let after = state.current_goal().map(|g| g.target.clone());
            match after {
                Some(t) => {
                    let resolved = state.metas.instantiate(&t);
                    &resolved != before && !contains_meta_fvar(&resolved)
                }
                None => false,
            }
        }
        _ => false,
    };
    // Always roll back: search must not mutate the live proof state.
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    state.metas_mut().pop_scope();
    useful
}

/// `rw?` — search for equality (or iff) lemmas whose left-hand side rewrites a
/// subterm of the goal.
///
/// Searches, in order:
/// 1. Local hypotheses whose type is `a = b` (or `a ↔ b`).
/// 2. Environment constants whose (possibly quantified) conclusion is `a = b`
///    (or `a ↔ b`), pre-filtered to equality/iff heads.
///
/// Each `Eq`-shaped candidate is confirmed by [`trial_rewrite_changes_goal`], which
/// runs the real [`rewrite`] tactic in a rolled-back scope, so every returned
/// `Eq` result is genuinely applicable and shares `rewrite`'s kernel-checked
/// proof path. `Iff`-shaped candidates are reported (with an `-- iff:` marker)
/// but not trial-applied, since [`rewrite`] only constructs `Eq.subst` proofs.
/// Local hypotheses are reported before environment constants, matching `rw`'s
/// shadowing resolution order.
///
/// REQUIRES: `state` is elaborating the active goal context whose local
///   hypotheses and environment are in sync.
/// ENSURES: Returned list has length at most `max_results`.
/// ENSURES: Every returned `Eq`-headed result's `name` is accepted by a forward
///   `rewrite` on the current goal.
/// ENSURES: Returns `Err(NoGoals)` iff there is no current goal to search.
pub fn rewrite_search(
    state: &mut ProofState,
    max_results: usize,
) -> Result<Vec<SearchResult>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let local_ctx = goal.local_ctx.clone();

    let mut results = Vec::new();

    // 1. Local hypotheses (shadow environment constants of the same name, like `rw`).
    for decl in &local_ctx {
        let Some(head) = classify_rewrite_head(&decl.ty) else {
            continue;
        };
        match head {
            RewriteHead::Eq => {
                if trial_rewrite_changes_goal(state, &decl.name) {
                    results.push(SearchResult {
                        name: Name::from_string(&decl.name),
                        expr: Expr::fvar(decl.fvar),
                        suggestion: format!("rw [{}]", decl.name),
                    });
                    if results.len() >= max_results {
                        return Ok(results);
                    }
                }
            }
            RewriteHead::Iff => {
                results.push(SearchResult {
                    name: Name::from_string(&decl.name),
                    expr: Expr::fvar(decl.fvar),
                    suggestion: format!("-- iff: rw [{}]", decl.name),
                });
                if results.len() >= max_results {
                    return Ok(results);
                }
            }
        }
    }

    // 2. Environment constants, pre-filtered to equality/iff conclusions.
    // Snapshot names of local hypotheses so an env constant shadowed by a local
    // of the same name is not double-reported (and resolves to the local in `rw`).
    let local_names: Vec<String> = local_ctx.iter().map(|d| d.name.clone()).collect();

    let constants: Vec<_> = state.env().constants().cloned().collect();
    for constant in &constants {
        let name_str = constant.name.to_string();
        // Skip internal/auto-generated names, matching library_search's filter.
        if name_str.starts_with('_') || name_str.contains("._") {
            continue;
        }
        if local_names.iter().any(|n| n == &name_str) {
            continue;
        }
        let Some(head) = classify_rewrite_head(&constant.type_) else {
            continue;
        };
        let levels: Vec<Level> = constant
            .level_params
            .iter()
            .enumerate()
            .map(|(i, _)| Level::param(Name::from_string(&format!("_u{i}"))))
            .collect();
        match head {
            RewriteHead::Eq => {
                if trial_rewrite_changes_goal(state, &name_str) {
                    results.push(SearchResult {
                        name: constant.name.clone(),
                        expr: Expr::const_(constant.name.clone(), levels),
                        suggestion: format!("rw [{}]", constant.name),
                    });
                    if results.len() >= max_results {
                        return Ok(results);
                    }
                }
            }
            RewriteHead::Iff => {
                results.push(SearchResult {
                    name: constant.name.clone(),
                    expr: Expr::const_(constant.name.clone(), levels),
                    suggestion: format!("-- iff: rw [{}]", constant.name),
                });
                if results.len() >= max_results {
                    return Ok(results);
                }
            }
        }
    }

    Ok(results)
}
