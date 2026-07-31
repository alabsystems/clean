// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evaluator for compiled match decision trees.
//!
//! Given a `DecisionTree` produced by `compile_match`, evaluates it against
//! a runtime environment to find the matching arm index. The environment
//! maps variable names to `MatchValue`s that carry constructor tags and
//! field bindings.
//!
//! Part of #3084 - Match expression compilation for native execution.

use crate::match_compile::{ConstructorTag, DecisionTree, Var};
use clean_kernel::{BigNat, Expr, ExprKind, Literal, Name};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Runtime values
// ---------------------------------------------------------------------------

/// A runtime value for match evaluation.
///
/// Represents either a constructor application (with fields) or a leaf value
/// (variable or literal). During evaluation, the Switch node inspects the
/// constructor tag and binds field values for sub-tree evaluation.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum MatchValue {
    /// A constructor application: tag + field values.
    Constructor(ConstructorTag, Vec<MatchValue>),
    /// An opaque leaf value (not destructurable further).
    Leaf,
}

impl MatchValue {
    /// Get the constructor tag, if this is a constructor value.
    #[must_use]
    pub fn ctor_tag(&self) -> Option<&ConstructorTag> {
        match self {
            Self::Constructor(tag, _) => Some(tag),
            Self::Leaf => None,
        }
    }

    /// Get the field values, if this is a constructor value.
    #[must_use]
    pub fn fields(&self) -> Option<&[MatchValue]> {
        match self {
            Self::Constructor(_, fields) => Some(fields),
            Self::Leaf => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors during decision tree evaluation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum MatchError {
    /// No arm matched the input (non-exhaustive pattern).
    #[error("non-exhaustive match: no arm matched")]
    NonExhaustive,

    /// A guard expression could not be evaluated.
    #[error("guard evaluation failed")]
    GuardFailed,

    /// A scrutinee variable was not found in the environment.
    #[error("unbound scrutinee variable: {0}")]
    UnboundVariable(Name),
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// A simple name-value binding environment for match evaluation.
#[derive(Debug, Clone)]
pub struct MatchEnv {
    bindings: Vec<(Name, MatchValue)>,
}

impl MatchEnv {
    /// Create a new environment from a slice of bindings.
    #[must_use]
    pub fn new(bindings: &[(Name, MatchValue)]) -> Self {
        Self {
            bindings: bindings.to_vec(),
        }
    }

    /// Look up a variable by name.
    #[must_use]
    pub fn lookup(&self, name: &Name) -> Option<&MatchValue> {
        // Search from the end to support shadowing
        self.bindings
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v)
    }

    /// Extend the environment with new bindings, returning a new env.
    #[must_use]
    pub fn extend(&self, new_bindings: &[(Name, MatchValue)]) -> Self {
        let mut bindings = self.bindings.clone();
        bindings.extend_from_slice(new_bindings);
        Self { bindings }
    }
}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

/// Evaluate a decision tree to find the matching arm index.
///
/// Returns the `body_idx` of the first matching arm, or a `MatchError`
/// if no arm matches (non-exhaustive).
///
/// Guard nodes are handled by [`try_eval_guard_const`]: a guard that
/// provably reduces to `true` selects its arm, a guard that provably
/// reduces to `false` falls through to the next arm, and a guard that
/// cannot be statically resolved is treated conservatively as a
/// fall-through (the arm is not selected). Use
/// [`eval_decision_tree_with_guards`] to supply a richer guard evaluator.
///
/// # Arguments
///
/// * `tree` - The compiled decision tree
/// * `env` - Variable bindings mapping scrutinee names to runtime values
pub fn eval_decision_tree(tree: &DecisionTree, env: &MatchEnv) -> Result<usize, MatchError> {
    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx == usize::MAX {
                Err(MatchError::NonExhaustive)
            } else {
                Ok(*idx)
            }
        }

        DecisionTree::Switch(scrutinee, branches, default) => {
            let val = env
                .lookup(&scrutinee.name)
                .ok_or_else(|| MatchError::UnboundVariable(scrutinee.name.clone()))?;

            // Try to match the scrutinee against each branch
            if let Some(tag) = val.ctor_tag() {
                for (branch_tag, subtree) in branches {
                    if branch_tag.name == tag.name {
                        // Match: bind field variables
                        let field_vars = fresh_field_names(branch_tag, scrutinee);
                        let fields = val.fields().unwrap_or(&[]);

                        let new_bindings: Vec<(Name, MatchValue)> =
                            field_vars.into_iter().zip(fields.iter().cloned()).collect();

                        let new_env = env.extend(&new_bindings);
                        return eval_decision_tree(subtree, &new_env);
                    }
                }
            }

            // No constructor matched: try default
            match default {
                Some(default_tree) => eval_decision_tree(default_tree, env),
                None => Err(MatchError::NonExhaustive),
            }
        }

        DecisionTree::Guard(guard_expr, success, failure) => {
            // Conservatively const-evaluate the guard against the current
            // bindings. If the guard provably reduces to `true` we take the
            // success branch; if it provably reduces to `false` we take the
            // failure branch. When the guard cannot be statically resolved
            // (`None`), we preserve the historical conservative behavior and
            // fall through to the failure branch rather than guessing — the
            // arm is *not* selected on an unknown guard, matching the prior
            // placeholder semantics so callers never see a wrongly-taken arm.
            match try_eval_guard_const(guard_expr) {
                Some(true) => eval_decision_tree(success, env),
                Some(false) | None => eval_decision_tree(failure, env),
            }
        }
    }
}

/// Evaluate a decision tree with a provided guard evaluator.
///
/// The `eval_guard` function is called for Guard nodes and should return
/// `Ok(true)` if the guard passes, `Ok(false)` if it fails, or
/// `Err(MatchError)` on error.
pub fn eval_decision_tree_with_guards<F>(
    tree: &DecisionTree,
    env: &MatchEnv,
    eval_guard: &F,
) -> Result<usize, MatchError>
where
    F: Fn(&Expr, &MatchEnv) -> Result<bool, MatchError>,
{
    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx == usize::MAX {
                Err(MatchError::NonExhaustive)
            } else {
                Ok(*idx)
            }
        }

        DecisionTree::Switch(scrutinee, branches, default) => {
            let val = env
                .lookup(&scrutinee.name)
                .ok_or_else(|| MatchError::UnboundVariable(scrutinee.name.clone()))?;

            if let Some(tag) = val.ctor_tag() {
                for (branch_tag, subtree) in branches {
                    if branch_tag.name == tag.name {
                        let field_vars = fresh_field_names(branch_tag, scrutinee);
                        let fields = val.fields().unwrap_or(&[]);

                        let new_bindings: Vec<(Name, MatchValue)> =
                            field_vars.into_iter().zip(fields.iter().cloned()).collect();

                        let new_env = env.extend(&new_bindings);
                        return eval_decision_tree_with_guards(subtree, &new_env, eval_guard);
                    }
                }
            }

            match default {
                Some(default_tree) => eval_decision_tree_with_guards(default_tree, env, eval_guard),
                None => Err(MatchError::NonExhaustive),
            }
        }

        DecisionTree::Guard(guard_expr, success, failure) => match eval_guard(guard_expr, env)? {
            true => eval_decision_tree_with_guards(success, env, eval_guard),
            false => eval_decision_tree_with_guards(failure, env, eval_guard),
        },
    }
}

// ---------------------------------------------------------------------------
// Built-in conservative guard evaluation
// ---------------------------------------------------------------------------

/// Conservatively const-evaluate a match-guard expression to a boolean.
///
/// Match guards are stored as kernel [`Expr`]s. There is no full reduction
/// engine available at this layer, so we deliberately recognize only a small,
/// well-defined set of guard shapes whose value is unambiguous:
///
/// * the canonical boolean constructors `Bool.true` / `Bool.false` (and their
///   `true` / `false` aliases) and the propositional `True` / `False`;
/// * `Bool.not` / `not` applied to a recognizable boolean;
/// * `Bool.and` / `and` and `Bool.or` / `or` applied to two recognizable
///   booleans (note: evaluated strictly — both operands must be resolvable);
/// * `Decidable.decide` / `decide` wrapping a recognizable boolean;
/// * the boolean `Nat` comparisons `Nat.beq` / `Nat.ble` / `Nat.blt` applied
///   to two natural-number literals.
///
/// Returns `Some(true)` / `Some(false)` only when the guard provably reduces
/// to that value. Any guard that mentions runtime bindings, calls an unknown
/// function, or otherwise cannot be statically resolved returns `None`. This
/// is the **sound, conservative** contract: callers must treat `None` as
/// "unknown" and never select an arm on the strength of an unresolved guard.
///
/// Only closed constant expressions are resolved; guards that reference
/// pattern bindings or other free variables stay unknown (`None`).
#[must_use]
pub fn try_eval_guard_const(guard: &Expr) -> Option<bool> {
    let guard = guard.strip_mdata();

    // Bare constants: Bool.true / true / True, Bool.false / false / False.
    if let ExprKind::Const(name, _) = guard.kind() {
        return const_name_to_bool(&name.to_string());
    }

    // Application spines: head constant applied to argument expressions.
    if guard.is_app() {
        let head = guard.get_app_fn();
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };
        let head_name = name.to_string();
        let args = guard.get_app_args();

        return match head_name.as_str() {
            "Bool.not" | "not" if args.len() == 1 => try_eval_guard_const(args[0]).map(|b| !b),
            "Bool.and" | "and" if args.len() == 2 => {
                let a = try_eval_guard_const(args[0])?;
                let b = try_eval_guard_const(args[1])?;
                Some(a && b)
            }
            "Bool.or" | "or" if args.len() == 2 => {
                let a = try_eval_guard_const(args[0])?;
                let b = try_eval_guard_const(args[1])?;
                Some(a || b)
            }
            // `decide`/`Decidable.decide` is applied as `decide (p) (inst)` or
            // `decide (inst)`; the recognizable boolean is whichever argument
            // already reduces, so probe each conservatively.
            "Decidable.decide" | "decide" => args.iter().find_map(|arg| try_eval_guard_const(arg)),
            "Nat.beq" if args.len() == 2 => {
                let (a, b) = (nat_lit(args[0])?, nat_lit(args[1])?);
                Some(a == b)
            }
            "Nat.ble" if args.len() == 2 => {
                let (a, b) = (nat_lit(args[0])?, nat_lit(args[1])?);
                Some(a <= b)
            }
            "Nat.blt" if args.len() == 2 => {
                let (a, b) = (nat_lit(args[0])?, nat_lit(args[1])?);
                Some(a < b)
            }
            _ => None,
        };
    }

    None
}

/// Map a constant name to a boolean, if it is a recognized boolean literal.
fn const_name_to_bool(name: &str) -> Option<bool> {
    match name {
        "Bool.true" | "true" | "True" => Some(true),
        "Bool.false" | "false" | "False" => Some(false),
        _ => None,
    }
}

/// Extract a natural-number literal from an expression, stripping metadata.
fn nat_lit(expr: &Expr) -> Option<&BigNat> {
    match expr.strip_mdata().kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

/// Generate fresh field variable names matching the convention in `compile_match`.
fn fresh_field_names(tag: &ConstructorTag, parent: &Var) -> Vec<Name> {
    (0..tag.arity)
        .map(|i| {
            parent
                .name
                .clone()
                .str(format!("_{}", tag.name))
                .str(format!("f{i}"))
        })
        .collect()
}
