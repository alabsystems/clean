// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced numeric normalization tactic.
//!
//! Normalizes numeric expressions to canonical form for both Nat and Int types.
//! Evaluates ground arithmetic and constructs proof terms showing the
//! normalization is correct.
//!
//! Part of #3082.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;

use super::combinator::try_tactic_preserving_state;
use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::nat_expr_eval::eval_nat_expr;
use super::norm_num_kernel::norm_num_kernel_proof;
use super::proof_term::{reduce_eq, rfl};
// The in-crate `decide` fallback MUST be the kernel-evaluating ladder
// (`decide::eval_decide`, the same function the `decide` token is registered
// to), not the bare SMT bridge. `smt::decide` answers "found counterexample —
// goal is not valid" on TRUE ground goals such as `(2:Nat) ≤ 3`, which
// `eval_decide` proves outright; `eval_decide` still ends in `smt::decide`, so
// this is strictly additive. Do not "simplify" this back to `super::smt::decide`.
use super::decide::eval_decide as decide;

/// Evaluate an Int expression to a concrete `i64` value.
///
/// # Supported heads
///
/// - `Int.ofNat(n)` — non-negative integer from Nat literal
/// - `Int.negSucc(n)` — negative integer `-(n+1)`
/// - `Int.add`, `HAdd.hAdd`, `Add.add` — addition
/// - `Int.mul`, `HMul.hMul`, `Mul.mul` — multiplication
/// - `Int.sub`, `HSub.hSub`, `Sub.sub` — subtraction
/// - `Int.neg`, `HNeg.hNeg`, `Neg.neg` — negation
/// - Nat literals (promoted to Int via implicit coercion)
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `Some(n)` iff `expr` is a ground Int expression evaluable to `n`
/// ENSURES: Returns `None` for symbolic expressions, non-Int types, or overflow
/// ENSURES: All arithmetic is checked to prevent overflow
/// ENSURES: Recursion terminates via `stack_safe` guard
pub(crate) fn eval_int_expr(expr: &Expr) -> Option<i64> {
    stack_safe(|| match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => i64::try_from(n.to_u64()?).ok(),
        ExprKind::Const(name, _) => eval_int_const(&name.to_string()),
        ExprKind::App(f, arg) => eval_int_app(expr, f, arg),
        _ => None,
    })
}

/// Evaluate constant names as Int values.
fn eval_int_const(name: &str) -> Option<i64> {
    match name {
        "Int.zero" | "Nat.zero" => Some(0),
        "Int.one" | "Nat.one" | "1" => Some(1),
        _ => None,
    }
}

/// Evaluate Int application expressions (binary ops, unary ops, spine forms).
fn eval_int_app(expr: &Expr, f: &Expr, arg: &Expr) -> Option<i64> {
    // Try binary direct form: f2 arg1 arg
    if let Some(result) = try_eval_int_binary_direct(f, arg) {
        return Some(result);
    }
    // Try app-spine form: op inst... a b (last two args are operands)
    if let Some(result) = try_eval_int_binary_spine(expr) {
        return Some(result);
    }
    // Unary operations
    if let Some(result) = try_eval_int_unary(f, arg) {
        return Some(result);
    }
    // Nat→Int coercion fallback
    eval_nat_expr(expr).and_then(|v| i64::try_from(v).ok())
}

/// Try evaluating a direct binary application: `(op a) b`.
fn try_eval_int_binary_direct(f: &Expr, arg: &Expr) -> Option<i64> {
    let ExprKind::App(f2, arg1) = f.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = f2.kind() else {
        return None;
    };
    let l = eval_int_expr(arg1)?;
    let r = eval_int_expr(arg)?;
    eval_int_binop(&name.to_string(), l, r)
}

/// Try evaluating an app-spine binary form: `op inst... a b`.
fn try_eval_int_binary_spine(expr: &Expr) -> Option<i64> {
    let all_args = expr.get_app_args();
    if all_args.len() < 2 {
        return None;
    }
    let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    let l = eval_int_expr(all_args[all_args.len() - 2])?;
    let r = eval_int_expr(all_args[all_args.len() - 1])?;
    eval_int_binop(&op_name.to_string(), l, r)
}

/// Apply a binary Int operation by name.
///
/// `Int.div` / `Int.mod` follow Lean 4 core's *T-division* convention
/// (truncation toward zero; remainder sign follows the dividend) and the
/// zero-divisor totalizations `a / 0 = 0`, `a % 0 = a`. These match
/// clean-kernel's native `reduce_int_div` / `reduce_int_mod` reducers
/// byte-for-byte, so a `rfl` close produced after this evaluation stays
/// kernel-checkable. Euclidean `Int.emod` / `Int.ediv` are deliberately
/// *not* handled here: the kernel has no native reducer for them, so a
/// `rfl` close would fail type-checking (same reasoning that excludes
/// `Nat.lcm` from the extended evaluator).
fn eval_int_binop(op: &str, l: i64, r: i64) -> Option<i64> {
    match op {
        "Int.add" | "HAdd.hAdd" | "Add.add" => l.checked_add(r),
        "Int.mul" | "HMul.hMul" | "Mul.mul" => l.checked_mul(r),
        "Int.sub" | "HSub.hSub" | "Sub.sub" => l.checked_sub(r),
        // Int.div: T-division, totalized as `a / 0 = 0`. `checked_div`
        // returns `None` only on the `i64::MIN / -1` overflow, where the
        // kernel reducer also declines, leaving the term symbolic.
        "Int.div" | "HDiv.hDiv" | "Div.div" => {
            if r == 0 {
                Some(0)
            } else {
                l.checked_div(r)
            }
        }
        // Int.mod: T-remainder, totalized as `a % 0 = a`. `checked_rem`
        // returns `None` only on the `i64::MIN % -1` overflow, matching the
        // kernel reducer.
        "Int.mod" | "HMod.hMod" | "Mod.mod" => {
            if r == 0 {
                Some(l)
            } else {
                l.checked_rem(r)
            }
        }
        _ => None,
    }
}

/// Evaluate unary Int operations: ofNat, negSucc, neg, succ.
fn try_eval_int_unary(f: &Expr, arg: &Expr) -> Option<i64> {
    let ExprKind::Const(name, _) = f.kind() else {
        return None;
    };
    match name.to_string().as_str() {
        "Int.ofNat" => i64::try_from(eval_nat_expr(arg)?).ok(),
        "Int.negSucc" => {
            let pos = i64::try_from(eval_nat_expr(arg)?).ok()?;
            pos.checked_add(1).and_then(|v| v.checked_neg())
        }
        "Int.neg" | "HNeg.hNeg" | "Neg.neg" => eval_int_expr(arg)?.checked_neg(),
        "Nat.succ" => {
            let val = eval_nat_expr(arg)?.checked_add(1)?;
            i64::try_from(val).ok()
        }
        _ => None,
    }
}

/// Try to evaluate an Int comparison expression.
///
/// Handles: `Int.lt`, `Int.le`, `LT.lt`, `LE.le`, `GT.gt`, `GE.ge`
/// applied to Int-evaluable arguments.
fn try_eval_int_comparison(expr: &Expr) -> Option<bool> {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }

    if let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() {
        let op_str = op_name.to_string();
        let l = eval_int_expr(args[args.len() - 2])?;
        let r = eval_int_expr(args[args.len() - 1])?;

        if op_str.contains("LT.lt") || op_str.contains("Int.lt") {
            return Some(l < r);
        }
        if op_str.contains("LE.le") || op_str.contains("Int.le") {
            return Some(l <= r);
        }
        if op_str.contains("GT.gt") || op_str.contains("Int.gt") {
            return Some(l > r);
        }
        if op_str.contains("GE.ge") || op_str.contains("Int.ge") {
            return Some(l >= r);
        }
    }

    None
}

/// Try to evaluate a Nat comparison expression.
fn try_eval_nat_comparison(expr: &Expr) -> Option<bool> {
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }

    if let ExprKind::Const(op_name, _) = expr.get_app_fn().kind() {
        let op_str = op_name.to_string();
        let l = eval_nat_expr(args[args.len() - 2])?;
        let r = eval_nat_expr(args[args.len() - 1])?;

        if op_str.contains("LT.lt") || op_str.contains("Nat.lt") {
            return Some(l < r);
        }
        if op_str.contains("LE.le") || op_str.contains("Nat.le") {
            return Some(l <= r);
        }
        // `GT.gt` / `GE.ge` are the typeclass heads; `Nat.gt` / `Nat.ge` are the
        // bare prelude heads (which `decide` / `norm_num` previously left
        // unrecognized, so ground `Nat.ge` / `Nat.gt` goals were dropped).
        if op_str.contains("GT.gt") || op_str.contains("Nat.gt") {
            return Some(l > r);
        }
        if op_str.contains("GE.ge") || op_str.contains("Nat.ge") {
            return Some(l >= r);
        }
    }

    None
}

/// Try to evaluate a comparison expression (both Nat and Int).
pub(crate) fn try_eval_comparison(expr: &Expr) -> Option<bool> {
    try_eval_nat_comparison(expr).or_else(|| try_eval_int_comparison(expr))
}

/// Try to evaluate a proposition to true/false for normalization.
///
/// Checks: `True` constant, Nat/Int comparisons, Nat/Int equalities.
fn try_eval_prop(expr: &Expr) -> bool {
    // Check for True
    if let ExprKind::Const(name, _) = expr.kind() {
        if name == &Name::from_string("True") {
            return true;
        }
    }

    // Check for comparisons (Nat and Int)
    if let Some(result) = try_eval_comparison(expr) {
        return result;
    }

    // Check for equality
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(expr) {
        // Try Nat evaluation first
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            return l == r;
        }
        // Try Int evaluation
        if let (Some(l), Some(r)) = (eval_int_expr(&lhs), eval_int_expr(&rhs)) {
            return l == r;
        }
    }

    false
}

/// Enhanced numeric normalization tactic.
///
/// Evaluates numeric expressions involving natural numbers and integers.
/// Uses computation to prove equalities, comparisons, and decidable
/// propositions involving numbers.
///
/// # Supported operations
///
/// - **Nat**: `+`, `*`, `-` (saturating), `^`, `succ`
/// - **Int**: `+`, `*`, `-`, `neg`, `ofNat`, `negSucc`
/// - **Comparisons**: `<`, `<=`, `>`, `>=` (both Nat and Int)
/// - **Equality**: `=` for ground numeric terms
/// - **Succ forms**: `Nat.succ (Nat.succ 0) = 2`
///
/// # Algorithm
///
/// 1. Check if the goal is a decidable numeric proposition and try `decide`
/// 2. Check if the goal is an equality and evaluate both sides
/// 3. Check for numeric comparisons and evaluate
/// 4. Fall back to `reduce_eq` for computational equality
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed via `decide`, `rfl`, or `reduce_eq`
/// ENSURES: On Err(ArithmeticFailed), evaluation determined the goal is false
/// ENSURES: Evaluation is sound: only closes goals where both sides reduce to same value
pub fn eval_norm_num(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = &goal.target;

    // Try to evaluate the goal as a decidable proposition
    if try_eval_prop(target) {
        if try_tactic_preserving_state(state, decide) {
            return Ok(());
        }
        if try_tactic_preserving_state(state, rfl) {
            return Ok(());
        }
    }

    // Check if goal is an equality and try to normalize both sides.
    // First try the kernel proof path (Part of #3369) which constructs
    // an explicit Eq.refl proof term on the evaluated normal form.
    // This produces kernel-verified proof output rather than relying on
    // the kernel's internal def-eq check via `rfl`.
    if let Ok(proof) = norm_num_kernel_proof(target) {
        let goal_clone = goal.clone();
        if state.close_goal(&goal_clone, proof).is_ok() {
            return Ok(());
        }
        // If close_goal fails (e.g., kernel type check issue), fall through
        // to the existing rfl/decide paths.
    }

    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(target) {
        // Try Nat evaluation
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num".into(),
                reason: format!("Nat: {l} != {r}"),
            });
        }
        // Try Int evaluation
        if let (Some(l), Some(r)) = (eval_int_expr(&lhs), eval_int_expr(&rhs)) {
            if l == r {
                return rfl(state);
            }
            return Err(TacticError::ArithmeticFailed {
                tactic: "norm_num".into(),
                reason: format!("Int: {l} != {r}"),
            });
        }
    }

    // Check for comparisons
    if let Some(result) = try_eval_comparison(target) {
        if result {
            return decide(state);
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "norm_num".to_string(),
            reason: "comparison is false".to_string(),
        });
    }

    // Ground disequality `a ≠ b` (e.g. `(5 : Nat) ≠ 3`): Lean's `norm_num`
    // closes these. Route through the kernel-checkable noConfusion disequality
    // builder. Part of the tactic-divergence parity work.
    if super::decide_eq::match_ne(target).is_some() {
        if super::decide_eq::try_close_ne_by_noconfusion(state).is_ok() {
            return Ok(());
        }
        return Err(TacticError::ArithmeticFailed {
            tactic: "norm_num".to_string(),
            reason: "could not prove disequality".to_string(),
        });
    }

    // Fallback: reduce_eq for computational equality
    reduce_eq(state).map_err(|_| TacticError::ArithmeticFailed {
        tactic: "norm_num".to_string(),
        reason: "could not evaluate numeric goal".to_string(),
    })
}
