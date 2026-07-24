// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced `#eval` command implementation.
//!
//! Provides richer evaluation of expressions with support for:
//! - IO-typed expressions routed through the IO bridge
//! - Ground term reduction via WHNF + native reducers
//! - Direct display of Nat/Int/String/Bool/List/Array literals
//! - Fallback pretty-printing of reduced expressions
//!
//! This module builds on the basic `elab_eval` in `commands.rs` with
//! structured result types and smarter display logic.

use crate::error::ElabError;
use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};

/// Categorized evaluation result from `#eval`.
///
/// Each variant captures a different output mode so callers can format
/// or route the result appropriately (e.g., IO output vs pure values).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum EvalResult {
    /// A successfully reduced pure value.
    Value(String),
    /// An IO expression that was executed; contains captured output.
    Io(String),
    /// The expression was a type (Sort/Pi) — displayed as-is.
    Type(String),
    /// An error occurred during evaluation.
    Error(String),
}

impl std::fmt::Display for EvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(v) | Self::Io(v) | Self::Type(v) | Self::Error(v) => write!(f, "{v}"),
        }
    }
}

/// Evaluate an already-elaborated kernel expression.
///
/// This is the enhanced entry point for `#eval`. It:
/// 1. Type-checks the expression to validate it
/// 2. Checks for IO type and routes through the IO bridge
/// 3. Reduces to WHNF
/// 4. Attempts to extract a literal display form
/// 5. Falls back to pretty-printing the reduced expression
///
/// # Errors
///
/// Returns [`ElabError`] if type inference fails.
pub fn eval_expression(expr: &Expr, env: &Environment) -> Result<EvalResult, ElabError> {
    let tc = TypeChecker::new(env);

    // Validate expression is well-typed.
    let ty = tc
        .infer_type(expr)
        .map_err(|e| ElabError::KernelCheckFailed {
            name: Name::anon(),
            detail: e.to_string(),
        })?;

    // Route IO-typed expressions through the IO bridge.
    if crate::io_bridge::is_io_typed(env, expr) {
        let reduced = tc.whnf(expr);
        let io_result = crate::io_bridge::eval_io_expr(&reduced)?;
        return Ok(EvalResult::Io(format!("{io_result}")));
    }

    // Reduce to WHNF.
    let reduced = tc.whnf(expr);

    // Check if the result is a type (Sort).
    if is_type_expr(&reduced) {
        return Ok(EvalResult::Type(format_with_type_annotation(&reduced, &ty)));
    }

    // Try to extract a literal display form.
    if let Some(display) = try_display_literal(&reduced) {
        return Ok(EvalResult::Value(display));
    }

    // Try to display constructor-based values (List, Option, etc.).
    if let Some(display) = try_display_constructor(&reduced) {
        return Ok(EvalResult::Value(display));
    }

    // Fallback: pretty-print the reduced expression with type annotation.
    Ok(EvalResult::Value(format_with_type_annotation(
        &reduced, &ty,
    )))
}

/// Check if the expression is a type (Sort, Pi, or similar).
fn is_type_expr(expr: &Expr) -> bool {
    matches!(expr.kind(), ExprKind::Sort(_))
}

/// Format an expression with its type annotation.
fn format_with_type_annotation(expr: &Expr, ty: &Expr) -> String {
    format!("{expr} : {ty}")
}

/// Try to extract a human-readable display from a literal expression.
///
/// Handles Nat, String, and direct literal extraction.
pub(crate) fn try_display_literal(expr: &Expr) -> Option<String> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n.to_string()),
        ExprKind::Lit(Literal::String(s)) => Some(format!("\"{s}\"")),
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            match name_str.as_str() {
                "Bool.true" | "True" => Some("true".to_owned()),
                "Bool.false" | "False" => Some("false".to_owned()),
                "Unit.unit" | "Unit.mk" | "PUnit.unit" => Some("()".to_owned()),
                "Nat.zero" => Some("0".to_owned()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Try to display constructor-based composite values.
///
/// Recognizes patterns like `Nat.succ (Nat.succ Nat.zero)` and
/// displays them as natural numbers, and similar for List/Option.
pub(crate) fn try_display_constructor(expr: &Expr) -> Option<String> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        let name_str = name.to_string();
        match name_str.as_str() {
            "Nat.succ" if args.len() == 1 => {
                // Recursively count successors.
                try_extract_nat(expr).map(|n| n.to_string())
            }
            "List.nil" => Some("[]".to_owned()),
            "List.cons" if args.len() >= 3 => {
                // List.cons {α} head tail
                let mut elements = Vec::new();
                let mut current = expr;
                loop {
                    let h = current.get_app_fn();
                    let a = current.get_app_args();
                    if let ExprKind::Const(n, _) = h.kind() {
                        let ns = n.to_string();
                        if ns == "List.cons" && a.len() >= 3 {
                            let elem_display = try_display_literal(a[1])
                                .or_else(|| try_display_constructor(a[1]))
                                .unwrap_or_else(|| format!("{}", a[1]));
                            elements.push(elem_display);
                            current = a[2];
                            continue;
                        } else if ns == "List.nil" {
                            break;
                        }
                    }
                    // Non-standard tail — show raw.
                    elements.push(format!("{current}"));
                    break;
                }
                Some(format!("[{}]", elements.join(", ")))
            }
            "Option.none" => Some("none".to_owned()),
            "Option.some" if args.len() >= 2 => {
                let inner = try_display_literal(args[1])
                    .or_else(|| try_display_constructor(args[1]))
                    .unwrap_or_else(|| format!("{}", args[1]));
                Some(format!("some {inner}"))
            }
            // Array.mk wraps a List of elements: `#[e1, e2]` displays as
            // `[e1, e2]` mirroring the List unrolling. The constructor is
            // `Array.mk {α} (toList : List α)`, so the trailing argument is
            // the backing list. If elaboration left the elements as direct
            // positional arguments (no intervening List), fall back to
            // formatting those arguments directly.
            "Array.mk" if !args.is_empty() => {
                let backing = args[args.len() - 1];
                if let Some(list_display) = try_display_constructor(backing) {
                    // Reuse the List rendering (already bracketed).
                    if list_display.starts_with('[') {
                        return Some(list_display);
                    }
                }
                // Elements supplied directly (surface `#[..]` not yet folded
                // into a List): skip the implicit type argument when present.
                let elem_start = usize::from(args.len() > 1 && is_type_like(args[0]));
                let elements: Vec<String> = args[elem_start..]
                    .iter()
                    .map(|e| {
                        try_display_literal(e)
                            .or_else(|| try_display_constructor(e))
                            .unwrap_or_else(|| format!("{e}"))
                    })
                    .collect();
                Some(format!("[{}]", elements.join(", ")))
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Heuristic: does this argument look like an implicit type argument?
///
/// Used by the `Array.mk` direct-positional fallback to drop a leading
/// element type (e.g. the `{α}` in `Array.mk Nat 1 2`). Conservative: only
/// `Sort` expressions and the small set of common element-type constants
/// (`Nat`, `Int`, `Bool`, `String`, `Char`, `Float`) count as type-like, so
/// genuine value elements are never silently dropped.
fn is_type_like(expr: &Expr) -> bool {
    match expr.get_app_fn().kind() {
        ExprKind::Sort(_) => true,
        ExprKind::Const(name, _) => matches!(
            name.to_string().as_str(),
            "Nat" | "Int" | "Bool" | "String" | "Char" | "Float"
        ),
        _ => false,
    }
}

/// Try to extract a natural number from a Nat expression (zero/succ form).
fn try_extract_nat(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(0),
        _ => {
            let head = expr.get_app_fn();
            let args = expr.get_app_args();
            if let ExprKind::Const(name, _) = head.kind() {
                if name.to_string() == "Nat.succ" && args.len() == 1 {
                    try_extract_nat(args[0]).map(|n| n + 1)
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
#[path = "eval_cmd_tests.rs"]
mod tests;
