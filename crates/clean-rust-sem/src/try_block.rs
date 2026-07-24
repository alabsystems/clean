// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Try block desugaring (RFC 2388).
//!
//! Rust's `try` blocks (`try { ... }`) evaluate a block where the `?` operator
//! short-circuits to the block boundary instead of the enclosing function.
//! The block produces a `Result<T, E>` (or `Option<T>`) value.
//!
//! This module provides:
//! - [`TryBlock`]: AST node representing a `try { body }` expression
//! - [`QuestionMarkOp`]: AST node for the `?` operator within try contexts
//! - [`desugar_try_block`]: Lowers a try block to a match + label-break pattern
//! - [`desugar_question_mark`]: Lowers `?` to a match on `Ok`/`Err` or `Some`/`None`
//!
//! ## Desugaring Strategy
//!
//! A `try` block desugars to a labeled block with break-on-error:
//!
//! ```text
//! try { body }
//! =>
//! 'try_label: {
//!     Result::Ok({
//!         // body, where `expr?` becomes:
//!         match expr {
//!             Result::Ok(val) => val,
//!             Result::Err(e) => break 'try_label Result::Err(e),
//!         }
//!     })
//! }
//! ```
//!
//! This differs from function-level `?` which uses `return` instead of `break`.

use crate::expr::{EnumPatternPayload, EnumVariantPayload, Expr, MatchArm, Pattern};

/// Counter for generating unique try-block labels.
///
/// Each try block gets a unique label so nested try blocks break to
/// the correct scope boundary.
static TRY_LABEL_COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Generate a fresh label name for a try block scope.
fn fresh_try_label() -> String {
    let id = TRY_LABEL_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("__try_{id}")
}

/// AST representation of a `try { body }` block (RFC 2388).
///
/// The body expression is evaluated in a context where `?` breaks to
/// the try block boundary instead of returning from the function.
#[derive(Debug, Clone)]
pub struct TryBlock {
    /// The body expression executed inside the try block.
    pub body: Expr,
    /// The expected result type wrapping the body's value.
    /// When `None`, defaults to `Result<T, E>` semantics.
    pub result_type: TryResultType,
}

/// Which carrier type the try block produces.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TryResultType {
    /// `try { body } : Result<T, E>` — the default.
    Result,
    /// `try { body } : Option<T>` — for option-returning contexts.
    Option,
}

/// AST representation of the `?` (question mark) operator.
///
/// `expr?` desugars differently depending on whether it appears inside
/// a try block (break to label) or at function level (return).
#[derive(Debug, Clone)]
pub struct QuestionMarkOp {
    /// The expression being questioned (must evaluate to Result or Option).
    pub expr: Expr,
    /// When `Some`, `?` breaks to this try-block label on error.
    /// When `None`, `?` returns from the enclosing function.
    pub try_label: Option<String>,
}

/// Desugar a [`TryBlock`] into a labeled loop + break pattern.
///
/// ```text
/// try { body }
/// =>
/// loop {
///     break '__try_N Result::Ok({ body });
/// }
/// ```
///
/// The `?` operators inside `body` must already be desugared with
/// [`desugar_question_mark`] using the same label, so errors break
/// to this loop boundary.
///
/// We use `Loop` + immediate `Break` because the crate's `Expr` enum
/// supports labeled loops with break values, giving us the labeled-block
/// semantics needed for try blocks.
#[must_use]
pub fn desugar_try_block(try_block: &TryBlock) -> Expr {
    let label = fresh_try_label();
    let body_with_desugared_questions = desugar_questions_in_expr(&try_block.body, &label);

    let ok_wrapped = match &try_block.result_type {
        TryResultType::Result => wrap_in_result_ok(body_with_desugared_questions),
        TryResultType::Option => wrap_in_option_some(body_with_desugared_questions),
    };

    // Labeled loop that immediately breaks with the wrapped success value.
    // Inner `?` operators break to this label with the error value.
    Expr::Loop {
        label: Some(label.clone()),
        body: Box::new(Expr::Break {
            label: Some(label),
            value: Some(Box::new(ok_wrapped)),
        }),
    }
}

/// Desugar a [`QuestionMarkOp`] into a match expression.
///
/// For function-level `?` (no try label):
/// ```text
/// expr? => match expr {
///     Result::Ok(val) => val,
///     Result::Err(e) => return Result::Err(e),
///     Option::Some(val) => val,
///     Option::None => return Option::None,
/// }
/// ```
///
/// For try-block `?` (with label):
/// ```text
/// expr? => match expr {
///     Result::Ok(val) => val,
///     Result::Err(e) => break 'label Result::Err(e),
///     Option::Some(val) => val,
///     Option::None => break 'label Option::None,
/// }
/// ```
#[must_use]
pub fn desugar_question_mark(qm: &QuestionMarkOp) -> Expr {
    let val = "__qm_val".to_string();
    let err = "__qm_err".to_string();
    let mut arms = result_qm_arms(&val, &err, &qm.try_label);
    arms.extend(option_qm_arms(&val, &qm.try_label));
    Expr::Match {
        scrutinee: Box::new(qm.expr.clone()),
        arms,
    }
}

fn qm_binding(name: &str) -> Pattern {
    Pattern::Binding {
        name: name.to_string(),
        mutable: false,
        subpattern: None,
    }
}

fn qm_var(name: &str) -> Expr {
    Expr::Var {
        name: name.to_string(),
        local_idx: 0,
    }
}

fn qm_exit(wrapped: Expr, label: &Option<String>) -> Expr {
    match label {
        Some(lbl) => Expr::Break {
            label: Some(lbl.clone()),
            value: Some(Box::new(wrapped)),
        },
        None => Expr::Return(Some(Box::new(wrapped))),
    }
}

fn result_qm_arms(val: &str, err: &str, label: &Option<String>) -> Vec<MatchArm> {
    vec![
        MatchArm {
            pattern: Pattern::EnumVariant {
                enum_name: "Result".to_string(),
                variant: "Ok".to_string(),
                payload: EnumPatternPayload::Tuple(vec![qm_binding(val)]),
            },
            guard: None,
            body: qm_var(val),
        },
        MatchArm {
            pattern: Pattern::EnumVariant {
                enum_name: "Result".to_string(),
                variant: "Err".to_string(),
                payload: EnumPatternPayload::Tuple(vec![qm_binding(err)]),
            },
            guard: None,
            body: qm_exit(
                Expr::EnumVariant {
                    enum_name: "Result".to_string(),
                    variant: "Err".to_string(),
                    payload: EnumVariantPayload::Tuple(vec![qm_var(err)]),
                    type_args: vec![],
                    const_args: vec![],
                },
                label,
            ),
        },
    ]
}

fn option_qm_arms(val: &str, label: &Option<String>) -> Vec<MatchArm> {
    vec![
        MatchArm {
            pattern: Pattern::EnumVariant {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: EnumPatternPayload::Tuple(vec![qm_binding(val)]),
            },
            guard: None,
            body: qm_var(val),
        },
        MatchArm {
            pattern: Pattern::EnumVariant {
                enum_name: "Option".to_string(),
                variant: "None".to_string(),
                payload: EnumPatternPayload::Unit,
            },
            guard: None,
            body: qm_exit(
                Expr::EnumVariant {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: EnumVariantPayload::Unit,
                    type_args: vec![],
                    const_args: vec![],
                },
                label,
            ),
        },
    ]
}

/// Wrap an expression in `Result::Ok(expr)`.
fn wrap_in_result_ok(expr: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: EnumVariantPayload::Tuple(vec![expr]),
        type_args: vec![],
        const_args: vec![],
    }
}

/// Wrap an expression in `Option::Some(expr)`.
fn wrap_in_option_some(expr: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: EnumVariantPayload::Tuple(vec![expr]),
        type_args: vec![],
        const_args: vec![],
    }
}

/// Wrap an expression in `Result::Err(expr)`.
#[cfg(test)]
fn wrap_in_result_err(expr: Expr) -> Expr {
    Expr::EnumVariant {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: EnumVariantPayload::Tuple(vec![expr]),
        type_args: vec![],
        const_args: vec![],
    }
}

/// Wrap an expression in `Option::None`.
#[cfg(test)]
fn wrap_in_option_none() -> Expr {
    Expr::EnumVariant {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: EnumVariantPayload::Unit,
        type_args: vec![],
        const_args: vec![],
    }
}

/// Recursively walk an expression, replacing any [`QuestionMarkOp`]-shaped
/// patterns (represented as function-level `?` desugaring with `Return`) to
/// use `Break` to the given try-block label instead.
///
/// This is needed because source-level `?` inside a `try` block must
/// short-circuit to the block boundary, not to the function boundary.
///
/// The function recognizes the match pattern emitted by the source parser's
/// `desugar_try_operator` and rewrites `Return` exits to `Break` exits.
fn desugar_questions_in_expr(expr: &Expr, label: &str) -> Expr {
    match expr {
        // Recurse into blocks
        Expr::Block { stmts, expr: tail } => Expr::Block {
            stmts: stmts
                .iter()
                .map(|s| desugar_questions_in_stmt(s, label))
                .collect(),
            expr: tail
                .as_ref()
                .map(|e| Box::new(desugar_questions_in_expr(e, label))),
        },

        // Recurse into if/else
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(desugar_questions_in_expr(condition, label)),
            then_branch: Box::new(desugar_questions_in_expr(then_branch, label)),
            else_branch: else_branch
                .as_ref()
                .map(|e| Box::new(desugar_questions_in_expr(e, label))),
        },

        // Recurse into match arms
        Expr::Match { scrutinee, arms } => Expr::Match {
            scrutinee: Box::new(desugar_questions_in_expr(scrutinee, label)),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(|g| desugar_questions_in_expr(g, label)),
                    body: desugar_questions_in_expr(&arm.body, label),
                })
                .collect(),
        },

        // Rewrite `return Err(e)` to `break 'label Err(e)` and
        // `return None` to `break 'label None`
        Expr::Return(Some(inner)) => {
            if is_result_err(inner) || is_option_none(inner) {
                Expr::Break {
                    label: Some(label.to_string()),
                    value: Some(inner.clone()),
                }
            } else {
                // Non-error returns pass through (they exit the function)
                Expr::Return(Some(Box::new(desugar_questions_in_expr(inner, label))))
            }
        }

        // Do NOT recurse into nested loops/closures — they have their own scope
        Expr::Loop { .. } | Expr::While { .. } | Expr::For { .. } | Expr::Closure { .. } => {
            expr.clone()
        }

        // All other expressions pass through unchanged
        other => other.clone(),
    }
}

/// Rewrite statements within a try block scope.
fn desugar_questions_in_stmt(stmt: &crate::expr::Stmt, label: &str) -> crate::expr::Stmt {
    match stmt {
        crate::expr::Stmt::Let {
            pattern,
            ty,
            init,
            else_block,
        } => crate::expr::Stmt::Let {
            pattern: pattern.clone(),
            ty: ty.clone(),
            init: init
                .as_ref()
                .map(|e| Box::new(desugar_questions_in_expr(e, label))),
            else_block: else_block
                .as_ref()
                .map(|e| Box::new(desugar_questions_in_expr(e, label))),
        },
        crate::expr::Stmt::Expr(e) => crate::expr::Stmt::Expr(desugar_questions_in_expr(e, label)),
        crate::expr::Stmt::Item(_) => stmt.clone(),
    }
}

/// Check if an expression is `Result::Err(...)`.
fn is_result_err(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::EnumVariant {
            enum_name,
            variant,
            ..
        } if enum_name == "Result" && variant == "Err"
    )
}

/// Check if an expression is `Option::None`.
fn is_option_none(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::EnumVariant {
            enum_name,
            variant,
            ..
        } if enum_name == "Option" && variant == "None"
    )
}

#[cfg(test)]
#[cfg(test)]
#[path = "try_block_tests.rs"]
mod tests;
