// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Monadic do notation desugaring to surface syntax.
//!
//! This module provides a standalone surface-level desugaring pass that converts
//! a sequence of `DoElement` nodes into nested `SurfaceExpr` trees using
//! `Bind.bind`, `Pure.pure`, and `ForIn.forIn` combinators.
//!
//! The desugaring produces `SurfaceExpr` (surface AST) rather than kernel `Expr`,
//! so the result is fed into the normal elaboration pipeline for type inference,
//! implicit argument insertion, and kernel type checking.
//!
//! # Desugaring rules
//!
//! ```text
//! do                                     →  Bind.bind action1 (fun x =>
//!   let x ← action1                          Bind.bind action2 (fun y =>
//!   let y ← action2                            pure (x + y)))
//!   pure (x + y)
//!
//! for x in xs do body                    →  ForIn.forIn xs () (fun x _ => do body; pure (ForInStep.yield ()))
//!
//! while cond do body                     →  Lean.Loop.repeat (do if cond then body; pure (ForInStep.yield ()) else pure (ForInStep.done ()))
//! ```
//!
//! Reference: Lean 4 `src/Lean/Elab/Do/Basic.lean`

use crate::ElabError;
use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

// ---------------------------------------------------------------------------
// DoElement: standalone do-element representation
// ---------------------------------------------------------------------------

/// A single element in a do-notation block.
///
/// This is a simplified representation for surface-level desugaring,
/// independent of the parser's `DoElem` type. It captures the core
/// monadic do-notation constructs needed for desugaring to `SurfaceExpr`.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub(crate) enum DoElement {
    /// Monadic bind: `let name ← action` or bare `action` (with `name = None`).
    /// Desugars to: `Bind.bind action (fun name => rest)`
    Bind {
        name: Option<String>,
        action: Box<SurfaceExpr>,
    },

    /// Pure let binding: `let name := value`.
    /// Desugars to: `let name := value in rest`
    Let {
        name: String,
        value: Box<SurfaceExpr>,
    },

    /// Mutable let binding: `let mut name := value`.
    /// For surface desugaring, treated identically to `Let` (mutable variable
    /// lifting is handled during elaboration, not here).
    LetMut {
        name: String,
        value: Box<SurfaceExpr>,
    },

    /// Bare expression statement: `expr`.
    /// If not the last element: desugars to `Bind.bind expr (fun _ => rest)`.
    /// If the last element: the expression itself is the result.
    Action(Box<SurfaceExpr>),

    /// Return: `return expr`.
    /// Desugars to: `Pure.pure expr`
    Return(Box<SurfaceExpr>),

    /// Conditional: `if cond then thenBranch else elseBranch`.
    /// Both branches are nested do-element sequences.
    If {
        cond: Box<SurfaceExpr>,
        then_branch: Vec<DoElement>,
        else_branch: Vec<DoElement>,
    },

    /// For-in loop: `for var in collection do body`.
    /// Desugars to: `ForIn.forIn collection () (fun var _ => do body; Pure.pure (ForInStep.yield ()))`
    ForIn {
        var: String,
        collection: Box<SurfaceExpr>,
        body: Vec<DoElement>,
    },
}

// ---------------------------------------------------------------------------
// Surface expression constructors (internal helpers)
// ---------------------------------------------------------------------------

/// Build `Bind.bind action (fun name => body)`.
fn mk_bind(name: &str, action: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    let bind = SurfaceExpr::ident("Bind.bind");
    let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
    let continuation = SurfaceExpr::lambda(vec![binder], body);
    SurfaceExpr::app(bind, vec![action, continuation])
}

/// Build `Pure.pure val`.
fn mk_pure(val: SurfaceExpr) -> SurfaceExpr {
    let pure_fn = SurfaceExpr::ident("Pure.pure");
    SurfaceExpr::app(pure_fn, vec![val])
}

/// Build `let name := val in body`.
fn mk_let(name: &str, val: SurfaceExpr, body: SurfaceExpr) -> SurfaceExpr {
    let binder = SurfaceBinder::new(name, None, SurfaceBinderInfo::Explicit);
    SurfaceExpr::Let(Span::dummy(), binder, Box::new(val), Box::new(body))
}

/// Build `if cond then t else e`.
fn mk_if(cond: SurfaceExpr, then_expr: SurfaceExpr, else_expr: SurfaceExpr) -> SurfaceExpr {
    SurfaceExpr::If(
        Span::dummy(),
        Box::new(cond),
        Box::new(then_expr),
        Box::new(else_expr),
    )
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Desugar a do-block (sequence of `DoElement`) into a single `SurfaceExpr`.
///
/// Processes elements left-to-right, threading the monadic context:
/// - `Bind { name, action }` -> `Bind.bind action (fun name => rest)`
/// - `Let { name, value }` -> `let name := value in rest`
/// - `LetMut { name, value }` -> `let name := value in rest` (surface level)
/// - `Action(expr)` -> `Bind.bind expr (fun _ => rest)` (non-terminal), or `expr` (terminal)
/// - `Return(expr)` -> `Pure.pure expr`
/// - `If { .. }` -> `if cond then (desugar thenBranch) else (desugar elseBranch)`
/// - `ForIn { .. }` -> delegated to [`desugar_for_in`]
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if the do block is empty.
///
/// # REQUIRES
/// - `elements` is non-empty
///
/// # ENSURES
/// - On success, returns a `SurfaceExpr` equivalent to the nested bind/pure chain
pub(crate) fn desugar_do_block(elements: &[DoElement]) -> Result<SurfaceExpr, ElabError> {
    match elements {
        [] => Err(ElabError::NotImplemented("empty do block".into())),
        [single] => desugar_terminal(single),
        [first, rest @ ..] => desugar_compound(first, rest),
    }
}

/// Desugar a single terminal do-element (no continuation).
fn desugar_terminal(elem: &DoElement) -> Result<SurfaceExpr, ElabError> {
    match elem {
        DoElement::Action(expr) => Ok(*expr.clone()),
        DoElement::Return(expr) => Ok(mk_pure(*expr.clone())),
        // Terminal bind: degenerate case, return the action itself.
        DoElement::Bind { action, .. } => Ok(*action.clone()),
        DoElement::Let { .. } | DoElement::LetMut { .. } => Err(ElabError::NotImplemented(
            "do block cannot end with a let binding (no continuation)".into(),
        )),
        DoElement::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_expr = desugar_do_block(then_branch)?;
            let else_expr = desugar_else_branch(else_branch)?;
            Ok(mk_if(*cond.clone(), then_expr, else_expr))
        }
        DoElement::ForIn {
            var,
            collection,
            body,
        } => desugar_for_in(var, collection, body),
    }
}

/// Desugar a compound do-element (has a continuation in `rest`).
fn desugar_compound(first: &DoElement, rest: &[DoElement]) -> Result<SurfaceExpr, ElabError> {
    let rest_expr = desugar_do_block(rest)?;
    match first {
        DoElement::Bind { name, action } => {
            let bind_name = name.as_deref().unwrap_or("_");
            Ok(mk_bind(bind_name, *action.clone(), rest_expr))
        }
        DoElement::Let { name, value } | DoElement::LetMut { name, value } => {
            Ok(mk_let(name, *value.clone(), rest_expr))
        }
        DoElement::Action(expr) => Ok(mk_bind("_", *expr.clone(), rest_expr)),
        // Non-terminal return: pure the value; rest is unreachable.
        DoElement::Return(expr) => Ok(mk_pure(*expr.clone())),
        DoElement::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_expr = desugar_do_block(then_branch)?;
            let else_expr = desugar_else_branch(else_branch)?;
            let if_expr = mk_if(*cond.clone(), then_expr, else_expr);
            Ok(mk_bind("_", if_expr, rest_expr))
        }
        DoElement::ForIn {
            var,
            collection,
            body,
        } => {
            let for_expr = desugar_for_in(var, collection, body)?;
            Ok(mk_bind("_", for_expr, rest_expr))
        }
    }
}

/// Desugar an else branch, defaulting to `Pure.pure PUnit.unit` when empty.
fn desugar_else_branch(else_branch: &[DoElement]) -> Result<SurfaceExpr, ElabError> {
    if else_branch.is_empty() {
        Ok(mk_pure(SurfaceExpr::ident("PUnit.unit")))
    } else {
        desugar_do_block(else_branch)
    }
}

/// Desugar a for-in loop into a `ForIn.forIn` application.
///
/// ```text
/// for x in xs do
///   body
/// ```
///
/// Desugars to:
/// ```text
/// ForIn.forIn xs () (fun x _ =>
///   do { body; Pure.pure (ForInStep.yield ()) })
/// ```
///
/// The accumulator type is `PUnit` (unit) and the step function returns
/// `ForInStep.yield ()` to signal "keep iterating".
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if `body` is empty.
///
/// # REQUIRES
/// - `body` is non-empty
///
/// # ENSURES
/// - Returns a `SurfaceExpr` equivalent to `ForIn.forIn collection init step_fn`
pub(crate) fn desugar_for_in(
    var: &str,
    collection: &SurfaceExpr,
    body: &[DoElement],
) -> Result<SurfaceExpr, ElabError> {
    if body.is_empty() {
        return Err(ElabError::NotImplemented("empty for-in body".into()));
    }

    // Build the body expression, then append `Pure.pure (ForInStep.yield ())`
    let body_expr = desugar_do_block(body)?;

    // Continuation result: Pure.pure (ForInStep.yield ())
    let yield_step = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.yield"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    let yield_pure = mk_pure(yield_step);

    // Combine body with yield: bind body (_ => yield_pure)
    let step_body = mk_bind("_", body_expr, yield_pure);

    // Step function: fun var _ => step_body
    let var_binder = SurfaceBinder::new(var, None, SurfaceBinderInfo::Explicit);
    let acc_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
    let step_fn = SurfaceExpr::lambda(vec![var_binder, acc_binder], step_body);

    // Initial accumulator: ()
    let init = SurfaceExpr::ident("PUnit.unit");

    // ForIn.forIn collection init step_fn
    let for_in = SurfaceExpr::ident("ForIn.forIn");
    Ok(SurfaceExpr::app(
        for_in,
        vec![collection.clone(), init, step_fn],
    ))
}

/// Desugar a while loop into a repeat-with-conditional construct.
///
/// ```text
/// while cond do
///   body
/// ```
///
/// Desugars to:
/// ```text
/// Lean.Loop.repeat (do
///   if cond then
///     body; Pure.pure (ForInStep.yield ())
///   else
///     Pure.pure (ForInStep.done ()))
/// ```
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if `body` is empty.
///
/// # REQUIRES
/// - `body` is non-empty
///
/// # ENSURES
/// - Returns a `SurfaceExpr` equivalent to a repeat-with-conditional loop
pub(crate) fn desugar_while(
    cond: &SurfaceExpr,
    body: &[DoElement],
) -> Result<SurfaceExpr, ElabError> {
    if body.is_empty() {
        return Err(ElabError::NotImplemented("empty while body".into()));
    }

    let body_expr = desugar_do_block(body)?;

    // Then branch: body; Pure.pure (ForInStep.yield ())
    let yield_step = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.yield"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    let yield_pure = mk_pure(yield_step);
    let then_expr = mk_bind("_", body_expr, yield_pure);

    // Else branch: Pure.pure (ForInStep.done ())
    let done_step = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.done"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    let else_expr = mk_pure(done_step);

    // if cond then ... else ...
    let if_expr = mk_if(cond.clone(), then_expr, else_expr);

    // Lean.Loop.repeat (if_expr)
    let repeat_fn = SurfaceExpr::ident("Lean.Loop.repeat");
    Ok(SurfaceExpr::app(repeat_fn, vec![if_expr]))
}

// ---------------------------------------------------------------------------
// Conversion from parser DoElem to DoElement
// ---------------------------------------------------------------------------

/// Convert a parser `DoElem` sequence into `DoElement` sequence.
///
/// This bridges the parser's `DoElem` type (which has many variants for
/// elaboration) into the simplified `DoElement` type used by standalone
/// surface desugaring.
///
/// Variants not directly representable in `DoElement` (e.g., `TryCatch`,
/// `Match`, `Break`, `Continue`) are mapped to `Action` with a placeholder
/// so they can still be processed. The full elaboration pipeline
/// (`elab_do.rs`) handles these directly without this conversion.
pub(crate) fn from_parser_do_elems(elems: &[clean_parser::DoElem]) -> Vec<DoElement> {
    elems.iter().map(from_parser_do_elem).collect()
}

fn from_parser_do_elem(elem: &clean_parser::DoElem) -> DoElement {
    match elem {
        clean_parser::DoElem::Bind(_, binder, action) => DoElement::Bind {
            name: if binder.name == "_" {
                None
            } else {
                Some(binder.name.clone())
            },
            action: action.clone(),
        },

        clean_parser::DoElem::Let(_, binder, val) => DoElement::Let {
            name: binder.name.clone(),
            value: val.clone(),
        },

        clean_parser::DoElem::LetMut(_, binder, val) => DoElement::LetMut {
            name: binder.name.clone(),
            value: val.clone(),
        },

        clean_parser::DoElem::Return(_, expr) => DoElement::Return(expr.clone()),

        clean_parser::DoElem::Expr(_, expr) => DoElement::Action(expr.clone()),

        clean_parser::DoElem::If(_, cond, then_branch, else_branch) => DoElement::If {
            cond: cond.clone(),
            then_branch: from_parser_do_elems(then_branch),
            else_branch: else_branch
                .as_ref()
                .map(|e| from_parser_do_elems(e))
                .unwrap_or_default(),
        },

        clean_parser::DoElem::For(_, binder, collection, body) => DoElement::ForIn {
            var: binder.name.clone(),
            collection: collection.clone(),
            body: from_parser_do_elems(body),
        },

        // All other variants map to Action with the original element's span.
        // The full elaboration pipeline handles these natively.
        other => {
            let span = match other {
                clean_parser::DoElem::LetRec(s, _)
                | clean_parser::DoElem::IfLet(s, _, _, _, _)
                | clean_parser::DoElem::IfDecidable(s, _, _, _, _)
                | clean_parser::DoElem::Match(s, _, _)
                | clean_parser::DoElem::TryCatch(s, _, _, _)
                | clean_parser::DoElem::LetElse(s, _, _, _)
                | clean_parser::DoElem::LetExpr(s, _, _, _, _)
                | clean_parser::DoElem::Repeat(s, _)
                | clean_parser::DoElem::While(s, _, _)
                | clean_parser::DoElem::DbgTrace(s, _)
                | clean_parser::DoElem::Break(s)
                | clean_parser::DoElem::Continue(s)
                | clean_parser::DoElem::Reassign(s, _, _)
                | clean_parser::DoElem::PatternReassign(s, _, _) => *s,
                // Already handled above
                clean_parser::DoElem::Bind(s, _, _)
                | clean_parser::DoElem::Let(s, _, _)
                | clean_parser::DoElem::LetMut(s, _, _)
                | clean_parser::DoElem::Return(s, _)
                | clean_parser::DoElem::Expr(s, _)
                | clean_parser::DoElem::If(s, _, _, _)
                | clean_parser::DoElem::For(s, _, _, _) => *s,
            };
            DoElement::Action(Box::new(SurfaceExpr::Hole(span)))
        }
    }
}
