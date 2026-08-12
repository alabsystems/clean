// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended do-notation desugaring for advanced monadic patterns.
//!
//! Supplements `do_notation.rs` with desugaring for constructs that the base
//! module maps to `Action(Hole)` placeholders:
//!
//! - **Try/catch** (`DoElem::TryCatch`) — `MonadExcept.tryCatch` / `tryCatchThe`
//! - **Reassignment** (`DoElem::Reassign`) — `StateT.set` for mutable variable update
//! - **Break/continue** — `ForInStep.done` / loop continuation control
//! - **Nested do-blocks** — recursive desugaring of inner blocks
//! - **DbgTrace** — `dbgTrace msg (fun () => rest)`
//! - **Repeat** — `ForIn.forIn Lean.Loop.mk () (fun _ _ => body)`
//!
//! Each function in this module converts a specific `DoElem` variant into
//! `SurfaceExpr` using the monad combinator vocabulary established by Lean 4.
//!
//! Reference: Lean 4 `src/Lean/Elab/Do/Basic.lean`

use crate::do_notation::{desugar_do_block, DoElement};
use crate::ElabError;
use clean_parser::{DoCatchClause, DoElem, Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

// ---------------------------------------------------------------------------
// Error type for extended do-notation
// ---------------------------------------------------------------------------

/// Errors specific to extended do-notation desugaring.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) enum DoExtError {
    /// A try block has no catch or finally clauses.
    #[error("try block requires at least one catch or finally clause")]
    TryWithoutHandler,

    /// A break statement appears outside a loop context.
    #[error("break outside of for/repeat/while loop")]
    BreakOutsideLoop,

    /// A continue statement appears outside a loop context.
    #[error("continue outside of for/repeat/while loop")]
    ContinueOutsideLoop,

    /// An empty try body was supplied.
    #[error("empty try body")]
    EmptyTryBody,

    /// Reassignment target is not a valid mutable variable name.
    #[error("invalid reassignment target: {0}")]
    InvalidReassignTarget(String),
}

impl From<DoExtError> for ElabError {
    fn from(err: DoExtError) -> Self {
        ElabError::NotImplemented(err.to_string())
    }
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

// ---------------------------------------------------------------------------
// Try/Catch desugaring
// ---------------------------------------------------------------------------

/// Desugar a try/catch/finally block into `MonadExcept.tryCatch` / `tryCatchThe`
/// / `tryFinally` combinator chains.
///
/// Multiple catch clauses fold left. Typed catches use `tryCatchThe ExcType`.
///
/// # Errors
///
/// Returns error if try body is empty or no catch/finally clause is present.
pub(crate) fn desugar_try_catch(
    try_body: &[DoElement],
    catches: &[CatchClause],
    finally_body: Option<&[DoElement]>,
) -> Result<SurfaceExpr, ElabError> {
    if try_body.is_empty() {
        return Err(DoExtError::EmptyTryBody.into());
    }
    if catches.is_empty() && finally_body.is_none() {
        return Err(DoExtError::TryWithoutHandler.into());
    }

    let mut expr = desugar_do_block(try_body)?;

    // Wrap with each catch clause (fold left)
    for clause in catches {
        expr = desugar_single_catch(expr, clause)?;
    }

    // Wrap with finally if present
    if let Some(fin_body) = finally_body {
        if !fin_body.is_empty() {
            let fin_expr = desugar_do_block(fin_body)?;
            let try_finally = SurfaceExpr::ident("tryFinally");
            expr = SurfaceExpr::app(try_finally, vec![expr, fin_expr]);
        }
    }

    Ok(expr)
}

/// A catch clause in a try/catch block (simplified from parser `DoCatchClause`).
#[derive(Debug, Clone)]
pub(crate) struct CatchClause {
    /// Exception binder name
    pub(crate) binder: String,
    /// Optional exception type (uses `tryCatchThe` when present)
    pub(crate) exc_type: Option<SurfaceExpr>,
    /// Handler body as do-elements
    pub(crate) body: Vec<DoElement>,
}

/// Convert a parser `DoCatchClause` to the simplified `CatchClause`.
pub(crate) fn from_parser_catch_clause(clause: &DoCatchClause) -> CatchClause {
    CatchClause {
        binder: clause.binder.clone(),
        exc_type: clause.exc_type.as_ref().map(|e| *e.clone()),
        body: crate::do_notation::from_parser_do_elems(&clause.body),
    }
}

/// Desugar a single catch clause wrapping an expression.
fn desugar_single_catch(
    body_expr: SurfaceExpr,
    clause: &CatchClause,
) -> Result<SurfaceExpr, ElabError> {
    let handler_body = if clause.body.is_empty() {
        mk_pure(SurfaceExpr::ident("PUnit.unit"))
    } else {
        desugar_do_block(&clause.body)?
    };

    let binder = SurfaceBinder::new(&clause.binder, None, SurfaceBinderInfo::Explicit);
    let handler_fn = SurfaceExpr::lambda(vec![binder], handler_body);

    if let Some(ref exc_ty) = clause.exc_type {
        // tryCatchThe ExcType body (fun e => handler)
        let try_catch_the = SurfaceExpr::ident("tryCatchThe");
        Ok(SurfaceExpr::app(
            try_catch_the,
            vec![exc_ty.clone(), body_expr, handler_fn],
        ))
    } else {
        // MonadExcept.tryCatch body (fun e => handler)
        let try_catch = SurfaceExpr::ident("MonadExcept.tryCatch");
        Ok(SurfaceExpr::app(try_catch, vec![body_expr, handler_fn]))
    }
}

// ---------------------------------------------------------------------------
// Reassignment desugaring
// ---------------------------------------------------------------------------

/// Desugar mutable variable reassignment `x := new_val` as let-shadowing.
///
/// The actual StateT lifting is handled by the full elaboration pipeline;
/// surface desugaring produces `let x := new_val in rest`.
pub(crate) fn desugar_reassign(
    var: &str,
    new_val: &SurfaceExpr,
    rest: &[DoElement],
) -> Result<SurfaceExpr, ElabError> {
    if var.is_empty() {
        return Err(DoExtError::InvalidReassignTarget(var.to_string()).into());
    }
    let rest_expr = desugar_do_block(rest)?;
    Ok(mk_let(var, new_val.clone(), rest_expr))
}

// ---------------------------------------------------------------------------
// Break/Continue desugaring
// ---------------------------------------------------------------------------

/// Desugar `break` to `Pure.pure (ForInStep.done ())`.
pub(crate) fn desugar_break() -> SurfaceExpr {
    let done = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.done"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    mk_pure(done)
}

/// Desugar `continue` to `Pure.pure (ForInStep.yield ())`.
pub(crate) fn desugar_continue() -> SurfaceExpr {
    let yield_step = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.yield"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    mk_pure(yield_step)
}

// ---------------------------------------------------------------------------
// DbgTrace desugaring
// ---------------------------------------------------------------------------

/// Desugar `dbg_trace msg` to `dbgTrace msg (fun _ => rest)`.
pub(crate) fn desugar_dbg_trace(
    msg: &SurfaceExpr,
    rest: &[DoElement],
) -> Result<SurfaceExpr, ElabError> {
    let rest_expr = desugar_do_block(rest)?;
    let unit_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
    let thunk = SurfaceExpr::lambda(vec![unit_binder], rest_expr);
    let dbg_fn = SurfaceExpr::ident("dbgTrace");
    Ok(SurfaceExpr::app(dbg_fn, vec![msg.clone(), thunk]))
}

// ---------------------------------------------------------------------------
// Repeat desugaring
// ---------------------------------------------------------------------------

/// Desugar `repeat body` to `ForIn.forIn Lean.Loop.mk () step_fn`.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if `body` is empty.
pub(crate) fn desugar_repeat(body: &[DoElement]) -> Result<SurfaceExpr, ElabError> {
    if body.is_empty() {
        return Err(ElabError::NotImplemented("empty repeat body".into()));
    }

    let body_expr = desugar_do_block(body)?;

    // Continuation: body; Pure.pure (ForInStep.yield ())
    let yield_step = SurfaceExpr::app(
        SurfaceExpr::ident("ForInStep.yield"),
        vec![SurfaceExpr::ident("PUnit.unit")],
    );
    let yield_pure = mk_pure(yield_step);
    let step_body = mk_bind("_", body_expr, yield_pure);

    // Step function: fun _ _ => step_body
    let iter_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
    let acc_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
    let step_fn = SurfaceExpr::lambda(vec![iter_binder, acc_binder], step_body);

    // ForIn.forIn Lean.Loop.mk () step_fn
    let for_in = SurfaceExpr::ident("ForIn.forIn");
    let loop_mk = SurfaceExpr::ident("Lean.Loop.mk");
    let init = SurfaceExpr::ident("PUnit.unit");
    Ok(SurfaceExpr::app(for_in, vec![loop_mk, init, step_fn]))
}

// ---------------------------------------------------------------------------
// Nested do-block desugaring
// ---------------------------------------------------------------------------

/// Desugar a nested do-block by recursively applying `desugar_do_block`.
pub(crate) fn desugar_nested_do(inner_elements: &[DoElement]) -> Result<SurfaceExpr, ElabError> {
    desugar_do_block(inner_elements)
}

// ---------------------------------------------------------------------------
// Extended DoElem conversion
// ---------------------------------------------------------------------------

/// Convert a parser `DoElem::TryCatch` to desugared `SurfaceExpr`.
///
/// This provides direct conversion from parser representation, bridging the
/// gap that `from_parser_do_elem` fills with a `Hole` placeholder.
pub(crate) fn desugar_parser_try_catch(
    try_body: &[DoElem],
    catches: &[DoCatchClause],
    finally_body: Option<&[DoElem]>,
) -> Result<SurfaceExpr, ElabError> {
    let try_elements = crate::do_notation::from_parser_do_elems(try_body);
    let catch_clauses: Vec<CatchClause> = catches.iter().map(from_parser_catch_clause).collect();
    let finally_elements = finally_body.map(crate::do_notation::from_parser_do_elems);
    desugar_try_catch(&try_elements, &catch_clauses, finally_elements.as_deref())
}

/// Desugar a `DoElem::Reassign` within a do-block continuation.
///
/// Converts `x := new_val` followed by remaining elements into surface
/// let-shadowing with the rest of the block.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) fn desugar_parser_reassign(
    var: &str,
    new_val: &SurfaceExpr,
    rest: &[DoElem],
) -> Result<SurfaceExpr, ElabError> {
    let rest_elements = crate::do_notation::from_parser_do_elems(rest);
    desugar_reassign(var, new_val, &rest_elements)
}

// ---------------------------------------------------------------------------
// Extended desugar for full DoElem (all variants)
// ---------------------------------------------------------------------------

/// Desugar a complete sequence of `DoElem` using extended patterns.
///
/// This is the full-featured alternative to `do_notation::desugar_do_block`
/// that handles all `DoElem` variants natively rather than falling back to
/// `Hole` placeholders for unsupported ones.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` for empty sequences.
pub(crate) fn desugar_do_elems_ext(elems: &[DoElem]) -> Result<SurfaceExpr, ElabError> {
    match elems {
        [] => Err(ElabError::NotImplemented("empty do block".into())),
        [single] => desugar_single_ext(single),
        [first, rest @ ..] => desugar_compound_ext(first, rest),
    }
}

/// Desugar a single terminal `DoElem` with extended support.
fn desugar_single_ext(elem: &DoElem) -> Result<SurfaceExpr, ElabError> {
    match elem {
        DoElem::Expr(_, expr) => Ok(*expr.clone()),
        DoElem::Return(_, expr) => Ok(mk_pure(*expr.clone())),
        DoElem::Bind(_, _, action) => Ok(*action.clone()),
        DoElem::Let(_, _, _) | DoElem::LetMut(_, _, _) => Err(ElabError::NotImplemented(
            "do block cannot end with a let binding".into(),
        )),
        DoElem::If(_, cond, then_b, else_b) => {
            let then_expr = desugar_do_elems_ext(then_b)?;
            let else_expr = if let Some(e) = else_b {
                desugar_do_elems_ext(e)?
            } else {
                mk_pure(SurfaceExpr::ident("PUnit.unit"))
            };
            Ok(SurfaceExpr::If(
                Span::dummy(),
                cond.clone(),
                Box::new(then_expr),
                Box::new(else_expr),
            ))
        }
        DoElem::For(_, binder, collection, body) => crate::do_notation::desugar_for_in(
            &binder.name,
            collection,
            &crate::do_notation::from_parser_do_elems(body),
        ),
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            desugar_parser_try_catch(try_body, catches, finally_body.as_deref())
        }
        DoElem::Break(_) => Ok(desugar_break()),
        DoElem::Continue(_) => Ok(desugar_continue()),
        DoElem::Repeat(_, body) => {
            let elements = crate::do_notation::from_parser_do_elems(body);
            desugar_repeat(&elements)
        }
        DoElem::While(_, cond, body) => {
            let elements = crate::do_notation::from_parser_do_elems(body);
            crate::do_notation::desugar_while(cond, &elements)
        }
        _ => {
            // Fallback for remaining variants (LetRec, IfLet, Match, etc.)
            let converted = crate::do_notation::from_parser_do_elems(std::slice::from_ref(elem));
            desugar_do_block(&converted)
        }
    }
}

/// Desugar a compound `DoElem` (with continuation) using extended support.
fn desugar_compound_ext(first: &DoElem, rest: &[DoElem]) -> Result<SurfaceExpr, ElabError> {
    let rest_expr = desugar_do_elems_ext(rest)?;
    match first {
        DoElem::Bind(_, binder, action) => {
            let name = if binder.name == "_" {
                "_"
            } else {
                &binder.name
            };
            Ok(mk_bind(name, *action.clone(), rest_expr))
        }
        DoElem::Let(_, binder, value) | DoElem::LetMut(_, binder, value) => {
            Ok(mk_let(&binder.name, *value.clone(), rest_expr))
        }
        DoElem::Expr(_, expr) => Ok(mk_bind("_", *expr.clone(), rest_expr)),
        DoElem::Return(_, expr) => Ok(mk_pure(*expr.clone())),
        DoElem::If(_, cond, then_b, else_b) => {
            let then_expr = desugar_do_elems_ext(then_b)?;
            let else_expr = if let Some(e) = else_b {
                desugar_do_elems_ext(e)?
            } else {
                mk_pure(SurfaceExpr::ident("PUnit.unit"))
            };
            let if_expr = SurfaceExpr::If(
                Span::dummy(),
                cond.clone(),
                Box::new(then_expr),
                Box::new(else_expr),
            );
            Ok(mk_bind("_", if_expr, rest_expr))
        }
        DoElem::For(_, binder, collection, body) => {
            let for_expr = crate::do_notation::desugar_for_in(
                &binder.name,
                collection,
                &crate::do_notation::from_parser_do_elems(body),
            )?;
            Ok(mk_bind("_", for_expr, rest_expr))
        }
        DoElem::TryCatch(_, try_body, catches, finally_body) => {
            let tc_expr = desugar_parser_try_catch(try_body, catches, finally_body.as_deref())?;
            Ok(mk_bind("_", tc_expr, rest_expr))
        }
        DoElem::Reassign(_, var, new_val) => Ok(mk_let(var, *new_val.clone(), rest_expr)),
        DoElem::DbgTrace(_, msg) => {
            let unit_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
            let thunk = SurfaceExpr::lambda(vec![unit_binder], rest_expr);
            let dbg_fn = SurfaceExpr::ident("dbgTrace");
            Ok(SurfaceExpr::app(dbg_fn, vec![*msg.clone(), thunk]))
        }
        DoElem::Repeat(_, body) => {
            let elements = crate::do_notation::from_parser_do_elems(body);
            let repeat_expr = desugar_repeat(&elements)?;
            Ok(mk_bind("_", repeat_expr, rest_expr))
        }
        DoElem::While(_, cond, body) => {
            let elements = crate::do_notation::from_parser_do_elems(body);
            let while_expr = crate::do_notation::desugar_while(cond, &elements)?;
            Ok(mk_bind("_", while_expr, rest_expr))
        }
        DoElem::Break(_) => Ok(desugar_break()),
        DoElem::Continue(_) => Ok(desugar_continue()),
        _ => {
            // Fallback: convert via from_parser_do_elems and delegate
            let mut all_elems = vec![first.clone()];
            all_elems.extend_from_slice(rest);
            let converted = crate::do_notation::from_parser_do_elems(&all_elems);
            desugar_do_block(&converted)
        }
    }
}
