// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Control flow desugaring for kernel-level do-notation.
//!
//! Extracted from [`do_notation_desugar`] to keep each module under 500 lines.
//! Contains desugaring for:
//! - **For-in loops** → `ForIn.forIn iter () step_fn`
//! - **Try/catch** → `MonadExcept.tryCatch try_expr handler`
//! - **Repeat/until** → `ForIn.forIn Lean.Loop.mk () step_fn`
//!
//! All functions accept and forward the `DoDesugarConfig` and `bind_count`
//! accumulator from the parent desugaring pass.
//!
//! Reference: Lean 4 `src/Lean/Elab/Do/Basic.lean`

use crate::do_notation_desugar::{
    desugar_stmts, fresh_fvar_id, make_bind, make_ite, make_pure, make_unit, subst_stmts,
    DoDesugarConfig, DoStmt,
};
use crate::ElabError;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Name};

// ---------------------------------------------------------------------------
// For loop desugaring
// ---------------------------------------------------------------------------

/// Desugar a for-in loop into `ForIn.forIn iter () (fun var _ => body)`.
///
/// The loop body is desugared and wrapped with a yield step continuation.
/// If `rest` is non-empty, the loop result is bound to `_` via `Bind.bind`
/// before the continuation.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if the loop body is empty.
pub(crate) fn desugar_for_loop(
    var: &Name,
    iter: &Expr,
    body: &[DoStmt],
    rest: &[DoStmt],
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    if body.is_empty() {
        return Err(ElabError::NotImplemented("empty for loop body".into()));
    }

    // Create a fresh FVar for the loop variable so references in the body
    // are properly captured as BVar in the step function lambda.
    let fvar_id = fresh_fvar_id();
    let subst_body = subst_stmts(body, var, fvar_id);
    let body_expr = desugar_stmts(&subst_body, config, bind_count)?;

    // yield step: Pure.pure (ForInStep.yield ())
    let yield_step = Expr::app(Expr::const_str("ForInStep.yield"), make_unit());
    let yield_pure = make_pure(yield_step);

    // body; yield
    *bind_count += 1;
    let wildcard = Name::from_string("_");
    let step_body = make_bind(body_expr, &wildcard, yield_pure);

    // Step function: fun var _ => step_body
    // First wrap in inner lambda (accumulator), then abstract FVar so var
    // resolves to BVar(1) (the outer lambda parameter) inside the body.
    let inner_lam = Expr::lam(BinderInfo::Default, Expr::const_str("_hole"), step_body);
    let abstracted_inner = inner_lam.abstract_fvar(fvar_id);
    let step_fn = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("_hole"),
        abstracted_inner,
    );

    // ForIn.forIn iter () step_fn
    let for_in = Expr::const_str("ForIn.forIn");
    let for_expr = Expr::app(
        Expr::app(Expr::app(for_in, iter.clone()), make_unit()),
        step_fn,
    );

    if rest.is_empty() {
        Ok(for_expr)
    } else {
        let rest_expr = desugar_stmts(rest, config, bind_count)?;
        *bind_count += 1;
        Ok(make_bind(for_expr, &wildcard, rest_expr))
    }
}

// ---------------------------------------------------------------------------
// Try/catch desugaring
// ---------------------------------------------------------------------------

/// Desugar try/catch into `MonadExcept.tryCatch try_body handler`.
///
/// The handler is a lambda `fun catch_var => catch_body`. If `rest` is
/// non-empty, the result is bound to `_` before the continuation.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if the try body is empty.
pub(crate) fn desugar_try_catch(
    try_body: &[DoStmt],
    catch_var: &Name,
    catch_body: &[DoStmt],
    rest: &[DoStmt],
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    if try_body.is_empty() {
        return Err(ElabError::NotImplemented("empty try body".into()));
    }

    let try_expr = desugar_stmts(try_body, config, bind_count)?;

    // Create a fresh FVar for the catch variable so references in the catch body
    // are properly captured as BVar in the handler lambda.
    let fvar_id = fresh_fvar_id();
    let catch_expr = if catch_body.is_empty() {
        make_pure(make_unit())
    } else {
        let subst_catch = subst_stmts(catch_body, catch_var, fvar_id);
        desugar_stmts(&subst_catch, config, bind_count)?
    };

    // Handler: fun catch_var => catch_body
    // Abstract FVar so catch_var resolves to BVar(0) inside the handler lambda.
    let abstracted_catch = catch_expr.abstract_fvar(fvar_id);
    let handler = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("_hole"),
        abstracted_catch,
    );

    // MonadExcept.tryCatch try_expr handler
    let try_catch = Expr::const_str("MonadExcept.tryCatch");
    let tc_expr = Expr::app(Expr::app(try_catch, try_expr), handler);

    if rest.is_empty() {
        Ok(tc_expr)
    } else {
        let rest_expr = desugar_stmts(rest, config, bind_count)?;
        *bind_count += 1;
        let wildcard = Name::from_string("_");
        Ok(make_bind(tc_expr, &wildcard, rest_expr))
    }
}

// ---------------------------------------------------------------------------
// Repeat desugaring
// ---------------------------------------------------------------------------

/// Desugar `repeat body [until cond]` into `ForIn.forIn Lean.Loop.mk () step_fn`.
///
/// Without an `until` condition, the step function always yields. With one,
/// it checks the condition after each body execution and returns
/// `ForInStep.done` to break when the condition holds.
///
/// # Errors
///
/// Returns `ElabError::NotImplemented` if the body is empty.
pub(crate) fn desugar_repeat(
    body: &[DoStmt],
    until: Option<&Expr>,
    config: &DoDesugarConfig,
    bind_count: &mut usize,
) -> Result<Expr, ElabError> {
    if body.is_empty() {
        return Err(ElabError::NotImplemented("empty repeat body".into()));
    }

    let body_expr = desugar_stmts(body, config, bind_count)?;

    // Yield step: Pure.pure (ForInStep.yield ())
    let yield_step = Expr::app(Expr::const_str("ForInStep.yield"), make_unit());
    let yield_pure = make_pure(yield_step);

    let step_result = if let Some(until_cond) = until {
        let done_step = Expr::app(Expr::const_str("ForInStep.done"), make_unit());
        let done_pure = make_pure(done_step);
        make_ite(until_cond.clone(), done_pure, yield_pure)
    } else {
        yield_pure
    };

    // body; step_result
    *bind_count += 1;
    let wildcard = Name::from_string("_");
    let step_body = make_bind(body_expr, &wildcard, step_result);

    // Step function: fun _ _ => step_body
    let step_fn = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("_hole"),
        Expr::lam(BinderInfo::Default, Expr::const_str("_hole"), step_body),
    );

    // ForIn.forIn Lean.Loop.mk () step_fn
    let for_in = Expr::const_str("ForIn.forIn");
    let loop_mk = Expr::const_str("Lean.Loop.mk");
    Ok(Expr::app(
        Expr::app(Expr::app(for_in, loop_mk), make_unit()),
        step_fn,
    ))
}
