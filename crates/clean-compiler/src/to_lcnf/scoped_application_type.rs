// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Full kernel typing for open constant applications in the active LCNF scope.

use super::LcnfContext;
use clean_kernel::{tc::TypeChecker, BinderInfo, Expr, ExprKind};

/// Recover an open constant application's type in its actual binder scope.
///
/// The context-free checker cannot check the arguments' loose BVars. Close the
/// expression under precisely the active typed binders instead of guessing a
/// primitive's codomain from its name. Full kernel inference checks the actual
/// constant declaration, exact universe instantiation, dependent Pi domains and
/// argument types, including in release builds (infer-only mode skips some of
/// those checks). Reopen the inferred telescope with the original stable ids.
///
/// Cached local types outside `bvar_stack` are deliberately not admitted: a
/// popped binder or an unavailable temporary cannot become typing authority.
/// Missing types, unknown/free locals, partial and oversaturated applications
/// retain the existing placeholder/refusal behavior.
pub(super) fn infer_scoped_const_application(ctx: &LcnfContext<'_>, expr: &Expr) -> Option<Expr> {
    if !matches!(expr.kind(), ExprKind::App(..)) {
        return None;
    }
    let ExprKind::Const(name, levels) = expr.get_app_fn().kind() else {
        return None;
    };
    let levels: Vec<_> = levels.iter().cloned().collect();
    let _ = ctx.env.instantiate_type(name, &levels)?;

    infer_scoped_expr_type(ctx, expr, true)
}

/// Infer an open expression's type under the active typed binder scope.
///
/// Closes `expr` under `ctx.bvar_stack` using `ctx.local_type`, runs full
/// kernel `infer_type_full`, and re-instantiates the outer binder telescope
/// with the original stable `FVarId`s. When `reject_pi_codomain` is true
/// (for call-site applications), partial applications whose inferred type
/// reduces to a `Pi` return `None` so callers keep the boxed closure fallback.
pub(super) fn infer_scoped_expr_type(
    ctx: &LcnfContext<'_>,
    expr: &Expr,
    reject_pi_codomain: bool,
) -> Option<Expr> {
    let mut closed = ctx.resolve_local_type(expr);
    for id in ctx.bvar_stack.iter().rev() {
        let ty = ctx.local_type(*id)?;
        closed = Expr::lam(BinderInfo::Default, ty.clone(), closed.abstract_fvar(*id));
    }
    if closed.has_fvar_quick() || closed.has_loose_bvars() {
        return None;
    }

    let tc = TypeChecker::with_mode(ctx.env, ctx.env.mode());
    let mut ty = tc.infer_type_full(&closed).ok()?;
    for id in &ctx.bvar_stack {
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return None;
        };
        ty = body.instantiate(&Expr::fvar(*id));
    }
    if reject_pi_codomain && matches!(tc.whnf(&ty).kind(), ExprKind::Pi(..)) {
        return None;
    }
    Some(ty)
}

/// A proof reference contributes no executable argument when the actual
/// application type-checks in the active local scope and its type has sort
/// Prop (or SProp). Looking at the declaration name alone would also erase an
/// ill-typed application or an unbound argument.
pub(super) fn scoped_proof_value_type(ctx: &LcnfContext<'_>, expr: &Expr) -> Option<Expr> {
    let ExprKind::Const(name, _) = expr.get_app_fn().kind() else {
        return None;
    };
    if !matches!(
        ctx.env.get_const(name)?.kind,
        clean_kernel::env::ConstantKind::Theorem | clean_kernel::env::ConstantKind::Definition
    ) {
        return None;
    }
    // Closed evidence inside a synthesized recursor branch has no local
    // typing dependencies. The enclosing branch can include temporary binders
    // whose types are unavailable to LCNF.
    let tc = TypeChecker::with_mode(ctx.env, ctx.env.mode());
    let infer = |term: &Expr| {
        if term.has_loose_bvars() || term.has_fvar_quick() {
            infer_scoped_expr_type(ctx, term, false)
        } else {
            tc.infer_type_full(term).ok()
        }
    };
    let ty = infer(expr)?;
    let sort = infer(&ty)?;
    (sort.is_prop() || matches!(sort.kind(), ExprKind::SProp)).then_some(ty)
}
