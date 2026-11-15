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
    if matches!(tc.whnf(&ty).kind(), ExprKind::Pi(..)) {
        return None;
    }
    Some(ty)
}
