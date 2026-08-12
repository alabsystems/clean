// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared recursor-application scaffolding for kernel-side theorem
//! synthesis (the P3 lift bridges and the P4 deep-induction generator):
//! a telescope cursor that applies recursor arguments while exposing each
//! slot's instantiated domain, plus binder-safe telescope walkers and
//! closers over [`EnvDeclBuilder`] locals.

use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};

use super::decl_builder::EnvDeclBuilder;

/// Error surface: synthesis modules map the `&'static str` payloads into
/// their own invariant errors.
pub(crate) type RecApplyResult<T> = Result<T, &'static str>;

/// Cursor for applying arguments to a recursor while walking its stored Pi
/// telescope, so every slot's expected (instantiated) domain can be read off.
pub(crate) struct RecApply {
    pub(crate) term: Expr,
    pub(crate) cursor: Expr,
}

impl RecApply {
    pub(crate) fn new(head: Expr, ty: Expr) -> Self {
        RecApply {
            term: head,
            cursor: ty,
        }
    }

    pub(crate) fn peek_domain(&self) -> RecApplyResult<Expr> {
        match &self.cursor.kind {
            ExprKind::Pi(_, dom, _) => Ok((**dom).clone()),
            _ => Err("recursor telescope ended before all slots were applied"),
        }
    }

    pub(crate) fn apply(&mut self, arg: Expr) -> RecApplyResult<()> {
        match &self.cursor.kind {
            ExprKind::Pi(_, _, body) => {
                self.cursor = body.instantiate(&arg);
                self.term = Expr::app(self.term.clone(), arg);
                Ok(())
            }
            _ => Err("recursor telescope ended before all slots were applied"),
        }
    }
}

/// Walk a Pi telescope with fresh locals from `b`, instantiating as we go.
/// Returns the locals `(id, fvar, ty)` and the final codomain.
pub(crate) fn walk_telescope(
    b: &mut EnvDeclBuilder,
    ty: &Expr,
) -> (Vec<(FVarId, Expr, Expr)>, Expr) {
    let mut locals = Vec::new();
    let mut cursor = ty.clone();
    while let ExprKind::Pi(_, dom, body) = &cursor.kind {
        let dom = (**dom).clone();
        let (id, fv) = b.fresh_local(dom.clone());
        cursor = body.instantiate(&fv);
        locals.push((id, fv, dom));
    }
    (locals, cursor)
}

/// Close `body` under lambda binders for `locals`, innermost-last.
pub(crate) fn close_lams(b: &EnvDeclBuilder, locals: &[(FVarId, Expr, Expr)], body: Expr) -> Expr {
    let mut out = body;
    for (id, _, ty) in locals.iter().rev() {
        out = b.mk_lam(*id, BinderInfo::Default, ty.clone(), out);
    }
    out
}

/// Close `body` under Pi binders for `locals`, innermost-last.
pub(crate) fn close_pis(b: &EnvDeclBuilder, locals: &[(FVarId, Expr, Expr)], body: Expr) -> Expr {
    let mut out = body;
    for (id, _, ty) in locals.iter().rev() {
        out = b.mk_pi(*id, BinderInfo::Default, ty.clone(), out);
    }
    out
}
