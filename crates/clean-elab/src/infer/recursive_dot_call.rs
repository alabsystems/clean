// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A structural self-call written in generalized field notation whose
//! receiver is NOT the first explicit argument.
//!
//! ```text
//! def Ex.evalAt (k : Int) (w : Nat) : Ex → Int
//!   | .lit v     => v + k
//!   | .add e₁ e₂ => e₁.evalAt k w + e₂.evalAt k w
//! ```
//!
//! Lean 4.8.0 resolves `e₁.evalAt k w` against the function being defined
//! (`LValResolution.localRec`, `Lean/Elab/App.lean`) and places the receiver
//! with `addLValArg`: it walks the function's binders, counting explicit
//! ones, and inserts `e₁` at the first binder whose type is an application of
//! the receiver's type head `Ex` — here the third explicit argument, giving
//! `Ex.evalAt k w e₁`. Clean's method-dot path returned the induction
//! hypothesis for `e₁` and then applied it to `k w`, which is right only when
//! the receiver is the first explicit argument; with `k w` in front the
//! definition was refused (trust-ir `Proofs/AYBridge.lean`
//! `TrustIrExpr.evalAt`, whose failure the rest of that file inherits).
//!
//! This module performs `addLValArg` against the declaration telescope the
//! recursion context recorded and hands the reordered call to
//! [`ElabCtx::try_elab_recursive_call`], the path an explicitly spelled
//! `Ex.evalAt k w e₁` already takes: every argument is elaborated and checked,
//! the receiver must be the structural child an induction hypothesis is bound
//! for, and the fixed parameters must be passed unchanged.
//!
//! The method-dot path (`elab_proj`) substitutes the receiver's induction
//! hypothesis, so it computes the call with the receiver in the DECREASING
//! position. That is Lean's call only when `addLValArg` puts the receiver
//! there too. It is kept for the one placement where both are position 0, so
//! no definition that elaborated before changes term. Every other placement
//! goes through the reordered call, and a reordered call that is not a
//! structural self-call is refused as the explicit spelling is refused; it
//! is never handed back to the method-dot path, which would compute a
//! different call. Before 2026-10-08 a receiver placed at position 0 always
//! kept the method-dot path, and a reordered call that declined fell back to
//! it: `def T.g (a : RAlias) (n : Nat) : T → Nat | .node l r => l.g a n + …`
//! with `@[reducible] def RAlias := T` (Lean: `T.g l a n`, a type mismatch)
//! was accepted as `T.g a n l`, and so was `def T.m2 (n : Nat) (a : T) : T →
//! Nat | .node l r => l.m2 (n + 1) a + 1` (Lean: "fail to show termination"
//! for `T.m2 (n + 1) l a`); and `l.g3 a r` in `def T.g3 (a : RAlias) (b : T)
//! : T → Nat`, which Lean accepts as `T.g3 l a r`, computed `T.g3 a r l`.

use super::ElabCtx;
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind};
use clean_parser::{Projection, SurfaceArg, SurfaceExpr, SurfaceName};

impl ElabCtx<'_> {
    /// `recv.f a₁ … aₙ` inside the structural definition of `T.f`, where
    /// `recv : T …` is a local: route it as `T.f a₁ … recv … aₙ` with the
    /// receiver at its `addLValArg` position. `Ok(None)` for every other
    /// shape, which keeps the ordinary path.
    pub(super) fn try_elab_recursive_dot_call(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        let Some(ctx) = self.recursive_def_ctx.as_ref() else {
            return Ok(None);
        };
        if self.explicit_mode || args.iter().any(|arg| arg.name.is_some()) {
            return Ok(None);
        }
        let SurfaceExpr::Proj(span, base, Projection::Named(field)) =
            Self::unwrap_surface_parens(func)
        else {
            return Ok(None);
        };
        let SurfaceExpr::Ident(_, recv) = Self::unwrap_surface_parens(base) else {
            return Ok(None);
        };
        let short = ctx.short_name();
        let decreasing = ctx.decreasing_arg_pos;
        let func_surface = ctx.func_name.clone();
        if field.name() != short.name() {
            return Ok(None);
        }
        let Some((_, recv_ty)) = self.lookup_local(recv) else {
            return Ok(None);
        };
        // The receiver's type head `T` names the namespace the field is looked
        // up in; the call is a self-call only when `T.f` IS the function being
        // defined (siblings of a fused fold keep their own envelope).
        let recv_ty = self.metas.instantiate(recv_ty);
        let func_name = ctx.func_name.name().clone();
        let Some(type_head) = [recv_ty.clone(), self.whnf(&recv_ty)]
            .iter()
            .find_map(|ty| match ty.get_app_fn().kind() {
                ExprKind::Const(head, _)
                    if crate::namespace::append_names(head, field.name()) == func_name =>
                {
                    Some(head.clone())
                }
                _ => None,
            })
        else {
            return Ok(None);
        };
        let Some(position) = self.dot_receiver_position(&type_head, args.len()) else {
            return Ok(None);
        };
        // The method-dot path computes the call with the receiver at the
        // decreasing position; only there is it Lean's call.
        if position == 0 && decreasing == 0 {
            return Ok(None);
        }
        let mut reordered = args.to_vec();
        reordered.insert(
            position,
            SurfaceArg {
                span: *span,
                expr: base.as_ref().clone(),
                name: None,
            },
        );
        match self.try_elab_recursive_call(&SurfaceExpr::Ident(*span, short), &reordered)? {
            Some(call) => Ok(Some(call)),
            // Lean elaborates exactly the reordered call. One that is not a
            // structural self-call is refused as its explicit spelling is
            // (`RecursionOutsideFragment`, with the miss the call recorded).
            None => Err(self.unknown_ident_error(&func_surface)),
        }
    }

    /// Where recursion DETECTION should place the receiver of a method-dot
    /// self-call of `name`, read off the surface binders before anything is
    /// elaborated: `addLValArg`'s explicit index of the first binder whose
    /// declared type is headed by the function's namespace `T` (`T.f`).
    ///
    /// Routing only — the call itself is placed by
    /// [`Self::try_elab_recursive_dot_call`] against the elaborated telescope,
    /// and the lowering resolves it or refuses. `None` (the legacy reading)
    /// for position 0, for an implicit first match (Lean then passes the
    /// receiver by name), and when no binder names `T`. The binder heads are
    /// read as written, not through `whnfR`, so a binder typed by a
    /// REDUCIBLE alias of `T` is skipped here although Lean places the
    /// receiver there. The call is still elaborated where Lean places it, or
    /// refused, never computed with the receiver elsewhere (pinned in
    /// `infer/tests/recursive_dot_call.rs`, as is the position-0 shape this
    /// reading cannot route).
    pub(super) fn method_dot_receiver_pos(
        &self,
        name: &SurfaceName,
        binders: &[clean_parser::SurfaceBinder],
    ) -> Option<usize> {
        fn head(ty: &SurfaceExpr) -> Option<&SurfaceName> {
            match ty {
                SurfaceExpr::Ident(_, name) => Some(name),
                SurfaceExpr::App(_, func, _) | SurfaceExpr::Paren(_, func) => head(func),
                _ => None,
            }
        }
        let namespace = self.qualify_name(name).parent();
        if namespace.is_anonymous() {
            return None;
        }
        let mut explicit_index = 0usize;
        for binder in binders
            .iter()
            .filter(|binder| !binder.name.is_section_variable())
        {
            let explicit = matches!(binder.info, clean_parser::SurfaceBinderInfo::Explicit);
            let names_namespace = binder
                .ty
                .as_deref()
                .and_then(head)
                .is_some_and(|head| !head.is_anonymous() && namespace.has_suffix(head));
            if names_namespace {
                return (explicit && explicit_index > 0).then_some(explicit_index);
            }
            if explicit {
                explicit_index += 1;
            }
        }
        None
    }

    /// Lean's `addLValArg` over the recorded declaration telescope: the
    /// own explicit-argument index of the first parameter whose type is an
    /// application of `type_head`, provided that parameter is explicit and the
    /// index does not pass the `supplied` positional arguments. `None` when the
    /// receiver would have to go in as a named argument (Lean's fallback) or no
    /// parameter fits. Captured section parameters are already applied to the
    /// internal recursive binding, so they do not consume receiver slots.
    ///
    /// A parameter's type matches as Lean 4.8.0's `typeMatchesBaseName`
    /// decides it: its head as written, else the head of its `whnfR`
    /// (REDUCIBLE transparency). A parameter typed by a semireducible alias of
    /// `T` is skipped there, so it is skipped here; default-transparency
    /// `whnf` matched it and placed the receiver where Lean does not.
    fn dot_receiver_position(&self, type_head: &Name, supplied: usize) -> Option<usize> {
        let ctx = self.recursive_def_ctx.as_ref()?;
        let mut explicit_index = 0usize;
        for param in ctx
            .parameters
            .iter()
            .filter(|param| !param.captured_section)
        {
            let ty = self.metas.instantiate(&param.type_);
            let head_is = |ty: &Expr| matches!(ty.get_app_fn().kind(), ExprKind::Const(head, _) if head == type_head);
            if head_is(&ty) || head_is(&self.whnf_reducible(&ty)) {
                return (param.binder_info == BinderInfo::Default && explicit_index <= supplied)
                    .then_some(explicit_index);
            }
            if param.binder_info == BinderInfo::Default {
                explicit_index += 1;
            }
        }
        None
    }
}
