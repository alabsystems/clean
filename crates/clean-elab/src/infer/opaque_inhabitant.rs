// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The inhabitant Lean requires before it declares an `opaque` constant or a
//! `partial def` (`Lean/Elab/PreDefinition/MkInhabitant.lean`,
//! `mkInhabitantFor`).
//!
//! Both are axioms to the kernel (a body-less `opaque` registers as one; a
//! `partial def` keeps only its signature), so an uninhabited type would make
//! the declaration a proof of it: `opaque o : False` was accepted, by `clean
//! check` and by `clean lean` (exit 0), where pinned Lean 4.8.0 and
//! 4.30.0-rc2 both refuse "failed to synthesize Inhabited False" (review r6,
//! X9; docs/DECISIONS.md R134). The declaration's HEADER binders are opened as
//! locals, the class-typed ones as local instances, so `opaque f (n : Nat) :
//! Fin (n+1)` asks for `Inhabited (Fin (n+1))` with `n` in scope and `opaque f
//! (α : Type) [Inhabited α] : α` is served by its own binder; the binders of
//! the type after the colon stay a function type, as in Lean.

use super::lean_init_inhabited::LeanInhabited;
use super::ElabCtx;
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};
use clean_parser::SurfaceName;

/// Which class inhabited the type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum OpaqueInhabitant {
    /// `Inhabited`: Lean's inhabitant is `default`, which has code.
    Inhabited,
    /// Only `Nonempty`: Lean's inhabitant is `Classical.ofNonempty`.
    Nonempty,
}

impl ElabCtx<'_> {
    /// Require an `Inhabited` (or, when `allow_nonempty`, a `Nonempty`)
    /// instance of `ty` past its first `header_binders` binders, which are
    /// opened as locals (a class-typed one as a local instance, as every local
    /// is in Lean). The binders of the type after the colon are NOT opened:
    /// Lean asks for `Inhabited ((α : Type) → [Inhabited α] → α)` there, and
    /// refuses it (review r6 fix round). Clean's own instance search is tried
    /// first, then the instances both pinned Leans' `Init` have
    /// ([`super::lean_init_inhabited`]). `label` names the declaration.
    ///
    /// # Errors
    ///
    /// [`ElabError::FailedToSynthesizeInstance`] when no instance is found.
    pub(super) fn require_opaque_inhabitant(
        &mut self,
        label: &str,
        ty: &Expr,
        header_binders: usize,
        allow_nonempty: bool,
    ) -> Result<OpaqueInhabitant, ElabError> {
        let saved_locals = self.locals.len();
        let mut pushed_instances = 0usize;
        let mut result_ty = self.metas.instantiate(ty);
        for opened in 0..header_binders as u64 {
            let current = result_ty.clone();
            let ExprKind::Pi(binder, dom, body) = current.kind() else {
                break;
            };
            let dom = dom.as_ref().clone();
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(
                SurfaceName::unspellable("__opaque_param", opened),
                fvar,
                dom.clone(),
            );
            if self.binder_is_local_instance(binder.info, &dom) {
                self.push_local_instance(fvar, dom);
                pushed_instances += 1;
            }
            result_ty = body.instantiate(&Expr::fvar(fvar));
        }
        let found = self.find_inhabitant(&result_ty, allow_nonempty);
        let failure = found.is_none().then(|| {
            let level = self
                .infer_sort(&result_ty)
                .unwrap_or_else(|_| Level::succ(Level::zero()));
            let goal = Expr::app(
                Expr::const_(Name::from_string("Inhabited"), vec![level]),
                result_ty.clone(),
            );
            ElabError::FailedToSynthesizeInstance {
                goal: format!(
                    "Inhabited{} {} (required to declare `{label}`: its type must be inhabited)",
                    if allow_nonempty { " or Nonempty" } else { "" },
                    crate::error_render::term(&result_ty)
                ),
                detail: self.instance_failure_detail(&goal),
            }
        });
        for _ in 0..pushed_instances {
            self.pop_local_instance();
        }
        self.locals.truncate(saved_locals);
        match (found, failure) {
            (Some(inhabitant), _) => Ok(inhabitant),
            (None, Some(error)) => Err(error),
            (None, None) => Err(ElabError::InternalInvariant(format!(
                "`{label}`: inhabitant search failed without a failure"
            ))),
        }
    }

    /// `Inhabited ty`, by Clean's instance search or as both pinned Leans'
    /// `Init` has it, else (when allowed) `Nonempty ty`.
    fn find_inhabitant(&mut self, ty: &Expr, allow_nonempty: bool) -> Option<OpaqueInhabitant> {
        let level = self.infer_sort(ty).ok()?;
        let class_goal = |class: &str| {
            Expr::app(
                Expr::const_(Name::from_string(class), vec![level.clone()]),
                ty.clone(),
            )
        };
        if self.resolve_instance(&class_goal("Inhabited")).is_some()
            || self.lean_init_inhabited(ty) == LeanInhabited::Yes
        {
            return Some(OpaqueInhabitant::Inhabited);
        }
        (allow_nonempty && self.nonempty_through_pis(ty, 0)).then_some(OpaqueInhabitant::Nonempty)
    }

    /// `Nonempty ty` by Clean's instance search, read through `ty`'s function
    /// binders as both Leans' `instance [∀ a, Nonempty (β a)] : Nonempty (∀ a,
    /// β a)` does: the codomain under plain locals, which are NOT local
    /// instances (only a declaration's header binders are).
    fn nonempty_through_pis(&mut self, ty: &Expr, depth: u64) -> bool {
        let ty = self.metas.instantiate(ty);
        if let ExprKind::Pi(_, dom, body) = ty.kind() {
            if depth > 32 {
                return false;
            }
            let saved = self.locals.len();
            let fvar = self.fresh_fvar();
            self.push_local_with_fvar(
                SurfaceName::unspellable("__opaque_nonempty", depth),
                fvar,
                dom.as_ref().clone(),
            );
            let found = self.nonempty_through_pis(&body.instantiate(&Expr::fvar(fvar)), depth + 1);
            self.locals.truncate(saved);
            return found;
        }
        let Ok(level) = self.infer_sort(&ty) else {
            return false;
        };
        let goal = Expr::app(
            Expr::const_(Name::from_string("Nonempty"), vec![level]),
            ty.clone(),
        );
        self.resolve_instance(&goal).is_some()
    }
}
