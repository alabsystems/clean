// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What Lean asks of the recursive helper of a `partial` declaration before it
//! adds it as an opaque (`super` module docs).

use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Name};
use clean_parser::SurfaceName;

use crate::infer::ElabCtx;
use crate::ElabError;

impl ElabCtx<'_> {
    /// What Lean asks of a recursive helper of a `partial` declaration before
    /// it adds it as an opaque (`Lean/Elab/PreDefinition/Main.lean`): its type
    /// is a function (`invalid use of 'partial'`), and `mkInhabitantFor`
    /// (`MkInhabitant.lean`) finds an inhabitant of the result type under the
    /// parameters — an `Inhabited` instance, a parameter of that type, or an
    /// `Inhabited` function type over the trailing parameters; then the same
    /// with `Nonempty`. Clean only checks that one exists: the opaque carries
    /// the helper's own (kernel-checked) value, never a default.
    pub(super) fn check_partial_helper(&mut self, name: &Name, ty: &Expr) -> Result<(), ElabError> {
        if !matches!(self.whnf(ty).kind(), ExprKind::Pi(..)) {
            return Err(ElabError::Unsupported {
                feature: format!("invalid use of 'partial', '{name}' is not a function"),
            });
        }
        let snapshot = self.local_scope_snapshot();
        let metas = self.metas.clone();
        let mut params: Vec<(FVarId, BinderInfo, Expr)> = Vec::new();
        let mut result_ty = ty.clone();
        while let ExprKind::Pi(data, dom, body) = result_ty.kind() {
            let dom = (**dom).clone();
            let fvar = self.push_local(SurfaceName::from_name(Name::from_string("x")), dom.clone());
            if self.binder_is_local_instance(data.info, &dom) {
                self.push_local_instance(fvar, dom.clone());
            }
            let next = body.instantiate(&Expr::fvar(fvar));
            params.push((fvar, data.info, dom));
            result_ty = next;
        }
        let inhabited = ["Inhabited", "Nonempty"]
            .into_iter()
            .any(|class| self.inhabitant_exists(class, &params, &result_ty));
        self.metas = metas;
        self.restore_local_scope(snapshot, true);
        if inhabited {
            Ok(())
        } else {
            Err(ElabError::FailedToSynthesizeInstance {
                goal: format!(
                    "Inhabited or Nonempty of the result type of `{name}` (Lean: failed to \
                     compile partial definition '{name}', failed to show that type is \
                     inhabited and non empty)"
                ),
                detail: String::new(),
            })
        }
    }

    /// One `go?` round of `mkInhabitantFor` for `class` (`Inhabited`, then
    /// `Nonempty`), over the opened parameters `params` and result `ty`.
    fn inhabitant_exists(
        &mut self,
        class: &str,
        params: &[(FVarId, BinderInfo, Expr)],
        ty: &Expr,
    ) -> bool {
        if self.class_instance_exists(class, ty) {
            return true;
        }
        // `findAssumption?`
        if params.iter().any(|(_, _, dom)| self.is_def_eq(dom, ty)) {
            return true;
        }
        // `mkFnInhabitant?`: the result type over ever more trailing
        // parameters.
        let mut fn_ty = ty.clone();
        for (fvar, info, dom) in params.iter().rev() {
            fn_ty = Expr::pi(*info, dom.clone(), fn_ty.abstract_fvar(*fvar));
            if self.class_instance_exists(class, &fn_ty) {
                return true;
            }
        }
        false
    }

    /// Whether instance resolution finds `class ty` (`class.{u} : Sort u →
    /// …`).
    fn class_instance_exists(&mut self, class: &str, ty: &Expr) -> bool {
        let Ok(level) = self.infer_sort(ty) else {
            return false;
        };
        let goal = Expr::app(
            Expr::const_(Name::from_string(class), vec![level]),
            ty.clone(),
        );
        self.resolve_instance(&goal).is_some()
    }
}
