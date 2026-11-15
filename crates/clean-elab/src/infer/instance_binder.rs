// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean's `elabBinderViews` annotation check, distinct from lambda binders.

use super::*;

enum ClassQuickResult {
    Class,
    NotClass,
    Reduce,
}

impl<'a> ElabCtx<'a> {
    /// Lean's `isClassQuick?` rejects free-variable heads before WHNF,
    /// including local definitions whose values happen to be class types.
    fn instance_annotation_class_quick(&self, ty: &Expr) -> ClassQuickResult {
        let mut current = ty;
        loop {
            match current.kind() {
                ExprKind::Pi(_, _, body) | ExprKind::MData(_, body) => current = body,
                ExprKind::Const(name, _) => return self.instance_annotation_class_const(name),
                ExprKind::App(..) => {
                    return match current.get_app_fn().kind() {
                        ExprKind::Const(name, _) => self.instance_annotation_class_const(name),
                        ExprKind::Lam(..) => ClassQuickResult::Reduce,
                        _ => ClassQuickResult::NotClass,
                    };
                }
                ExprKind::Let(..) | ExprKind::Proj(..) => return ClassQuickResult::Reduce,
                _ => return ClassQuickResult::NotClass,
            }
        }
    }

    fn instance_annotation_class_const(&self, name: &Name) -> ClassQuickResult {
        if self.head_is_class(name) {
            ClassQuickResult::Class
        } else if self.env.get_const(name).is_some_and(|info| {
            info.kind == clean_kernel::env::ConstantKind::Definition && info.value.is_some()
        }) {
            ClassQuickResult::Reduce
        } else {
            ClassQuickResult::NotClass
        }
    }

    fn instance_annotation_is_class(&self, ty: &Expr) -> bool {
        match self.instance_annotation_class_quick(ty) {
            ClassQuickResult::Class => true,
            ClassQuickResult::NotClass => false,
            ClassQuickResult::Reduce => {
                let mut conclusion = ty.clone();
                loop {
                    conclusion = self.whnf_reducible(&conclusion);
                    if let ExprKind::Pi(_, _, body) = conclusion.kind() {
                        conclusion = body.as_ref().clone();
                    } else {
                        break;
                    }
                }
                crate::instances::extract_class_app(&conclusion)
                    .is_some_and(|(head, _)| self.head_is_class(&head))
            }
        }
    }

    /// Check a header's bracketed binder after ordinary type elaboration.
    /// Lean's `elabFunBinderViews` deliberately does not perform this check.
    pub(super) fn check_instance_binder_annotation(
        &mut self,
        info: SurfaceBinderInfo,
        ty: &Expr,
    ) -> Result<(), ElabError> {
        if info != SurfaceBinderInfo::Instance
            || matches!(self.get_option("checkBinderAnnotations"), Some(Some(value)) if value == "false")
        {
            return Ok(());
        }

        let mut conclusion = self.metas.instantiate_levels(&self.metas.instantiate(ty));
        if !self.instance_annotation_is_class(&conclusion) {
            return Err(ElabError::InvalidInstanceBinder {
                type_: ty.to_string(),
            });
        }
        let mut unused_parameter = None;
        loop {
            // Lean's subsequent `checkLocalInstanceParameters` uses ordinary
            // WHNF, separately from reducible class-head recognition above.
            conclusion = self.whnf(&conclusion);
            if let ExprKind::Pi(binder, domain, body) = conclusion.kind() {
                // Lean permits an unused INSTANCE parameter: resolution can
                // synthesize it. Every other parameter must occur forward.
                if binder.info != BinderInfo::InstImplicit
                    && !body.has_loose_bvar(0)
                    && unused_parameter.is_none()
                {
                    unused_parameter = Some(domain.to_string());
                }
                conclusion = body.as_ref().clone();
            } else {
                break;
            }
        }
        if let Some(type_) = unused_parameter {
            return Err(ElabError::InvalidParametricLocalInstance { type_ });
        }
        Ok(())
    }
}
