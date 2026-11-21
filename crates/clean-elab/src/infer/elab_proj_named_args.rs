// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain a resolved method's full telescope while positioning named arguments.
//! Lean's addLValArg skips parameters explicitly supplied by name before placing
//! the already elaborated receiver in the next parameter of the namespace type.

use super::*;

pub(super) struct NamedDotReceiver {
    pub(super) term: Expr,
    pub(super) namespace: Name,
}

/// The final field of an application can report the already elaborated
/// receiver for named arguments or its generated positional lambda prefix.
pub(super) enum DotHeadCapture {
    Named(Option<NamedDotReceiver>),
    Positional { generated_binders: usize },
}

impl ElabCtx<'_> {
    pub(super) fn apply_or_capture_dot_receiver(
        &mut self,
        method: Expr,
        ty: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
        namespace: &Name,
        mut capture: Option<&mut DotHeadCapture>,
    ) -> Result<Expr, ElabError> {
        if let (Some(DotHeadCapture::Named(capture)), ExprKind::Const(name, _)) =
            (capture.as_deref_mut(), method.kind())
        {
            // Recursors have their own motive/major-premise elaboration rules.
            if !self.is_dot_recursor_family_member(name, namespace) {
                *capture = Some(NamedDotReceiver {
                    term: receiver.clone(),
                    namespace: namespace.clone(),
                });
                return Ok(method);
            }
        }
        self.apply_dot_receiver(method, ty, receiver, receiver_ty, namespace, capture)
    }

    /// Lean's `typeMatchesBaseName` looks through reducible and instance heads.
    /// Test each alias before its next delta step so an intermediate namespace
    /// still selects its parameter. An ordinary definition is not an alias here.
    pub(super) fn dot_parameter_matches_namespace(
        &self,
        domain: &Expr,
        namespace: &Name,
    ) -> Result<bool, ElabError> {
        if namespace == &Name::from_string("Function") {
            return Ok(matches!(
                self.whnf_instances(domain).kind(),
                ExprKind::Pi(..)
            ));
        }
        let mut current = self.metas.instantiate(domain);
        for _ in 0..64 {
            let ExprKind::Const(name, levels) = current.get_app_fn().kind() else {
                return Ok(
                    matches!(self.whnf_instances(&current).get_app_fn().kind(), ExprKind::Const(head, _) if head == namespace),
                );
            };
            if name == namespace {
                return Ok(true);
            }
            let value = self.env.unfold_with_transparency(
                name,
                levels,
                clean_kernel::TransparencyMode::Instances,
            );
            let Some(value) = value else {
                return Ok(
                    matches!(self.whnf_instances(&current).get_app_fn().kind(), ExprKind::Const(head, _) if head == namespace),
                );
            };
            let args = current.get_app_args().into_iter().cloned();
            current = crate::tactic::op_projection::head_beta(&Expr::apps(value, args));
        }
        Err(ElabError::Unsupported {
            feature: format!("field parameter alias chain exceeded 64 steps for {namespace}"),
        })
    }

    pub(super) fn named_dot_receiver_slot(
        &mut self,
        function: &Expr,
        receiver: &NamedDotReceiver,
        slots: &[(Option<SurfaceName>, Option<BinderInfo>)],
        occupied: &[Option<SurfaceArg>],
        positional: usize,
        trailing_ellipsis: bool,
    ) -> Result<(usize, Vec<BinderInfo>), ElabError> {
        let ty = self.infer_type(function)?;
        let mut ty = self.whnf(&ty);
        self.metas.push_scope();
        let mut position = 0;
        let mut kinds = Vec::new();
        let mut found = None;
        while let ExprKind::Pi(binder, domain, body) = ty.kind() {
            let index = kinds.len();
            kinds.push(binder.info);
            let explicit = self.explicit_mode || binder.info == BinderInfo::Default;
            if found.is_none() && !occupied.get(index).is_some_and(Option::is_some) {
                let matches_namespace =
                    match self.dot_parameter_matches_namespace(domain, &receiver.namespace) {
                        Ok(value) => value,
                        Err(error) => {
                            self.metas.pop_scope();
                            return Err(error);
                        }
                    };
                if matches_namespace {
                    let name = slots.get(index).and_then(|(name, _)| name.as_ref());
                    let unique_name = name.is_some_and(|n| {
                        !n.name().is_anon()
                            && !slots[..index]
                                .iter()
                                .any(|(earlier, _)| earlier.as_ref() == Some(n))
                    });
                    if (explicit && position <= positional) || unique_name {
                        found = Some(index);
                    }
                    if found.is_none() || !trailing_ellipsis {
                        break;
                    }
                }
                position += usize::from(explicit);
            }
            // Open dependent domains without assigning any speculative argument
            // to the actual method application or polluting later inference.
            let placeholder = self.fresh_meta(domain.as_ref().clone());
            ty = self.whnf(&body.instantiate(&placeholder));
        }
        self.metas.pop_scope();
        found
            .map(|index| (index, kinds))
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!(
                    "field notation on {function} has no usable receiver parameter of type {}",
                    receiver.namespace
                ),
            })
    }
}
