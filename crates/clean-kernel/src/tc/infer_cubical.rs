// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cubical mode type inference helpers.
//!
//! Extracted from `infer.rs` (#2594) — no logic changes.
//! Each method is the verbatim body of a cubical `ExprKind` match arm
//! from `infer_type_fast_inner`.

#[cfg(not(debug_assertions))]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(not(debug_assertions))]
use crate::level::Level;
use crate::tc::TypeChecker;
#[cfg(not(debug_assertions))]
use crate::tc::TypeError;
#[cfg(not(debug_assertions))]
use std::sync::Arc;

impl<'env> TypeChecker<'env> {
    /// Infer `CubicalInterval : Sort(Type)`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_interval(&self) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalInterval".to_string(),
                mode: "Cubical".to_string(),
            });
        }
        // The interval I is a type with two elements (i0, i1), so it lives in Type
        Ok(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))))
    }

    /// Infer `CubicalI0 | CubicalI1 : CubicalInterval`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_endpoint(&self) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalI0/CubicalI1".to_string(),
                mode: "Cubical".to_string(),
            });
        }
        Ok(Expr::from_kind(ExprKind::CubicalInterval))
    }

    /// Infer the type of `CubicalPath { ty, left, right }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_path(
        &self,
        ty: &Arc<Expr>,
        left: &Arc<Expr>,
        right: &Arc<Expr>,
    ) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalPath".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        // ty : I -> Sort(l)
        let ty_type = self.infer_type_fast_impl(ty)?;
        let ty_type_whnf = self.whnf_impl(&ty_type);
        let ExprKind::Pi(_, arg_ty, body_ty) = &ty_type_whnf.kind else {
            return Err(TypeError::NotAFunction {
                ty: Box::new(ty_type),
                location: None,
            });
        };
        let arg_ty = arg_ty.clone();
        let body_ty = body_ty.clone();
        if !matches!(self.whnf_impl(&arg_ty).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(Expr::from_kind(ExprKind::CubicalInterval)),
                inferred: Box::new(arg_ty.as_ref().clone()),
                location: None,
            });
        }
        let body_ty_whnf = self.whnf_impl(&body_ty);
        let ExprKind::Sort(level) = &body_ty_whnf.kind else {
            return Err(TypeError::ExpectedSort {
                ty: Box::new(body_ty.as_ref().clone()),
                location: None,
            });
        };
        let level = level.clone();

        // left : ty 0, right : ty 1
        let expected_left_ty = Expr::from_kind(ExprKind::App(
            ty.clone(),
            Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
        ));
        let left_ty = self.infer_type_fast_impl(left)?;
        if !self.is_def_eq(&left_ty, &expected_left_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_left_ty),
                inferred: Box::new(left_ty),
                location: None,
            });
        }

        let expected_right_ty = Expr::from_kind(ExprKind::App(
            ty.clone(),
            Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
        ));
        let right_ty = self.infer_type_fast_impl(right)?;
        if !self.is_def_eq(&right_ty, &expected_right_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_right_ty),
                inferred: Box::new(right_ty),
                location: None,
            });
        }

        Ok(Expr::from_kind(ExprKind::Sort(level)))
    }

    /// Infer the type of `CubicalPathLam { body }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_path_lam(&self, body: &Arc<Expr>) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalPathLam".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        // Add interval variable to context and infer body type
        let fvar_id = self.ctx_push(
            crate::name::Name::anon(),
            Expr::from_kind(ExprKind::CubicalInterval),
            BinderInfo::Default,
        );
        let body_with_fvar = self.open_bvar(body, fvar_id);
        let body_type = self.infer_type_fast_impl(&body_with_fvar)?;
        self.ctx_pop();

        // Build Path type: Path (λ i : I, body_type) (body[0]) (body[1])
        let left = body.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        let right = body.instantiate(&Expr::from_kind(ExprKind::CubicalI1));
        let body_type_abstract = body_type.abstract_fvar(fvar_id);
        let ty_family = Expr::from_kind(ExprKind::Lam(
            BinderInfo::Default.into(),
            Arc::new(Expr::from_kind(ExprKind::CubicalInterval)),
            Arc::new(body_type_abstract),
        ));
        Ok(Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(ty_family),
            left: Arc::new(left),
            right: Arc::new(right),
        }))
    }

    /// Infer the type of `CubicalPathApp { path, arg }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_path_app(
        &self,
        path: &Arc<Expr>,
        arg: &Arc<Expr>,
    ) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalPathApp".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        let path_type = self.infer_type_fast_impl(path)?;
        let path_type_whnf = self.whnf_impl(&path_type);
        let ExprKind::CubicalPath { ty, .. } = &path_type_whnf.kind else {
            return Err(TypeError::NotAFunction {
                ty: Box::new(path_type),
                location: None,
            });
        };
        let ty = ty.clone();
        let arg_type = self.infer_type_fast_impl(arg)?;
        if !matches!(self.whnf_impl(&arg_type).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(Expr::from_kind(ExprKind::CubicalInterval)),
                inferred: Box::new(arg_type),
                location: None,
            });
        }

        Ok(Expr::from_kind(ExprKind::App(ty, arg.clone())))
    }

    /// Infer the type of `CubicalHComp { ty, phi, u, base }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_hcomp(
        &self,
        ty: &Arc<Expr>,
        phi: &Arc<Expr>,
        u: &Arc<Expr>,
        base: &Arc<Expr>,
    ) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalHComp".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        let ty_sort = self.infer_type_fast_impl(ty)?;
        if !matches!(self.whnf_impl(&ty_sort).kind, ExprKind::Sort(_)) {
            return Err(TypeError::ExpectedSort {
                ty: Box::new(ty_sort),
                location: None,
            });
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let i0 = Expr::from_kind(ExprKind::CubicalI0);
        let i1 = Expr::from_kind(ExprKind::CubicalI1);

        let phi_ty = self.infer_type_fast_impl(phi)?;
        if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval.clone()),
                inferred: Box::new(phi_ty),
                location: None,
            });
        }

        let u_ty = self.infer_type_fast_impl(u)?;
        let u_ty_whnf = self.whnf_impl(&u_ty);
        let ExprKind::Pi(_, domain, codomain) = &u_ty_whnf.kind else {
            return Err(TypeError::NotAFunction {
                ty: Box::new(u_ty),
                location: None,
            });
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval.clone()),
                inferred: Box::new((**domain).clone()),
                location: None,
            });
        }

        let codomain_i0 = codomain.instantiate(&i0);
        if !self.is_def_eq(&codomain_i0, ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                inferred: Box::new(codomain_i0),
                location: None,
            });
        }
        let codomain_i1 = codomain.instantiate(&i1);
        if !self.is_def_eq(&codomain_i1, ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                inferred: Box::new(codomain_i1),
                location: None,
            });
        }

        let base_ty = self.infer_type_fast_impl(base)?;
        if !self.is_def_eq(&base_ty, ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                inferred: Box::new(base_ty),
                location: None,
            });
        }

        // Multi-branch system well-formedness: overlapping faces must agree
        // (Deliverable A). Subsumes the legacy single-branch case (no overlap).
        self.validate_hcomp_system(phi, u, ty)?;
        // Cap / floor-agreement (CCHM well-formedness): on every active face φᵢ,
        // the tube's i0-end must match the floor — `uᵢ i0 ≡ base` on φᵢ. This is
        // the side condition every `hcomp` reduction rule assumes; without it a
        // floor-disagreeing hcomp inhabits e.g. `Path Nat 0 1` (a soundness hole).
        self.validate_hcomp_cap(phi, u, base)?;

        Ok(ty.as_ref().clone())
    }

    /// Infer the type of `CubicalTransp { ty, phi, base }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_transp(
        &self,
        ty: &Arc<Expr>,
        phi: &Arc<Expr>,
        base: &Arc<Expr>,
    ) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalTransp".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let i0 = Arc::new(Expr::from_kind(ExprKind::CubicalI0));
        let i1 = Arc::new(Expr::from_kind(ExprKind::CubicalI1));

        let ty_ty = self.infer_type_fast_impl(ty)?;
        let ty_ty_whnf = self.whnf_impl(&ty_ty);
        let ExprKind::Pi(_, domain, codomain_sort) = &ty_ty_whnf.kind else {
            return Err(TypeError::NotAFunction {
                ty: Box::new(ty_ty),
                location: None,
            });
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval.clone()),
                inferred: Box::new((**domain).clone()),
                location: None,
            });
        }
        let codomain_sort_i0 = codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
            return Err(TypeError::ExpectedSort {
                ty: Box::new(codomain_sort_i0),
                location: None,
            });
        }

        let phi_ty = self.infer_type_fast_impl(phi)?;
        if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval),
                inferred: Box::new(phi_ty),
                location: None,
            });
        }

        let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), i0));
        let base_ty = self.infer_type_fast_impl(base)?;
        if !self.is_def_eq(&base_ty, &expected_base_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_base_ty),
                inferred: Box::new(base_ty),
                location: None,
            });
        }

        Ok(Expr::from_kind(ExprKind::App(ty.clone(), i1)))
    }

    /// Infer the type of `CubicalCoe { ty, r, s, base }`.
    ///
    /// ```text
    /// ty : I → Sort u    r : I    s : I    base : ty r
    /// ───────────────────────────────────────────────
    ///            coe ty r s base : ty s
    /// ```
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_cubical_coe(
        &self,
        ty: &Arc<Expr>,
        r: &Arc<Expr>,
        s: &Arc<Expr>,
        base: &Arc<Expr>,
    ) -> Result<Expr, TypeError> {
        if !self.mode.has_cubical_layer() {
            return Err(TypeError::ModeRequired {
                feature: "CubicalCoe".to_string(),
                mode: "Cubical".to_string(),
            });
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);

        // ty : I → Sort u  (a line of types).
        let ty_ty = self.infer_type_fast_impl(ty)?;
        let ty_ty_whnf = self.whnf_impl(&ty_ty);
        let ExprKind::Pi(_, domain, codomain_sort) = &ty_ty_whnf.kind else {
            return Err(TypeError::NotAFunction {
                ty: Box::new(ty_ty),
                location: None,
            });
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval.clone()),
                inferred: Box::new((**domain).clone()),
                location: None,
            });
        }
        let codomain_sort_i0 = codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
            return Err(TypeError::ExpectedSort {
                ty: Box::new(codomain_sort_i0),
                location: None,
            });
        }

        // r : I
        let r_ty = self.infer_type_fast_impl(r)?;
        if !matches!(self.whnf_impl(&r_ty).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval.clone()),
                inferred: Box::new(r_ty),
                location: None,
            });
        }
        // s : I
        let s_ty = self.infer_type_fast_impl(s)?;
        if !matches!(self.whnf_impl(&s_ty).kind, ExprKind::CubicalInterval) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(interval),
                inferred: Box::new(s_ty),
                location: None,
            });
        }

        // base : ty r
        let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), r.clone()));
        let base_ty = self.infer_type_fast_impl(base)?;
        if !self.is_def_eq(&base_ty, &expected_base_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_base_ty),
                inferred: Box::new(base_ty),
                location: None,
            });
        }

        // Result: ty s
        Ok(Expr::from_kind(ExprKind::App(ty.clone(), s.clone())))
    }
}
