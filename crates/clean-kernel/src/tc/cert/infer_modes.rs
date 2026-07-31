// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mode-specific type inference with certificates.
//!
//! Handles Cubical, SetTheoretic (ZFC), and Impredicative mode expression kinds.
//! Called from `infer_core.rs` when a mode-specific ExprKind is encountered.

use std::sync::Arc;

use crate::cert::ProofCert;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::tc::TypeChecker;
use crate::TypeError;

use super::convert_fvar_cert_to_bvar;

impl<'env> TypeChecker<'env> {
    /// Infer type with certificate for mode-specific expression kinds.
    pub(crate) fn infer_mode_specific_cert(
        &self,
        e: &Expr,
    ) -> Result<(Expr, ProofCert), TypeError> {
        match &e.kind {
            // Cubical mode expressions
            ExprKind::CubicalInterval => {
                // I : IType (special sort)
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalInterval".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }
                // In Cubical mode, I is a type with two elements (i0, i1)
                let cert = ProofCert::CubicalInterval;
                Ok((
                    Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                    cert,
                ))
            }
            ExprKind::CubicalI0 | ExprKind::CubicalI1 => {
                // 0, 1 : I
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalI0/CubicalI1".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }
                // Type is the interval I
                let ty = Expr::from_kind(ExprKind::CubicalInterval);
                let cert = ProofCert::CubicalEndpoint {
                    is_one: matches!(e.kind, ExprKind::CubicalI1),
                };
                Ok((ty, cert))
            }
            ExprKind::CubicalPath { ty, left, right } => {
                // Path A a b : Type
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalPath".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }
                // Check ty is a type family over the interval: ty : I -> Sort(l)
                let (ty_type, ty_cert) = self.infer_type_with_cert_impl(ty)?;
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

                // Check endpoints: left : ty 0 and right : ty 1
                let expected_left_ty = Expr::from_kind(ExprKind::App(
                    ty.clone(),
                    Arc::new(ExprKind::CubicalI0.into()),
                ));
                let (left_ty, left_cert) = self.infer_type_with_cert_impl(left)?;
                if !self.is_def_eq(&left_ty, &expected_left_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_left_ty),
                        inferred: Box::new(left_ty),
                        location: None,
                    });
                }

                let expected_right_ty = Expr::from_kind(ExprKind::App(
                    ty.clone(),
                    Arc::new(ExprKind::CubicalI1.into()),
                ));
                let (right_ty, right_cert) = self.infer_type_with_cert_impl(right)?;
                if !self.is_def_eq(&right_ty, &expected_right_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_right_ty),
                        inferred: Box::new(right_ty),
                        location: None,
                    });
                }

                // Path types live at the same universe level as their type family codomain.
                let result_ty = Expr::from_kind(ExprKind::Sort(level.clone()));
                let cert = ProofCert::CubicalPath {
                    ty_cert: Box::new(ty_cert),
                    ty_level: level,
                    left_cert: Box::new(left_cert),
                    right_cert: Box::new(right_cert),
                };
                Ok((result_ty, cert))
            }
            ExprKind::CubicalPathLam { body } => {
                // <i> e : Path A (e[0/i]) (e[1/i])
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
                let body_result = self.infer_type_with_cert_impl(&body_with_fvar);
                // Pop BEFORE `?` so an Err leaves self.ctx unchanged.
                self.ctx_pop();
                let (body_type, body_cert_raw) = body_result?;

                // Convert FVar certificates back to BVar certificates for the body
                let body_cert = convert_fvar_cert_to_bvar(body_cert_raw, fvar_id, 0);

                // The result is a Path type, with a type family λ i : I, body_type
                let left = body.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
                let right = body.instantiate(&Expr::from_kind(ExprKind::CubicalI1));
                let body_type_abstract = body_type.abstract_fvar(fvar_id);
                let ty_family = Expr::from_kind(ExprKind::Lam(
                    BinderInfo::Default.into(),
                    Arc::new(Expr::from_kind(ExprKind::CubicalInterval)),
                    Arc::new(body_type_abstract.clone()),
                ));
                let result_ty = Expr::from_kind(ExprKind::CubicalPath {
                    ty: Arc::new(ty_family),
                    left: Arc::new(left),
                    right: Arc::new(right),
                });
                let cert = ProofCert::CubicalPathLam {
                    body_cert: Box::new(body_cert),
                    body_type: Box::new(body_type_abstract),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }
            ExprKind::CubicalPathApp { path, arg } => {
                // p @ i : A (when p : Path A a b and i : I)
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalPathApp".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }
                // Check path has Path type
                let (path_type, path_cert) = self.infer_type_with_cert_impl(path)?;
                let path_type_whnf = self.whnf_impl(&path_type);
                let ExprKind::CubicalPath { ty, .. } = &path_type_whnf.kind else {
                    return Err(TypeError::NotAFunction {
                        ty: Box::new(path_type),
                        location: None,
                    });
                };
                let ty = ty.clone();
                // Check arg has interval type
                let (arg_type, arg_cert) = self.infer_type_with_cert_impl(arg)?;
                if !matches!(self.whnf_impl(&arg_type).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(Expr::from_kind(ExprKind::CubicalInterval)),
                        inferred: Box::new(arg_type),
                        location: None,
                    });
                }
                // Result is the path's type family applied to the interval point
                let result_ty = Expr::from_kind(ExprKind::App(ty.clone(), arg.clone()));
                let cert = ProofCert::CubicalPathApp {
                    path_cert: Box::new(path_cert),
                    arg_cert: Box::new(arg_cert),
                    path_type: Box::new(path_type_whnf.clone()),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                // hcomp {A} {φ} u base : A
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalHComp".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }
                // Simplified: check ty is a type
                let (ty_sort, ty_cert) = self.infer_type_with_cert_impl(ty)?;
                let ty_sort_whnf = self.whnf_impl(&ty_sort);
                if !matches!(ty_sort_whnf.kind, ExprKind::Sort(_)) {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(ty_sort),
                        location: None,
                    });
                }

                let interval = Expr::from_kind(ExprKind::CubicalInterval);
                let i0 = Expr::from_kind(ExprKind::CubicalI0);
                let i1 = Expr::from_kind(ExprKind::CubicalI1);

                let (phi_ty, phi_cert) = self.infer_type_with_cert_impl(phi)?;
                if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(interval.clone()),
                        inferred: Box::new(phi_ty),
                        location: None,
                    });
                }

                let (u_ty, u_cert) = self.infer_type_with_cert_impl(u)?;
                let u_ty_whnf = self.whnf_impl(&u_ty);
                let ExprKind::Pi(_, domain, codomain) = &u_ty_whnf.kind else {
                    return Err(TypeError::NotAFunction {
                        ty: Box::new(u_ty),
                        location: None,
                    });
                };
                if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(interval),
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

                let (base_ty, base_cert) = self.infer_type_with_cert_impl(base)?;
                if !self.is_def_eq(&base_ty, ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(ty.as_ref().clone()),
                        inferred: Box::new(base_ty),
                        location: None,
                    });
                }
                // Multi-branch system well-formedness: overlapping faces must
                // agree (Deliverable A). Mirrors the release `infer_cubical_hcomp`.
                self.validate_hcomp_system(phi, u, ty)?;
                // Cap / floor-agreement (CCHM well-formedness): `uᵢ i0 ≡ base` on
                // every active face φᵢ — the side condition every `hcomp` reduction
                // rule assumes. Without it a floor-disagreeing hcomp inhabits e.g.
                // `Path Nat 0 1` (a soundness hole). Mirrors `infer_cubical_hcomp`.
                self.validate_hcomp_cap(phi, u, base)?;
                let result_ty = ty.as_ref().clone();
                let cert = ProofCert::CubicalHComp {
                    ty_cert: Box::new(ty_cert),
                    phi_cert: Box::new(phi_cert),
                    u_cert: Box::new(u_cert),
                    base_cert: Box::new(base_cert),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                // transp A φ base : A 1
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalTransp".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }

                let interval = Expr::from_kind(ExprKind::CubicalInterval);
                let i0 = Arc::new(Expr::from_kind(ExprKind::CubicalI0));
                let i1 = Arc::new(Expr::from_kind(ExprKind::CubicalI1));

                // Check ty : I -> Sort u
                let (ty_ty, ty_cert) = self.infer_type_with_cert_impl(ty)?;
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
                let codomain_sort_i0 =
                    codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
                if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(codomain_sort_i0),
                        location: None,
                    });
                }

                // Check phi : I
                let (phi_ty, phi_cert) = self.infer_type_with_cert_impl(phi)?;
                if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(interval),
                        inferred: Box::new(phi_ty),
                        location: None,
                    });
                }

                // Check base : ty i0
                let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), i0.clone()));
                let (base_ty, base_cert) = self.infer_type_with_cert_impl(base)?;
                if !self.is_def_eq(&base_ty, &expected_base_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_base_ty),
                        inferred: Box::new(base_ty),
                        location: None,
                    });
                }

                // Result type is ty applied to i1
                let result_ty = Expr::from_kind(ExprKind::App(ty.clone(), i1));
                let cert = ProofCert::CubicalTransp {
                    ty_cert: Box::new(ty_cert),
                    phi_cert: Box::new(phi_cert),
                    base_cert: Box::new(base_cert),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                // coe A r s base : A s
                if !self.mode.has_cubical_layer() {
                    return Err(TypeError::ModeRequired {
                        feature: "CubicalCoe".to_string(),
                        mode: "Cubical".to_string(),
                    });
                }

                let interval = Expr::from_kind(ExprKind::CubicalInterval);

                // Check ty : I -> Sort u
                let (ty_ty, ty_cert) = self.infer_type_with_cert_impl(ty)?;
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
                let codomain_sort_i0 =
                    codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
                if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(codomain_sort_i0),
                        location: None,
                    });
                }

                // Check r : I
                let (r_ty, r_cert) = self.infer_type_with_cert_impl(r)?;
                if !matches!(self.whnf_impl(&r_ty).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(interval.clone()),
                        inferred: Box::new(r_ty),
                        location: None,
                    });
                }
                // Check s : I
                let (s_ty, s_cert) = self.infer_type_with_cert_impl(s)?;
                if !matches!(self.whnf_impl(&s_ty).kind, ExprKind::CubicalInterval) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(interval),
                        inferred: Box::new(s_ty),
                        location: None,
                    });
                }

                // Check base : ty r
                let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), r.clone()));
                let (base_ty, base_cert) = self.infer_type_with_cert_impl(base)?;
                if !self.is_def_eq(&base_ty, &expected_base_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_base_ty),
                        inferred: Box::new(base_ty),
                        location: None,
                    });
                }

                // Result type is ty applied to s
                let result_ty = Expr::from_kind(ExprKind::App(ty.clone(), s.clone()));
                let cert = ProofCert::CubicalCoe {
                    ty_cert: Box::new(ty_cert),
                    r_cert: Box::new(r_cert),
                    s_cert: Box::new(s_cert),
                    base_cert: Box::new(base_cert),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }

            // SetTheoretic mode expressions
            ExprKind::ZFCSet(set_expr) => {
                // ZFC set expressions have type Set (a special sort)
                if self.mode != CleanMode::SetTheoretic {
                    return Err(TypeError::ModeRequired {
                        feature: "ZFCSet".to_string(),
                        mode: "SetTheoretic".to_string(),
                    });
                }
                // ZFC sets are in the universe of sets
                let result_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                let cert_kind = self.infer_zfc_set_cert(set_expr)?;
                let cert = ProofCert::ZFCSet {
                    kind: cert_kind,
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }
            ExprKind::ZFCMem { element, set } => {
                // element ∈ set : Prop
                if self.mode != CleanMode::SetTheoretic {
                    return Err(TypeError::ModeRequired {
                        feature: "ZFCMem".to_string(),
                        mode: "SetTheoretic".to_string(),
                    });
                }
                // Check both element and set are sets
                let (elem_ty, elem_cert) = self.infer_type_with_cert_impl(element)?;
                let (set_ty, set_cert) = self.infer_type_with_cert_impl(set)?;
                let expected_set_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&elem_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty.clone()),
                        inferred: Box::new(elem_ty),
                        location: None,
                    });
                }
                if !self.is_def_eq(&set_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(set_ty),
                        location: None,
                    });
                }
                // Membership is a proposition
                let result_ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
                let cert = ProofCert::ZFCMem {
                    elem_cert: Box::new(elem_cert),
                    set_cert: Box::new(set_cert),
                };
                Ok((result_ty, cert))
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                // {x ∈ domain | pred x} : Set
                if self.mode != CleanMode::SetTheoretic {
                    return Err(TypeError::ModeRequired {
                        feature: "ZFCComprehension".to_string(),
                        mode: "SetTheoretic".to_string(),
                    });
                }
                // Check domain is a set
                let (domain_ty, var_ty_cert) = self.infer_type_with_cert_impl(domain)?;
                let expected_set_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&domain_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(domain_ty),
                        location: None,
                    });
                }
                // Check pred : Set -> Prop
                let (pred_ty, pred_cert) = self.infer_type_with_cert_impl(pred)?;
                let expected_pred_ty = Expr::arrow(
                    Expr::const_(super::NAME_ZFC_SET.clone(), vec![]),
                    Expr::prop(),
                );
                if !self.is_def_eq(&pred_ty, &expected_pred_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_pred_ty),
                        inferred: Box::new(pred_ty),
                        location: None,
                    });
                }
                // Result is a set
                let result_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                let cert = ProofCert::ZFCComprehension {
                    var_ty_cert: Box::new(var_ty_cert),
                    pred_cert: Box::new(pred_cert),
                    result_type: Box::new(result_ty.clone()),
                };
                Ok((result_ty, cert))
            }

            // Impredicative mode expressions
            ExprKind::SProp => {
                // SProp : Type 1 (strict propositions live at the same level as Prop)
                if self.mode != CleanMode::Impredicative
                    && self.mode != CleanMode::Classical
                    && self.mode != CleanMode::SetTheoretic
                {
                    return Err(TypeError::ModeRequired {
                        feature: "SProp".to_string(),
                        mode: "Impredicative".to_string(),
                    });
                }
                // SProp is a sort like Prop, so SProp : Type 1
                let result_ty = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
                let cert = ProofCert::SProp;
                Ok((result_ty, cert))
            }
            ExprKind::Squash(inner) => {
                // Squash A : SProp (when A : Sort u)
                if self.mode != CleanMode::Impredicative
                    && self.mode != CleanMode::Classical
                    && self.mode != CleanMode::SetTheoretic
                {
                    return Err(TypeError::ModeRequired {
                        feature: "Squash".to_string(),
                        mode: "Impredicative".to_string(),
                    });
                }
                // Check inner is a type
                let (inner_ty, inner_cert) = self.infer_type_with_cert_impl(inner)?;
                let inner_ty_whnf = self.whnf_impl(&inner_ty);
                let ExprKind::Sort(_level) = &inner_ty_whnf.kind else {
                    return Err(TypeError::ExpectedSort {
                        ty: Box::new(inner_ty),
                        location: None,
                    });
                };
                // Squash A : SProp
                let result_ty = Expr::from_kind(ExprKind::SProp);
                let cert = ProofCert::Squash {
                    inner_cert: Box::new(inner_cert),
                };
                Ok((result_ty, cert))
            }

            _ => unreachable!("non-mode expression in infer_mode_specific_cert"),
        }
    }
}
