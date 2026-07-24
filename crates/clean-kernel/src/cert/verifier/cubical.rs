// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cubical type theory certificate rules.
//!
//! Handles: CubicalInterval, CubicalEndpoint, CubicalPath, CubicalPathLam,
//! CubicalPathApp, CubicalHComp, CubicalTransp.

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;
use std::sync::Arc;

use super::super::types::{expr_name, CertError, ProofCert};
use super::CertVerifier;

impl<'env> CertVerifier<'env> {
    /// CubicalInterval: I : Type (Sort 1) — I has two elements (i0, i1)
    pub(crate) fn verify_cubical_interval(&self) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalInterval".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }
        Ok(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))))
    }

    /// Cubical endpoints: 0, 1 : I
    pub(crate) fn verify_cubical_endpoint(
        &self,
        is_one: bool,
        expr_kind: &ExprKind,
        expr: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalEndpoint".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }
        match (is_one, expr_kind) {
            (false, ExprKind::CubicalI0) | (true, ExprKind::CubicalI1) => {
                Ok(Expr::from_kind(ExprKind::CubicalInterval))
            }
            _ => Err(CertError::StructureMismatch {
                expected: if is_one {
                    "CubicalI1".to_string()
                } else {
                    "CubicalI0".to_string()
                },
                actual: expr_name(expr),
            }),
        }
    }

    /// Cubical Path type: Path A a b : Sort(l)
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_cubical_path(
        &mut self,
        ty_cert: &ProofCert,
        ty_level: &Level,
        left_cert: &ProofCert,
        right_cert: &ProofCert,
        ty: &Arc<Expr>,
        left: &Expr,
        right: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalPath".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        // Verify ty : I -> Sort(l)
        let ty_type = self.verify_impl(ty_cert, ty)?;
        let ty_type_whnf = self.whnf_impl(&ty_type);
        let ExprKind::Pi(_, arg_ty, body_ty) = &ty_type_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalPath type family is not a function".to_string(),
            ));
        };
        if !matches!(self.whnf_impl(arg_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(Expr::from_kind(ExprKind::CubicalInterval)),
                actual: Box::new(arg_ty.as_ref().clone()),
                location: "CubicalPath type family domain".to_string(),
            });
        }
        let body_ty_whnf = self.whnf_impl(body_ty);
        let ExprKind::Sort(level) = &body_ty_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalPath type family codomain is not a universe".to_string(),
            ));
        };
        if !self.level_eq(level, ty_level) {
            return Err(CertError::LevelMismatch {
                expected: ty_level.clone(),
                actual: level.clone(),
            });
        }

        // Verify left : ty 0
        let left_ty = self.verify_impl(left_cert, left)?;
        let expected_left_ty = Expr::from_kind(ExprKind::App(
            ty.clone(),
            Arc::new(Expr::from_kind(ExprKind::CubicalI0)),
        ));
        if !self.def_eq_impl(&left_ty, &expected_left_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_left_ty),
                actual: Box::new(left_ty),
                location: "CubicalPath left endpoint".to_string(),
            });
        }

        // Verify right : ty 1
        let right_ty = self.verify_impl(right_cert, right)?;
        let expected_right_ty = Expr::from_kind(ExprKind::App(
            ty.clone(),
            Arc::new(Expr::from_kind(ExprKind::CubicalI1)),
        ));
        if !self.def_eq_impl(&right_ty, &expected_right_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_right_ty),
                actual: Box::new(right_ty),
                location: "CubicalPath right endpoint".to_string(),
            });
        }

        // Path types live at the same universe level as the type family codomain
        Ok(Expr::from_kind(ExprKind::Sort(ty_level.clone())))
    }

    /// Cubical PathLam: <i> e : Path A (e[0/i]) (e[1/i])
    pub(crate) fn verify_cubical_path_lam(
        &mut self,
        body_cert: &ProofCert,
        result_type: &Expr,
        body: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalPathLam".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        // Extend context with interval variable and verify body
        self.context
            .push(Expr::from_kind(ExprKind::CubicalInterval));
        let _body_ty = self.verify_impl(body_cert, body)?;
        self.context.pop();

        // Result should be a Path type
        let result_whnf = self.whnf_impl(result_type);
        if !matches!(result_whnf.kind, ExprKind::CubicalPath { .. }) {
            return Err(CertError::InvalidCert(
                "CubicalPathLam result is not a Path type".to_string(),
            ));
        }

        Ok(result_type.clone())
    }

    /// Cubical PathApp: p @ i : A
    pub(crate) fn verify_cubical_path_app(
        &mut self,
        path_cert: &ProofCert,
        arg_cert: &ProofCert,
        result_type: &Expr,
        path: &Expr,
        arg: &Arc<Expr>,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalPathApp".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        // Verify path has Path type
        let path_ty = self.verify_impl(path_cert, path)?;
        let path_ty_whnf = self.whnf_impl(&path_ty);
        let ExprKind::CubicalPath { ty, .. } = &path_ty_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalPathApp path is not a Path type".to_string(),
            ));
        };

        // Verify arg : I
        let arg_ty = self.verify_impl(arg_cert, arg)?;
        if !matches!(self.whnf_impl(&arg_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(Expr::from_kind(ExprKind::CubicalInterval)),
                actual: Box::new(arg_ty),
                location: "CubicalPathApp argument".to_string(),
            });
        }

        // Result type should match ty applied to the argument
        let expected_result_ty = Expr::from_kind(ExprKind::App(ty.clone(), arg.clone()));
        if !self.def_eq_impl(&expected_result_ty, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_result_ty),
                actual: Box::new(result_type.clone()),
                location: "CubicalPathApp result".to_string(),
            });
        }

        Ok(result_type.clone())
    }

    /// Cubical HComp: hcomp {A} {φ} u base : A
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_cubical_hcomp(
        &mut self,
        ty_cert: &ProofCert,
        phi_cert: &ProofCert,
        u_cert: &ProofCert,
        base_cert: &ProofCert,
        result_type: &Expr,
        ty: &Arc<Expr>,
        phi: &Expr,
        u: &Expr,
        base: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalHComp".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        // Verify ty is a type
        let ty_sort = self.verify_impl(ty_cert, ty)?;
        if !matches!(self.whnf_impl(&ty_sort).kind, ExprKind::Sort(_)) {
            return Err(CertError::InvalidCert(
                "CubicalHComp type is not a type".to_string(),
            ));
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let i0 = Expr::from_kind(ExprKind::CubicalI0);
        let i1 = Expr::from_kind(ExprKind::CubicalI1);

        // Verify phi : I
        let phi_ty = self.verify_impl(phi_cert, phi)?;
        if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval.clone()),
                actual: Box::new(phi_ty),
                location: "CubicalHComp phi".to_string(),
            });
        }

        // Verify u : (i : I) -> ty
        let u_ty = self.verify_impl(u_cert, u)?;
        let u_ty_whnf = self.whnf_impl(&u_ty);
        let ExprKind::Pi(_, domain, codomain) = &u_ty_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalHComp partial element is not a function".to_string(),
            ));
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval),
                actual: Box::new((**domain).clone()),
                location: "CubicalHComp partial element domain".to_string(),
            });
        }
        let codomain_i0 = codomain.instantiate(&i0);
        if !self.def_eq_impl(&codomain_i0, ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                actual: Box::new(codomain_i0),
                location: "CubicalHComp partial element at i0".to_string(),
            });
        }
        let codomain_i1 = codomain.instantiate(&i1);
        if !self.def_eq_impl(&codomain_i1, ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                actual: Box::new(codomain_i1),
                location: "CubicalHComp partial element at i1".to_string(),
            });
        }

        // Verify base : ty
        let base_ty = self.verify_impl(base_cert, base)?;
        if !self.def_eq_impl(&base_ty, ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                actual: Box::new(base_ty),
                location: "CubicalHComp base".to_string(),
            });
        }

        // Result type should match ty
        if !self.def_eq_impl(ty, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                actual: Box::new(result_type.clone()),
                location: "CubicalHComp result".to_string(),
            });
        }

        // SOUNDNESS — CCHM well-formedness (overlap agreement + cap/floor
        // agreement). The basic typing above does NOT see these side conditions:
        // without them a floor-disagreeing `hcomp` like
        // `hcomp {Nat} [(j=1)↦λ_.succ zero] zero` verifies, and `<j>` of it
        // re-verifies `Path Nat 0 1` (a closed proof of `Empty`), violating this
        // verifier's `infer_type(expr) == result` contract. The release path and
        // the cert builder run these; the verifier must too. Binder variables are
        // loose `BVar`s here, so this is delegated to the FVar-based validators via
        // `validate_hcomp_for_cert`, which opens them against `self.context`.
        let tc = crate::tc::TypeChecker::with_mode(self.env, self.mode);
        if let Err(e) = tc.validate_hcomp_for_cert(&self.context, phi, u, base, ty) {
            return Err(match e {
                crate::TypeError::TypeMismatch {
                    expected, inferred, ..
                } => CertError::TypeMismatch {
                    expected: Box::new(*expected),
                    actual: Box::new(*inferred),
                    location: "CubicalHComp well-formedness (cap/overlap)".to_string(),
                },
                other => CertError::InvalidCert(format!(
                    "CubicalHComp well-formedness (cap/overlap) failed: {other:?}"
                )),
            });
        }

        Ok(result_type.clone())
    }

    /// Cubical Transp: transp ty φ base : ty[1/i]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_cubical_transp(
        &mut self,
        ty_cert: &ProofCert,
        phi_cert: &ProofCert,
        base_cert: &ProofCert,
        result_type: &Expr,
        ty: &Arc<Expr>,
        phi: &Expr,
        base: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalTransp".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let i0 = Arc::new(Expr::from_kind(ExprKind::CubicalI0));
        let i1 = Arc::new(Expr::from_kind(ExprKind::CubicalI1));

        // Verify ty : I -> Sort u
        let ty_ty = self.verify_impl(ty_cert, ty)?;
        let ty_ty_whnf = self.whnf_impl(&ty_ty);
        let ExprKind::Pi(_, domain, codomain_sort) = &ty_ty_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalTransp type family is not a function".to_string(),
            ));
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval.clone()),
                actual: Box::new((**domain).clone()),
                location: "CubicalTransp type family domain".to_string(),
            });
        }
        let codomain_sort_i0 = codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
            return Err(CertError::InvalidCert(
                "CubicalTransp type family codomain is not a universe".to_string(),
            ));
        }

        // Verify phi : I
        let phi_ty = self.verify_impl(phi_cert, phi)?;
        if !matches!(self.whnf_impl(&phi_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval),
                actual: Box::new(phi_ty),
                location: "CubicalTransp phi".to_string(),
            });
        }

        // Verify base : ty i0
        let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), i0.clone()));
        let base_ty = self.verify_impl(base_cert, base)?;
        if !self.def_eq_impl(&base_ty, &expected_base_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_base_ty),
                actual: Box::new(base_ty),
                location: "CubicalTransp base".to_string(),
            });
        }

        // Result type must match ty i1
        let expected_result_ty = Expr::from_kind(ExprKind::App(ty.clone(), i1));
        if !self.def_eq_impl(&expected_result_ty, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_result_ty),
                actual: Box::new(result_type.clone()),
                location: "CubicalTransp result".to_string(),
            });
        }

        // Result type is ty[1/i]
        Ok(result_type.clone())
    }

    /// Cubical Coe: coe ty r s base : ty s
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_cubical_coe(
        &mut self,
        ty_cert: &ProofCert,
        r_cert: &ProofCert,
        s_cert: &ProofCert,
        base_cert: &ProofCert,
        result_type: &Expr,
        ty: &Arc<Expr>,
        r: &Arc<Expr>,
        s: &Arc<Expr>,
        base: &Expr,
    ) -> Result<Expr, CertError> {
        if !self.mode.has_cubical_layer() {
            return Err(CertError::ModeRequired {
                feature: "CubicalCoe".to_string(),
                required_mode: CleanMode::Cubical,
                current_mode: self.mode,
            });
        }

        let interval = Expr::from_kind(ExprKind::CubicalInterval);

        // Verify ty : I -> Sort u
        let ty_ty = self.verify_impl(ty_cert, ty)?;
        let ty_ty_whnf = self.whnf_impl(&ty_ty);
        let ExprKind::Pi(_, domain, codomain_sort) = &ty_ty_whnf.kind else {
            return Err(CertError::InvalidCert(
                "CubicalCoe type family is not a function".to_string(),
            ));
        };
        if !matches!(self.whnf_impl(domain).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval.clone()),
                actual: Box::new((**domain).clone()),
                location: "CubicalCoe type family domain".to_string(),
            });
        }
        let codomain_sort_i0 = codomain_sort.instantiate(&Expr::from_kind(ExprKind::CubicalI0));
        if !matches!(self.whnf_impl(&codomain_sort_i0).kind, ExprKind::Sort(_)) {
            return Err(CertError::InvalidCert(
                "CubicalCoe type family codomain is not a universe".to_string(),
            ));
        }

        // Verify r : I
        let r_ty = self.verify_impl(r_cert, r)?;
        if !matches!(self.whnf_impl(&r_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval.clone()),
                actual: Box::new(r_ty),
                location: "CubicalCoe r".to_string(),
            });
        }
        // Verify s : I
        let s_ty = self.verify_impl(s_cert, s)?;
        if !matches!(self.whnf_impl(&s_ty).kind, ExprKind::CubicalInterval) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(interval),
                actual: Box::new(s_ty),
                location: "CubicalCoe s".to_string(),
            });
        }

        // Verify base : ty r
        let expected_base_ty = Expr::from_kind(ExprKind::App(ty.clone(), r.clone()));
        let base_ty = self.verify_impl(base_cert, base)?;
        if !self.def_eq_impl(&base_ty, &expected_base_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_base_ty),
                actual: Box::new(base_ty),
                location: "CubicalCoe base".to_string(),
            });
        }

        // Result type must match ty s
        let expected_result_ty = Expr::from_kind(ExprKind::App(ty.clone(), s.clone()));
        if !self.def_eq_impl(&expected_result_ty, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_result_ty),
                actual: Box::new(result_type.clone()),
                location: "CubicalCoe result".to_string(),
            });
        }

        Ok(result_type.clone())
    }
}
