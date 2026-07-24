// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core CIC certificate rule implementations.
//!
//! Handles: Sort, BVar, FVar, Const, App, Lam, Pi, Let, Lit, DefEq, MData.

use crate::expr::{BinderData, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;
use std::sync::LazyLock;

static NAME_NAT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
static NAME_STRING: LazyLock<Name> = LazyLock::new(|| Name::from_string("String"));

use super::super::types::{CertError, ProofCert};
use super::CertVerifier;

impl<'env> CertVerifier<'env> {
    /// Sort rule: Sort(l) : Sort(succ(l))
    pub(crate) fn verify_sort(&self, level: &Level, l: &Level) -> Result<Expr, CertError> {
        if level != l {
            return Err(CertError::LevelMismatch {
                expected: level.clone(),
                actual: l.clone(),
            });
        }
        Ok(Expr::from_kind(ExprKind::Sort(Level::succ(level.clone()))))
    }

    /// BVar rule: context lookup
    pub(crate) fn verify_bvar(
        &mut self,
        idx: u32,
        expected_type: &Expr,
        i: u32,
    ) -> Result<Expr, CertError> {
        if idx != i {
            return Err(CertError::InvalidBVar(i));
        }
        // Convert de Bruijn index to level and lookup
        let depth = self.context.len();
        if (idx as usize) >= depth {
            return Err(CertError::InvalidBVar(idx));
        }
        let level = depth - 1 - (idx as usize);
        let ctx_type = &self.context[level];

        // The type at context[level] was stored when context had `level` entries.
        // At that time, the type's free BVars referred to binders 0..level-1.
        // Now at depth `depth`, we have `depth - level` additional binders between
        // us and where the type was valid. So we lift by `depth - level` which
        // equals `idx + 1` (since level = depth - 1 - idx).
        // SAFETY: lift_amount = depth - level = idx + 1, and idx is u32, so this fits in u32.
        #[allow(clippy::cast_possible_truncation)]
        let lift_amount = (depth - level) as u32;
        let lifted_ctx_type = ctx_type.lift(lift_amount);

        // Verify the certificate's expected_type matches the lifted context type
        // Use def_eq_impl since we're inside verify_impl (avoid redundant stack_safe)
        if !self.def_eq_impl(expected_type, &lifted_ctx_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_type.clone()),
                actual: Box::new(lifted_ctx_type),
                location: format!("BVar({idx})"),
            });
        }
        Ok(expected_type.clone())
    }

    /// FVar rule: local context lookup
    pub(crate) fn verify_fvar(
        &mut self,
        id: &FVarId,
        type_: &Expr,
        fid: &FVarId,
    ) -> Result<Expr, CertError> {
        if id != fid {
            return Err(CertError::UnknownFVar(*fid));
        }
        // Verify FVar type is in context
        let ctx_ty = self.fvar_types.get(id).ok_or(CertError::UnknownFVar(*id))?;
        // Use def_eq_impl since we're inside verify_impl (avoid redundant stack_safe)
        if !self.def_eq_impl(type_, ctx_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(type_.clone()),
                actual: Box::new(ctx_ty.clone()),
                location: format!("FVar {id:?}"),
            });
        }
        Ok(type_.clone())
    }

    /// Const rule: environment lookup
    pub(crate) fn verify_const(
        &mut self,
        name: &Name,
        levels: &[Level],
        type_: &Expr,
        n: &Name,
        ls: &[Level],
    ) -> Result<Expr, CertError> {
        if name != n {
            return Err(CertError::StructureMismatch {
                expected: format!("Const {name:?}"),
                actual: format!("Const {n:?}"),
            });
        }
        if levels != ls {
            return Err(CertError::InvalidCert(
                "Level parameters mismatch".to_string(),
            ));
        }
        // Verify against environment
        if let Some(env_type) = self.env.instantiate_type(name, levels) {
            // Use def_eq_impl since we're inside verify_impl
            if !self.def_eq_impl(type_, &env_type) {
                return Err(CertError::TypeMismatch {
                    expected: Box::new(type_.clone()),
                    actual: Box::new(env_type),
                    location: format!("Const {name:?}"),
                });
            }
        } else {
            return Err(CertError::UnknownConst(name.clone()));
        }
        Ok(type_.clone())
    }

    /// App rule: f a : B[a/x] when f : (x : A) → B and a : A
    pub(crate) fn verify_app(
        &mut self,
        fn_cert: &ProofCert,
        arg_cert: &ProofCert,
        result_type: &Expr,
        f: &Expr,
        a: &Arc<Expr>,
    ) -> Result<Expr, CertError> {
        // Verify function
        let fn_ty = self.verify_impl(fn_cert, f)?;

        // Check function type is Pi
        // Use whnf_impl since we're inside verify_impl (avoid redundant stack_safe)
        let fn_type_whnf = self.whnf_impl(&fn_ty);
        match &fn_type_whnf.kind {
            ExprKind::Pi(_, expected_arg_type, body_type) => {
                // Verify argument
                let arg_ty = self.verify_impl(arg_cert, a)?;

                // Check argument type matches
                // Use def_eq_impl since we're inside verify_impl
                if !self.def_eq_impl(&arg_ty, expected_arg_type) {
                    return Err(CertError::TypeMismatch {
                        expected: Box::new(expected_arg_type.as_ref().clone()),
                        actual: Box::new(arg_ty),
                        location: "App argument".to_string(),
                    });
                }

                // Verify result type
                let expected_result = body_type.instantiate(a);
                // Use def_eq_impl since we're inside verify_impl
                if !self.def_eq_impl(result_type, &expected_result) {
                    return Err(CertError::TypeMismatch {
                        expected: Box::new(expected_result),
                        actual: Box::new(result_type.clone()),
                        location: "App result".to_string(),
                    });
                }

                Ok(result_type.clone())
            }
            _ => Err(CertError::InvalidCert(format!(
                "Expected Pi type for function, got {fn_type_whnf:?}"
            ))),
        }
    }

    /// Lam rule: λ (x : A). b : (x : A) → B
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_lam(
        &mut self,
        binder_info: crate::expr::BinderInfo,
        arg_type_cert: &ProofCert,
        body_cert: &ProofCert,
        result_type: &Expr,
        bi: BinderData,
        arg_ty: &Arc<Expr>,
        body: &Expr,
    ) -> Result<Expr, CertError> {
        if binder_info != bi.info {
            return Err(CertError::InvalidCert(
                "Binder info mismatch in Lam".to_string(),
            ));
        }

        // Verify arg type is a type (Sort)
        let arg_sort = self.verify_impl(arg_type_cert, arg_ty)?;
        // Use whnf_impl since we're inside verify_impl
        match &self.whnf_impl(&arg_sort).kind {
            ExprKind::Sort(_) => {}
            _ => {
                return Err(CertError::InvalidCert(
                    "Lambda argument type is not a type".to_string(),
                ))
            }
        }

        // Extend context for body verification
        self.context.push(arg_ty.as_ref().clone());
        let body_ty = self.verify_impl(body_cert, body)?;
        self.context.pop();

        // Build expected Pi type
        let expected_pi = Expr::from_kind(ExprKind::Pi(bi, arg_ty.clone(), body_ty.into()));
        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(&expected_pi, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_pi),
                actual: Box::new(result_type.clone()),
                location: "Lam result type".to_string(),
            });
        }

        Ok(result_type.clone())
    }

    /// Pi rule: (x : A) → B : Sort(imax(l1, l2))
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_pi(
        &mut self,
        binder_info: crate::expr::BinderInfo,
        arg_type_cert: &ProofCert,
        arg_level: &Level,
        body_type_cert: &ProofCert,
        body_level: &Level,
        bi: BinderData,
        arg_ty: &Arc<Expr>,
        body_ty: &Expr,
    ) -> Result<Expr, CertError> {
        if binder_info != bi.info {
            return Err(CertError::InvalidCert(
                "Binder info mismatch in Pi".to_string(),
            ));
        }

        // Verify arg type
        let arg_sort = self.verify_impl(arg_type_cert, arg_ty)?;
        // Use whnf_impl since we're inside verify_impl
        let arg_sort_whnf = self.whnf_impl(&arg_sort);
        let ExprKind::Sort(l1) = &arg_sort_whnf.kind else {
            return Err(CertError::InvalidCert(
                "Pi domain is not a type".to_string(),
            ));
        };

        // Check level matches
        if !self.level_eq(l1, arg_level) {
            return Err(CertError::LevelMismatch {
                expected: arg_level.clone(),
                actual: l1.clone(),
            });
        }

        // Extend context for body verification
        self.context.push(arg_ty.as_ref().clone());
        let body_sort = self.verify_impl(body_type_cert, body_ty)?;
        self.context.pop();

        // Use whnf_impl since we're inside verify_impl
        let body_sort_whnf = self.whnf_impl(&body_sort);
        let ExprKind::Sort(l2) = &body_sort_whnf.kind else {
            return Err(CertError::InvalidCert(
                "Pi codomain is not a type".to_string(),
            ));
        };

        // Check level matches
        if !self.level_eq(l2, body_level) {
            return Err(CertError::LevelMismatch {
                expected: body_level.clone(),
                actual: l2.clone(),
            });
        }

        // Result is Sort(imax(l1, l2))
        Ok(Expr::from_kind(ExprKind::Sort(Level::imax(
            arg_level.clone(),
            body_level.clone(),
        ))))
    }

    /// Let rule
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn verify_let(
        &mut self,
        type_cert: &ProofCert,
        value_cert: &ProofCert,
        body_cert: &ProofCert,
        result_type: &Expr,
        ty: &Arc<Expr>,
        val: &Arc<Expr>,
        body: &Expr,
    ) -> Result<Expr, CertError> {
        // Verify type is a type
        let ty_sort = self.verify_impl(type_cert, ty)?;
        // Use whnf_impl since we're inside verify_impl
        match &self.whnf_impl(&ty_sort).kind {
            ExprKind::Sort(_) => {}
            _ => return Err(CertError::InvalidCert("Let type is not a type".to_string())),
        }

        // Verify value has the type
        let val_ty = self.verify_impl(value_cert, val)?;
        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(&val_ty, ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(ty.as_ref().clone()),
                actual: Box::new(val_ty),
                location: "Let value".to_string(),
            });
        }

        // Extend context for body
        self.context.push(ty.as_ref().clone());
        let body_ty = self.verify_impl(body_cert, body)?;
        self.context.pop();

        // Result type is body type with value substituted
        let expected_result = body_ty.instantiate(val);
        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(&expected_result, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_result),
                actual: Box::new(result_type.clone()),
                location: "Let result".to_string(),
            });
        }

        Ok(result_type.clone())
    }

    /// Lit rule
    pub(crate) fn verify_lit(
        &self,
        lit: &Literal,
        type_: &Expr,
        l: &Literal,
    ) -> Result<Expr, CertError> {
        if lit != l {
            return Err(CertError::StructureMismatch {
                expected: format!("{lit:?}"),
                actual: format!("{l:?}"),
            });
        }

        let expected_type = match lit {
            Literal::Nat(_) => Expr::const_(NAME_NAT.clone(), vec![]),
            Literal::String(_) => Expr::const_(NAME_STRING.clone(), vec![]),
        };

        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(type_, &expected_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_type),
                actual: Box::new(type_.clone()),
                location: "Literal type".to_string(),
            });
        }

        Ok(type_.clone())
    }

    /// DefEq wrapper
    pub(crate) fn verify_def_eq(
        &mut self,
        inner: &ProofCert,
        expected_type: &Expr,
        actual_type: &Expr,
        expr: &Expr,
    ) -> Result<Expr, CertError> {
        let actual = self.verify_impl(inner, expr)?;

        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(&actual, actual_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(actual_type.clone()),
                actual: Box::new(actual.clone()),
                location: "DefEq inner".to_string(),
            });
        }

        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(actual_type, expected_type) {
            return Err(CertError::DefEqFailed {
                left: Box::new(actual_type.clone()),
                right: Box::new(expected_type.clone()),
            });
        }

        Ok(expected_type.clone())
    }

    /// MData rule: metadata is transparent, verify inner expression
    pub(crate) fn verify_mdata(
        &mut self,
        inner_cert: &ProofCert,
        result_type: &Expr,
        inner: &Expr,
    ) -> Result<Expr, CertError> {
        let inner_ty = self.verify_impl(inner_cert, inner)?;

        // Result type should match inner type
        // Use def_eq_impl since we're inside verify_impl
        if !self.def_eq_impl(&inner_ty, result_type) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(inner_ty),
                actual: Box::new(result_type.clone()),
                location: "MData result".to_string(),
            });
        }

        Ok(result_type.clone())
    }
}
