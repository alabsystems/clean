// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Certificate verifier implementation.
//!
//! The `CertVerifier` type-checks proof certificates against expressions,
//! verifying that certificates correctly witness typing derivations.
//! Definitional equality and WHNF reduction are in the sibling `reduction` module.
//!
//! Rule-family implementations are split into focused submodules:
//! - `core`: Sort, BVar, FVar, Const, App, Lam, Pi, Let, Lit, DefEq, MData
//! - `projection`: Proj verification and field-type derivation
//! - `cubical`: Cubical type theory rules (Interval, Path, HComp, Transp)
//! - `modes`: ZFC set theory, SProp, Squash

mod core;
mod cubical;
mod modes;
mod projection;

use crate::env::Environment;
use crate::expr::{stack_safe, Expr, ExprKind, FVarId};
use crate::mode::CleanMode;
use crate::tc::LocalContext;
use std::collections::HashMap;

use super::types::{cert_name, expr_name, CertError, ProofCert};

/// Certificate verifier state
pub struct CertVerifier<'env> {
    pub(super) env: &'env Environment,
    /// Local context: maps de Bruijn level to type
    /// (level 0 = outermost binding)
    pub(super) context: Vec<Expr>,
    /// `FVar` types
    pub(super) fvar_types: HashMap<FVarId, Expr>,
    /// Current mode for mode-aware verification
    pub(super) mode: CleanMode,
}

impl<'env> CertVerifier<'env> {
    /// Create a new certificate verifier inheriting the environment mode
    ///
    /// REQUIRES: `env` is a valid clean environment
    /// ENSURES: `self.mode() == env.mode()`
    /// ENSURES: `self.context` and `self.fvar_types` are empty
    pub fn new(env: &'env Environment) -> Self {
        Self {
            env,
            context: Vec::new(),
            fvar_types: HashMap::new(),
            mode: env.mode(),
        }
    }

    /// Create a new certificate verifier with a specific mode
    ///
    /// REQUIRES: `env` is a valid clean environment
    /// ENSURES: `self.mode() == mode`
    /// ENSURES: `self.context` and `self.fvar_types` are empty
    pub fn with_mode(env: &'env Environment, mode: CleanMode) -> Self {
        Self {
            env,
            context: Vec::new(),
            fvar_types: HashMap::new(),
            mode,
        }
    }

    /// Get the current mode
    ///
    /// ENSURES: Returns the active verification mode
    pub fn mode(&self) -> CleanMode {
        self.mode
    }

    /// Set the mode
    ///
    /// ENSURES: `self.mode() == mode`
    pub fn set_mode(&mut self, mode: CleanMode) {
        self.mode = mode;
    }

    /// Register a free variable type in the verifier context.
    /// Returns an error if the ID was already registered with a different type.
    ///
    /// REQUIRES: `id` is a valid `FVarId` originating from the local context
    /// REQUIRES: `ty` is well-formed
    /// ENSURES: On success, `id` is registered with type def-eq to `ty`
    /// ENSURES: Previously registered IDs retain their types
    pub fn register_fvar(&mut self, id: FVarId, ty: Expr) -> Result<(), CertError> {
        if let Some(existing) = self.fvar_types.get(&id) {
            if !self.def_eq(existing, &ty) {
                return Err(CertError::TypeMismatch {
                    expected: Box::new(existing.clone()),
                    actual: Box::new(ty),
                    location: format!("FVar {id:?}"),
                });
            }
        }
        self.fvar_types.insert(id, ty);
        Ok(())
    }

    /// Register all free variables from a `LocalContext`.
    ///
    /// This is useful when integrating with the elaborator to transfer
    /// the full local context into the certificate verifier.
    /// Returns an error if any `FVar` was already registered with a conflicting type.
    ///
    /// REQUIRES: `ctx` is a well-formed local context
    /// ENSURES: On success, every `FVar` in `ctx` is registered
    /// ENSURES: Existing registrations remain unchanged or def-eq
    pub fn register_local_context(&mut self, ctx: &LocalContext) -> Result<(), CertError> {
        for decl in ctx.iter() {
            self.register_fvar(decl.id, decl.type_.clone())?;
        }
        Ok(())
    }

    /// Verify a certificate and return the proven type
    ///
    /// This is the trusted checker - it verifies that the certificate
    /// correctly witnesses the typing derivation.
    ///
    /// REQUIRES: `cert` and `expr` must be structurally compatible (same shape)
    /// REQUIRES: All FVars in `expr` are registered via `register_fvar`
    /// REQUIRES: All Consts in `expr` are defined in `self.env`
    /// ENSURES: On success, `result` is the type of `expr`
    /// ENSURES: On success, `TypeChecker::infer_type(expr) == result`
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn verify(&mut self, cert: &ProofCert, expr: &Expr) -> Result<Expr, CertError> {
        stack_safe(|| self.verify_impl(cert, expr))
    }

    /// Internal implementation. Entry points should wrap with `stack_safe`.
    ///
    /// Dispatches to rule-family sub-dispatchers in core, projection, cubical,
    /// and modes modules. Each returns `Some(result)` if it handles the
    /// cert/expr pair, or `None` to fall through.
    pub(crate) fn verify_impl(&mut self, cert: &ProofCert, expr: &Expr) -> Result<Expr, CertError> {
        if let Some(r) = self.dispatch_core_leaf(cert, expr) {
            return r;
        }
        if let Some(r) = self.dispatch_core_binder(cert, expr) {
            return r;
        }
        if let Some(r) = self.dispatch_projection(cert, expr) {
            return r;
        }
        if let Some(r) = self.dispatch_cubical(cert, expr) {
            return r;
        }
        if let Some(r) = self.dispatch_modes(cert, expr) {
            return r;
        }
        Err(CertError::StructureMismatch {
            expected: cert_name(cert),
            actual: expr_name(expr),
        })
    }

    /// Dispatch core leaf rules: Sort, BVar, FVar, Const, Lit, DefEq, MData.
    fn dispatch_core_leaf(
        &mut self,
        cert: &ProofCert,
        expr: &Expr,
    ) -> Option<Result<Expr, CertError>> {
        match (cert, &expr.kind) {
            (ProofCert::Sort { level }, ExprKind::Sort(l)) => Some(self.verify_sort(level, l)),
            (ProofCert::BVar { idx, expected_type }, ExprKind::BVar(i)) => {
                Some(self.verify_bvar(*idx, expected_type, *i))
            }
            (ProofCert::FVar { id, type_ }, ExprKind::FVar(fid)) => {
                Some(self.verify_fvar(id, type_, fid))
            }
            (
                ProofCert::Const {
                    name,
                    levels,
                    type_,
                },
                ExprKind::Const(n, ls),
            ) => Some(self.verify_const(name, levels, type_, n, ls.as_slice())),
            (ProofCert::Lit { lit, type_ }, ExprKind::Lit(l)) => {
                Some(self.verify_lit(lit, type_, l))
            }
            (
                ProofCert::DefEq {
                    inner,
                    expected_type,
                    actual_type,
                    ..
                },
                _,
            ) => Some(self.verify_def_eq(inner, expected_type, actual_type, expr)),
            (
                ProofCert::MData {
                    metadata: _,
                    inner_cert,
                    result_type,
                },
                ExprKind::MData(_, inner),
            ) => Some(self.verify_mdata(inner_cert, result_type, inner)),
            _ => None,
        }
    }

    /// Dispatch core binder rules: App, Lam, Pi, Let.
    fn dispatch_core_binder(
        &mut self,
        cert: &ProofCert,
        expr: &Expr,
    ) -> Option<Result<Expr, CertError>> {
        match (cert, &expr.kind) {
            (
                ProofCert::App {
                    fn_cert,
                    fn_type: _,
                    arg_cert,
                    result_type,
                },
                ExprKind::App(f, a),
            ) => Some(self.verify_app(fn_cert, arg_cert, result_type, f, a)),
            (
                ProofCert::Lam {
                    binder_info,
                    arg_type_cert,
                    body_cert,
                    result_type,
                },
                ExprKind::Lam(bi, arg_ty, body),
            ) => Some(self.verify_lam(
                *binder_info,
                arg_type_cert,
                body_cert,
                result_type,
                *bi,
                arg_ty,
                body,
            )),
            (
                ProofCert::Pi {
                    binder_info,
                    arg_type_cert,
                    arg_level,
                    body_type_cert,
                    body_level,
                },
                ExprKind::Pi(bi, arg_ty, body_ty),
            ) => Some(self.verify_pi(
                *binder_info,
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
                *bi,
                arg_ty,
                body_ty,
            )),
            (
                ProofCert::Let {
                    type_cert,
                    value_cert,
                    body_cert,
                    result_type,
                },
                ExprKind::Let(_, ty, val, body, _),
            ) => {
                Some(self.verify_let(type_cert, value_cert, body_cert, result_type, ty, val, body))
            }
            _ => None,
        }
    }

    /// Dispatch projection rule.
    fn dispatch_projection(
        &mut self,
        cert: &ProofCert,
        expr: &Expr,
    ) -> Option<Result<Expr, CertError>> {
        match (cert, &expr.kind) {
            (
                ProofCert::Proj {
                    struct_name,
                    idx,
                    expr_cert,
                    expr_type,
                    field_type,
                },
                ExprKind::Proj(proj_name, proj_idx, proj_expr),
            ) => Some(self.verify_proj(
                struct_name,
                *idx,
                expr_cert,
                expr_type,
                field_type,
                proj_name,
                *proj_idx,
                proj_expr,
            )),
            _ => None,
        }
    }

    /// Dispatch cubical type theory rules.
    fn dispatch_cubical(
        &mut self,
        cert: &ProofCert,
        expr: &Expr,
    ) -> Option<Result<Expr, CertError>> {
        match (cert, &expr.kind) {
            (ProofCert::CubicalInterval, ExprKind::CubicalInterval) => {
                Some(self.verify_cubical_interval())
            }
            (ProofCert::CubicalEndpoint { is_one }, expr_kind) => {
                Some(self.verify_cubical_endpoint(*is_one, expr_kind, expr))
            }
            (
                ProofCert::CubicalPath {
                    ty_cert,
                    ty_level,
                    left_cert,
                    right_cert,
                },
                ExprKind::CubicalPath { ty, left, right },
            ) => Some(
                self.verify_cubical_path(ty_cert, ty_level, left_cert, right_cert, ty, left, right),
            ),
            (
                ProofCert::CubicalPathLam {
                    body_cert,
                    body_type: _,
                    result_type,
                },
                ExprKind::CubicalPathLam { body },
            ) => Some(self.verify_cubical_path_lam(body_cert, result_type, body)),
            (
                ProofCert::CubicalPathApp {
                    path_cert,
                    arg_cert,
                    path_type: _,
                    result_type,
                },
                ExprKind::CubicalPathApp { path, arg },
            ) => Some(self.verify_cubical_path_app(path_cert, arg_cert, result_type, path, arg)),
            (
                ProofCert::CubicalHComp {
                    ty_cert,
                    phi_cert,
                    u_cert,
                    base_cert,
                    result_type,
                },
                ExprKind::CubicalHComp { ty, phi, u, base },
            ) => Some(self.verify_cubical_hcomp(
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                result_type,
                ty,
                phi,
                u,
                base,
            )),
            (
                ProofCert::CubicalTransp {
                    ty_cert,
                    phi_cert,
                    base_cert,
                    result_type,
                },
                ExprKind::CubicalTransp { ty, phi, base },
            ) => Some(self.verify_cubical_transp(
                ty_cert,
                phi_cert,
                base_cert,
                result_type,
                ty,
                phi,
                base,
            )),
            (
                ProofCert::CubicalCoe {
                    ty_cert,
                    r_cert,
                    s_cert,
                    base_cert,
                    result_type,
                },
                ExprKind::CubicalCoe { ty, r, s, base },
            ) => Some(self.verify_cubical_coe(
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                result_type,
                ty,
                r,
                s,
                base,
            )),
            _ => None,
        }
    }

    /// Dispatch mode-specific rules: ZFC, SProp, Squash.
    fn dispatch_modes(&mut self, cert: &ProofCert, expr: &Expr) -> Option<Result<Expr, CertError>> {
        match (cert, &expr.kind) {
            (
                ProofCert::ZFCSet {
                    kind,
                    result_type: _,
                },
                ExprKind::ZFCSet(set_expr),
            ) => Some(self.verify_zfc_set_expr(kind, set_expr)),
            (
                ProofCert::ZFCMem {
                    elem_cert,
                    set_cert,
                },
                ExprKind::ZFCMem { element, set },
            ) => Some(self.verify_zfc_mem(elem_cert, set_cert, element, set)),
            (
                ProofCert::ZFCComprehension {
                    var_ty_cert,
                    pred_cert,
                    result_type: _,
                },
                ExprKind::ZFCComprehension { domain, pred },
            ) => Some(self.verify_zfc_comprehension(var_ty_cert, pred_cert, domain, pred)),
            (ProofCert::SProp, ExprKind::SProp) => Some(self.verify_sprop()),
            (ProofCert::Squash { inner_cert }, ExprKind::Squash(inner)) => {
                Some(self.verify_squash(inner_cert, inner))
            }
            _ => None,
        }
    }
}
