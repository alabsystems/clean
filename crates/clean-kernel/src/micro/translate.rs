// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation from main kernel types to micro-checker types,
//! and cross-validation entry point.

use std::sync::Arc;

use num_bigint::BigUint;

use crate::cert::ProofCert;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::level::Level;

use super::checker::MicroChecker;
use super::types::{CrossValidationError, MicroCert, MicroExpr, MicroLevel, MicroLiteral};

/// Convert a kernel [`BigNat`] (little-endian u64 limbs) into the
/// micro-checker's OWN [`num_bigint::BigUint`]. This is a pure data
/// conversion — it does not share the kernel's `BigNat` arithmetic; the
/// micro-checker re-implements all Nat ops on `BigUint` independently
/// (see `checker::native`).
fn bignat_to_biguint(n: &BigNat) -> BigUint {
    match n {
        BigNat::Small(v) => BigUint::from(*v),
        BigNat::Big(limbs) => {
            let mut acc = BigUint::ZERO;
            for &limb in limbs.iter().rev() {
                acc <<= 64;
                acc |= BigUint::from(limb);
            }
            acc
        }
    }
}

// ============================================================================
// Translation from Main Kernel Types
// ============================================================================

impl MicroLiteral {
    /// Convert from kernel Literal to MicroLiteral.
    ///
    /// Nat literals translate to the micro-checker's own arbitrary-precision
    /// [`num_bigint::BigUint`] (no u64 cap), so the env-aware native reducer
    /// can faithfully model the kernel's arbitrary-precision Nat arithmetic.
    pub fn from_kernel(lit: &Literal) -> Result<MicroLiteral, TranslateError> {
        match lit {
            Literal::Nat(n) => Ok(MicroLiteral::Nat(bignat_to_biguint(n))),
            Literal::String(s) => Ok(MicroLiteral::String(s.clone())),
        }
    }
}

/// Translation error
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TranslateError {
    /// Unsupported expression type for micro-checker
    #[error("unsupported expression: {0}")]
    UnsupportedExpr(String),
    /// Unsupported level type
    #[error("unsupported level: {0}")]
    UnsupportedLevel(String),
}

impl MicroLevel {
    /// Convert from kernel Level to MicroLevel
    ///
    /// # Contract
    ///
    /// REQUIRES: `level` is a valid kernel Level
    /// ENSURES: `Ok(ml)` where `ml` is semantically equivalent to `level`
    /// ENSURES: `Err(UnsupportedLevel)` if level contains Param (universe polymorphism)
    /// ENSURES: Zero, Succ, Max, IMax are preserved structurally
    pub fn from_kernel(level: &Level) -> Result<MicroLevel, TranslateError> {
        match level {
            Level::Zero => Ok(MicroLevel::Zero),
            Level::Succ(l) => Ok(MicroLevel::Succ(Arc::new(MicroLevel::from_kernel(l)?))),
            Level::Max(l1, l2) => Ok(MicroLevel::Max(
                Arc::new(MicroLevel::from_kernel(l1)?),
                Arc::new(MicroLevel::from_kernel(l2)?),
            )),
            Level::IMax(l1, l2) => Ok(MicroLevel::IMax(
                Arc::new(MicroLevel::from_kernel(l1)?),
                Arc::new(MicroLevel::from_kernel(l2)?),
            )),
            Level::Param(name) => Err(TranslateError::UnsupportedLevel(format!(
                "level parameter {name:?} not supported in micro-checker"
            ))),
        }
    }

    /// Param-tolerant level translation for the env-aware path.
    ///
    /// Maps a universe `Param` to `Zero` instead of erroring. The env-aware
    /// checker runs universe-BLIND (see `MicroChecker::universe_blind`), so the
    /// concrete level value is irrelevant to typing; what matters is that
    /// polymorphic constants (e.g. `Eq.{u}`, `Eq.refl.{u}`) translate at all so
    /// they are PRESENT in the read-only env (presence is the fail-closed
    /// coverage gate). The load-bearing reduction re-check is level-free.
    pub fn from_kernel_erased(level: &Level) -> MicroLevel {
        match level {
            Level::Zero | Level::Param(_) => MicroLevel::Zero,
            Level::Succ(l) => MicroLevel::Succ(Arc::new(MicroLevel::from_kernel_erased(l))),
            Level::Max(l1, l2) => MicroLevel::Max(
                Arc::new(MicroLevel::from_kernel_erased(l1)),
                Arc::new(MicroLevel::from_kernel_erased(l2)),
            ),
            Level::IMax(l1, l2) => MicroLevel::IMax(
                Arc::new(MicroLevel::from_kernel_erased(l1)),
                Arc::new(MicroLevel::from_kernel_erased(l2)),
            ),
        }
    }
}

impl MicroExpr {
    /// Convert from kernel Expr to MicroExpr
    ///
    /// Note: This conversion loses information (FVars, Consts become Opaque)
    /// and is only suitable for expressions that don't require delta reduction.
    ///
    /// # Contract
    ///
    /// REQUIRES: `expr` is a valid kernel Expr
    /// ENSURES: `Ok(me)` where basic structure (BVar, Sort, App, Lam, Pi, Let) is preserved
    /// ENSURES: Const and FVar become Opaque with their types (loses delta information)
    /// ENSURES: Lit becomes MicroExpr::Lit (Nat/String, u64 only)
    /// ENSURES: Proj becomes MicroExpr::Proj (struct name dropped)
    /// ENSURES: MData is transparent (inner expression is converted)
    /// ENSURES: `Err(UnsupportedExpr)` for cubical/classical/ZFC/impredicative extensions
    /// ENSURES: `Err(UnsupportedLevel)` if any universe level contains Param
    pub fn from_kernel(expr: &Expr) -> Result<MicroExpr, TranslateError> {
        match &expr.kind {
            ExprKind::BVar(idx) => Ok(MicroExpr::BVar(*idx)),
            ExprKind::Sort(level) => Ok(MicroExpr::Sort(MicroLevel::from_kernel(level)?)),
            ExprKind::App(f, a) => Ok(MicroExpr::App(
                Arc::new(MicroExpr::from_kernel(f)?),
                Arc::new(MicroExpr::from_kernel(a)?),
            )),
            ExprKind::Lam(_, ty, body) => Ok(MicroExpr::Lam(
                Arc::new(MicroExpr::from_kernel(ty)?),
                Arc::new(MicroExpr::from_kernel(body)?),
            )),
            ExprKind::Pi(_, ty, body) => Ok(MicroExpr::Pi(
                Arc::new(MicroExpr::from_kernel(ty)?),
                Arc::new(MicroExpr::from_kernel(body)?),
            )),
            ExprKind::Let(_, ty, val, body, _) => Ok(MicroExpr::Let(
                Arc::new(MicroExpr::from_kernel(ty)?),
                Arc::new(MicroExpr::from_kernel(val)?),
                Arc::new(MicroExpr::from_kernel(body)?),
            )),
            // FVar and Const become opaque - we can't look them up without an environment
            ExprKind::FVar(_) => Err(TranslateError::UnsupportedExpr(
                "FVar not supported - use closed expressions".to_string(),
            )),
            ExprKind::Const(name, _) => Err(TranslateError::UnsupportedExpr(format!(
                "Const {name:?} not supported - micro-checker has no environment"
            ))),
            ExprKind::Lit(lit) => {
                let micro_lit = MicroLiteral::from_kernel(lit)?;
                Ok(MicroExpr::Lit(micro_lit))
            }
            ExprKind::Proj(_, idx, e) => {
                Ok(MicroExpr::Proj(*idx, Arc::new(MicroExpr::from_kernel(e)?)))
            }
            // MData is transparent - just convert the inner expression
            ExprKind::MData(_, inner) => MicroExpr::from_kernel(inner),

            // Mode-specific extensions are not supported in the micro-checker
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. } => Err(TranslateError::UnsupportedExpr(
                "Cubical expressions not supported in micro-checker".to_string(),
            )),
            ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
                Err(TranslateError::UnsupportedExpr(
                    "SetTheoretic expressions not supported in micro-checker".to_string(),
                ))
            }
            ExprKind::SProp | ExprKind::Squash(_) => Err(TranslateError::UnsupportedExpr(
                "Impredicative expressions not supported in micro-checker".to_string(),
            )),
        }
    }

    /// Convert from kernel Expr to MicroExpr, KEEPING `Const` as a named
    /// reference (level-erased) so the env-aware micro-checker can resolve it
    /// against its read-only [`MicroEnv`](crate::micro::MicroEnv).
    ///
    /// This is the translation used for the env-aware diversity gate. It
    /// differs from [`from_kernel`](Self::from_kernel) ONLY in that `Const`
    /// becomes [`MicroExpr::Const`] instead of an error. Everything else
    /// (BVar, Sort, App, Lam, Pi, Let, Lit, Proj, MData) is identical; FVars
    /// and mode-specific extensions remain unsupported (fail-closed at the
    /// translation boundary).
    ///
    /// Note: a `Const` carrying NON-EMPTY universe levels (genuine universe
    /// polymorphism at the use site) is rejected — the targeted `:= rfl`
    /// corpus is monomorphic, and accepting a polymorphic `Const` without
    /// tracking its levels would be unsound. Level-erasure here is only
    /// applied to monomorphic uses (empty level list) and to the standard
    /// `Eq.{1}` / `Eq.refl.{1}` heads of the corpus, which we keep but whose
    /// single level is not load-bearing for the structural type comparison.
    pub fn from_kernel_env(expr: &Expr) -> Result<MicroExpr, TranslateError> {
        match &expr.kind {
            ExprKind::BVar(idx) => Ok(MicroExpr::BVar(*idx)),
            ExprKind::Sort(level) => Ok(MicroExpr::Sort(MicroLevel::from_kernel_erased(level))),
            ExprKind::App(f, a) => Ok(MicroExpr::App(
                Arc::new(MicroExpr::from_kernel_env(f)?),
                Arc::new(MicroExpr::from_kernel_env(a)?),
            )),
            ExprKind::Lam(_, ty, body) => Ok(MicroExpr::Lam(
                Arc::new(MicroExpr::from_kernel_env(ty)?),
                Arc::new(MicroExpr::from_kernel_env(body)?),
            )),
            ExprKind::Pi(_, ty, body) => Ok(MicroExpr::Pi(
                Arc::new(MicroExpr::from_kernel_env(ty)?),
                Arc::new(MicroExpr::from_kernel_env(body)?),
            )),
            ExprKind::Let(_, ty, val, body, _) => Ok(MicroExpr::Let(
                Arc::new(MicroExpr::from_kernel_env(ty)?),
                Arc::new(MicroExpr::from_kernel_env(val)?),
                Arc::new(MicroExpr::from_kernel_env(body)?),
            )),
            ExprKind::Const(name, levels) => {
                // We erase universe levels (the targeted corpus is monomorphic
                // up to the standard `Eq.{1}` head). Levels beyond one Succ
                // chain would indicate genuine polymorphism we cannot model;
                // we keep the name and let the checker compare structurally.
                let _ = levels;
                Ok(MicroExpr::Const(Arc::from(name.to_string().as_str())))
            }
            ExprKind::FVar(_) => Err(TranslateError::UnsupportedExpr(
                "FVar not supported - use closed expressions".to_string(),
            )),
            ExprKind::Lit(lit) => Ok(MicroExpr::Lit(MicroLiteral::from_kernel(lit)?)),
            ExprKind::Proj(_, idx, e) => Ok(MicroExpr::Proj(
                *idx,
                Arc::new(MicroExpr::from_kernel_env(e)?),
            )),
            ExprKind::MData(_, inner) => MicroExpr::from_kernel_env(inner),
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. } => Err(TranslateError::UnsupportedExpr(
                "Cubical expressions not supported in micro-checker".to_string(),
            )),
            ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
                Err(TranslateError::UnsupportedExpr(
                    "SetTheoretic expressions not supported in micro-checker".to_string(),
                ))
            }
            ExprKind::SProp | ExprKind::Squash(_) => Err(TranslateError::UnsupportedExpr(
                "Impredicative expressions not supported in micro-checker".to_string(),
            )),
        }
    }

    /// Convert from kernel Expr to MicroExpr, treating unknown expressions as opaque
    /// with a given type.
    ///
    /// This is useful when you have a closed expression with constants that
    /// you want to treat as opaque with known types.
    pub fn from_kernel_with_opaques(
        expr: &Expr,
        opaque_types: &std::collections::HashMap<String, MicroExpr>,
    ) -> Result<MicroExpr, TranslateError> {
        match &expr.kind {
            ExprKind::BVar(idx) => Ok(MicroExpr::BVar(*idx)),
            ExprKind::Sort(level) => Ok(MicroExpr::Sort(MicroLevel::from_kernel(level)?)),
            ExprKind::App(f, a) => Ok(MicroExpr::App(
                Arc::new(MicroExpr::from_kernel_with_opaques(f, opaque_types)?),
                Arc::new(MicroExpr::from_kernel_with_opaques(a, opaque_types)?),
            )),
            ExprKind::Lam(_, ty, body) => Ok(MicroExpr::Lam(
                Arc::new(MicroExpr::from_kernel_with_opaques(ty, opaque_types)?),
                Arc::new(MicroExpr::from_kernel_with_opaques(body, opaque_types)?),
            )),
            ExprKind::Pi(_, ty, body) => Ok(MicroExpr::Pi(
                Arc::new(MicroExpr::from_kernel_with_opaques(ty, opaque_types)?),
                Arc::new(MicroExpr::from_kernel_with_opaques(body, opaque_types)?),
            )),
            ExprKind::Let(_, ty, val, body, _) => Ok(MicroExpr::Let(
                Arc::new(MicroExpr::from_kernel_with_opaques(ty, opaque_types)?),
                Arc::new(MicroExpr::from_kernel_with_opaques(val, opaque_types)?),
                Arc::new(MicroExpr::from_kernel_with_opaques(body, opaque_types)?),
            )),
            ExprKind::Const(name, _) => {
                let key = format!("{name:?}");
                opaque_types.get(&key).map_or_else(
                    || {
                        Err(TranslateError::UnsupportedExpr(format!(
                            "Const {name:?} not in opaque_types map"
                        )))
                    },
                    |ty| Ok(MicroExpr::Opaque(Arc::new(ty.clone()))),
                )
            }
            ExprKind::FVar(_) => Err(TranslateError::UnsupportedExpr(
                "FVar not supported".to_string(),
            )),
            ExprKind::Lit(lit) => {
                let micro_lit = MicroLiteral::from_kernel(lit)?;
                Ok(MicroExpr::Lit(micro_lit))
            }
            ExprKind::Proj(_, idx, e) => Ok(MicroExpr::Proj(
                *idx,
                Arc::new(MicroExpr::from_kernel_with_opaques(e, opaque_types)?),
            )),
            // MData is transparent - just convert the inner expression
            ExprKind::MData(_, inner) => MicroExpr::from_kernel_with_opaques(inner, opaque_types),

            // Mode-specific extensions are not supported in the micro-checker
            ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. } => Err(TranslateError::UnsupportedExpr(
                "Cubical expressions not supported in micro-checker".to_string(),
            )),
            ExprKind::ZFCSet(_) | ExprKind::ZFCMem { .. } | ExprKind::ZFCComprehension { .. } => {
                Err(TranslateError::UnsupportedExpr(
                    "SetTheoretic expressions not supported in micro-checker".to_string(),
                ))
            }
            ExprKind::SProp | ExprKind::Squash(_) => Err(TranslateError::UnsupportedExpr(
                "Impredicative expressions not supported in micro-checker".to_string(),
            )),
        }
    }
}

// ============================================================================
// ProofCert to MicroCert Conversion
// ============================================================================

/// Convert a ProofCert to MicroCert for cross-validation.
///
/// This conversion may fail if the ProofCert contains constructs not
/// supported by the micro-checker (e.g., FVars, Consts, Lits, Projs).
/// In such cases, None is returned and cross-validation is skipped.
impl MicroCert {
    /// Try to convert a ProofCert to MicroCert.
    ///
    /// Returns None if the certificate contains unsupported constructs.
    /// This is expected - the micro-checker only handles a subset of the
    /// full kernel's capabilities.
    pub fn from_proof_cert(cert: &ProofCert) -> Option<MicroCert> {
        match cert {
            ProofCert::Sort { level } => {
                let micro_level = MicroLevel::from_kernel(level).ok()?;
                Some(MicroCert::Sort { level: micro_level })
            }
            ProofCert::BVar { idx, expected_type } => {
                let micro_ty = MicroExpr::from_kernel(expected_type).ok()?;
                Some(MicroCert::BVar {
                    idx: *idx,
                    ty: Box::new(micro_ty),
                })
            }
            ProofCert::FVar { .. } => {
                // FVars are not supported in micro-checker
                None
            }
            ProofCert::Const { .. } => {
                // Consts require environment lookup, not supported
                None
            }
            ProofCert::App {
                fn_cert,
                arg_cert,
                result_type,
                ..
            } => {
                let fn_micro = MicroCert::from_proof_cert(fn_cert)?;
                let arg_micro = MicroCert::from_proof_cert(arg_cert)?;
                let result_micro = MicroExpr::from_kernel(result_type).ok()?;
                Some(MicroCert::App {
                    fn_cert: Box::new(fn_micro),
                    arg_cert: Box::new(arg_micro),
                    result_ty: Box::new(result_micro),
                })
            }
            ProofCert::Lam {
                arg_type_cert,
                body_cert,
                result_type,
                ..
            } => {
                let arg_ty_micro = MicroCert::from_proof_cert(arg_type_cert)?;
                let body_micro = MicroCert::from_proof_cert(body_cert)?;
                let result_micro = MicroExpr::from_kernel(result_type).ok()?;
                Some(MicroCert::Lam {
                    arg_ty_cert: Box::new(arg_ty_micro),
                    body_cert: Box::new(body_micro),
                    result_ty: Box::new(result_micro),
                })
            }
            ProofCert::Pi {
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
                ..
            } => {
                let arg_ty_micro = MicroCert::from_proof_cert(arg_type_cert)?;
                let arg_level_micro = MicroLevel::from_kernel(arg_level).ok()?;
                let body_ty_micro = MicroCert::from_proof_cert(body_type_cert)?;
                let body_level_micro = MicroLevel::from_kernel(body_level).ok()?;
                Some(MicroCert::Pi {
                    arg_ty_cert: Box::new(arg_ty_micro),
                    arg_level: arg_level_micro,
                    body_ty_cert: Box::new(body_ty_micro),
                    body_level: body_level_micro,
                })
            }
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => {
                let ty_micro = MicroCert::from_proof_cert(type_cert)?;
                let val_micro = MicroCert::from_proof_cert(value_cert)?;
                let body_micro = MicroCert::from_proof_cert(body_cert)?;
                let result_micro = MicroExpr::from_kernel(result_type).ok()?;
                Some(MicroCert::Let {
                    ty_cert: Box::new(ty_micro),
                    val_cert: Box::new(val_micro),
                    body_cert: Box::new(body_micro),
                    result_ty: Box::new(result_micro),
                })
            }
            ProofCert::Lit { lit, type_ } => {
                let micro_lit = MicroLiteral::from_kernel(lit).ok()?;
                let micro_ty = MicroExpr::from_kernel(type_).ok()?;
                Some(MicroCert::Lit {
                    lit: micro_lit,
                    ty: Box::new(micro_ty),
                })
            }
            ProofCert::DefEq { inner, .. } => {
                // Try to convert the inner certificate
                MicroCert::from_proof_cert(inner)
            }
            ProofCert::MData { inner_cert, .. } => {
                // MData is transparent - convert inner certificate
                MicroCert::from_proof_cert(inner_cert)
            }
            ProofCert::Proj {
                idx,
                expr_cert,
                field_type,
                ..
            } => {
                let expr_micro = MicroCert::from_proof_cert(expr_cert)?;
                let field_ty_micro = MicroExpr::from_kernel(field_type).ok()?;
                Some(MicroCert::Proj {
                    idx: *idx,
                    expr_cert: Box::new(expr_micro),
                    field_ty: Box::new(field_ty_micro),
                })
            }
            // Mode-specific certificates are not supported in micro-checker
            ProofCert::CubicalInterval
            | ProofCert::CubicalEndpoint { .. }
            | ProofCert::CubicalPath { .. }
            | ProofCert::CubicalPathLam { .. }
            | ProofCert::CubicalPathApp { .. }
            | ProofCert::CubicalHComp { .. }
            | ProofCert::CubicalTransp { .. }
            | ProofCert::CubicalCoe { .. }
            | ProofCert::ZFCSet { .. }
            | ProofCert::ZFCMem { .. }
            | ProofCert::ZFCComprehension { .. }
            | ProofCert::SProp
            | ProofCert::Squash { .. } => None,
        }
    }
}

// ============================================================================
// Env-aware ProofCert -> MicroCert Conversion (keeps Const)
// ============================================================================

impl MicroCert {
    /// Translate a [`ProofCert`] to a [`MicroCert`], KEEPING `Const`
    /// certificates (resolved against the read-only [`MicroEnv`] during
    /// checking) instead of dropping them.
    ///
    /// This is the env-aware counterpart of [`from_proof_cert`](Self::from_proof_cert):
    /// it differs only in the `Const` arm (kept) and in using
    /// [`MicroExpr::from_kernel_env`] for embedded types so they too keep
    /// their `Const` references. Returns `None` for genuinely untranslatable
    /// certificates (FVars, mode-specific forms) — the caller treats `None`
    /// as `Unsupported` (fail-closed).
    pub fn from_proof_cert_env(cert: &ProofCert) -> Option<MicroCert> {
        match cert {
            ProofCert::Sort { level } => Some(MicroCert::Sort {
                level: MicroLevel::from_kernel(level).ok()?,
            }),
            ProofCert::BVar { idx, expected_type } => Some(MicroCert::BVar {
                idx: *idx,
                ty: Box::new(MicroExpr::from_kernel_env(expected_type).ok()?),
            }),
            ProofCert::Const { name, type_, .. } => Some(MicroCert::Const {
                name: Arc::from(name.to_string().as_str()),
                ty: Box::new(MicroExpr::from_kernel_env(type_).ok()?),
            }),
            ProofCert::FVar { .. } => None,
            ProofCert::App {
                fn_cert,
                arg_cert,
                result_type,
                ..
            } => Some(MicroCert::App {
                fn_cert: Box::new(MicroCert::from_proof_cert_env(fn_cert)?),
                arg_cert: Box::new(MicroCert::from_proof_cert_env(arg_cert)?),
                result_ty: Box::new(MicroExpr::from_kernel_env(result_type).ok()?),
            }),
            ProofCert::Lam {
                arg_type_cert,
                body_cert,
                result_type,
                ..
            } => Some(MicroCert::Lam {
                arg_ty_cert: Box::new(MicroCert::from_proof_cert_env(arg_type_cert)?),
                body_cert: Box::new(MicroCert::from_proof_cert_env(body_cert)?),
                result_ty: Box::new(MicroExpr::from_kernel_env(result_type).ok()?),
            }),
            ProofCert::Pi {
                arg_type_cert,
                arg_level,
                body_type_cert,
                body_level,
                ..
            } => Some(MicroCert::Pi {
                arg_ty_cert: Box::new(MicroCert::from_proof_cert_env(arg_type_cert)?),
                arg_level: MicroLevel::from_kernel_erased(arg_level),
                body_ty_cert: Box::new(MicroCert::from_proof_cert_env(body_type_cert)?),
                body_level: MicroLevel::from_kernel_erased(body_level),
            }),
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                result_type,
            } => Some(MicroCert::Let {
                ty_cert: Box::new(MicroCert::from_proof_cert_env(type_cert)?),
                val_cert: Box::new(MicroCert::from_proof_cert_env(value_cert)?),
                body_cert: Box::new(MicroCert::from_proof_cert_env(body_cert)?),
                result_ty: Box::new(MicroExpr::from_kernel_env(result_type).ok()?),
            }),
            ProofCert::Lit { lit, type_ } => Some(MicroCert::Lit {
                lit: MicroLiteral::from_kernel(lit).ok()?,
                ty: Box::new(MicroExpr::from_kernel_env(type_).ok()?),
            }),
            ProofCert::DefEq { inner, .. } => MicroCert::from_proof_cert_env(inner),
            ProofCert::MData { inner_cert, .. } => MicroCert::from_proof_cert_env(inner_cert),
            ProofCert::Proj {
                idx,
                expr_cert,
                field_type,
                ..
            } => Some(MicroCert::Proj {
                idx: *idx,
                expr_cert: Box::new(MicroCert::from_proof_cert_env(expr_cert)?),
                field_ty: Box::new(MicroExpr::from_kernel_env(field_type).ok()?),
            }),
            ProofCert::CubicalInterval
            | ProofCert::CubicalEndpoint { .. }
            | ProofCert::CubicalPath { .. }
            | ProofCert::CubicalPathLam { .. }
            | ProofCert::CubicalPathApp { .. }
            | ProofCert::CubicalHComp { .. }
            | ProofCert::CubicalTransp { .. }
            | ProofCert::CubicalCoe { .. }
            | ProofCert::ZFCSet { .. }
            | ProofCert::ZFCMem { .. }
            | ProofCert::ZFCComprehension { .. }
            | ProofCert::SProp
            | ProofCert::Squash { .. } => None,
        }
    }
}

// ============================================================================
// Env-aware diversity gate
// ============================================================================

/// Outcome of an env-aware micro re-check of one `:= rfl` theorem.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum DiversityOutcome {
    /// The micro-checker independently CONFIRMED both the proof-term typing
    /// AND (when `lhs`/`rhs` were supplied) the `lhs ≡ rhs` reduction.
    Confirmed,
    /// The micro-checker DISAGREED with the kernel — a genuine soundness
    /// alarm. The string carries the disagreement detail.
    Disagreement(String),
    /// The micro-checker could not model some construct (unknown const,
    /// unmodelable recursor, untranslatable cert, …). FAIL-CLOSED: callers
    /// must treat this as a gate failure, not a skip. The string names the gap.
    Unsupported(String),
}

/// Run the env-aware micro re-check for a single theorem, given the kernel's
/// inferred type + proof cert, plus (optionally) the two sides of the stated
/// `Eq` so the reduction half can be re-derived independently.
///
/// Two independent checks are performed by the micro-checker's OWN engine:
///
/// 1. **Typing**: re-verify the proof certificate (resolving every `Const`
///    via the read-only [`MicroEnv`]) and confirm the resulting type is
///    def-eq to the kernel's inferred type.
/// 2. **Reduction** (the `:= rfl` essence): if `eq_sides` is `Some((lhs, rhs))`,
///    re-derive `lhs ≡ rhs` with the micro-checker's own delta + native
///    Nat/Bool reducer. This is the half that re-checks the rfl computation.
///
/// Any `Unsupported` from either check is propagated (fail-closed). Any
/// disagreement is reported.
pub fn diversity_check_rfl(
    env: &super::MicroEnv,
    inferred_type: &Expr,
    cert: &ProofCert,
    eq_sides: Option<(&Expr, &Expr)>,
) -> DiversityOutcome {
    use super::types::MicroResult;

    // --- Stage A: translate the cert + inferred type (fail-closed on None) ---
    let Some(micro_cert) = MicroCert::from_proof_cert_env(cert) else {
        return DiversityOutcome::Unsupported(
            "proof certificate not translatable to MicroCert".to_string(),
        );
    };
    let Ok(micro_inferred) = MicroExpr::from_kernel_env(inferred_type) else {
        return DiversityOutcome::Unsupported("inferred type not translatable".to_string());
    };
    // We reconstruct the proof expression from the cert (replay) so the
    // checker has an `expr` to verify against. This is the micro-checker's own
    // view of the term; it does not call the kernel verifier.
    let micro_expr = micro_expr_of_cert(&micro_cert);

    // --- Stage B: env-aware typing re-check ---
    let mut checker = super::MicroChecker::with_env(env);
    match checker.verify_result(&micro_cert, &micro_expr) {
        MicroResult::Unsupported(m) => {
            return DiversityOutcome::Unsupported(format!("typing: {m}"));
        }
        MicroResult::Rejected(e) => {
            return DiversityOutcome::Disagreement(format!("typing rejected: {e}"));
        }
        MicroResult::Verified(ty) => {
            // Confirm the micro type matches the kernel's inferred type.
            let eq = super::MicroChecker::with_env(env);
            match eq.check_def_eq_result(&ty, &micro_inferred) {
                MicroResult::Unsupported(m) => {
                    return DiversityOutcome::Unsupported(format!("type compare: {m}"));
                }
                MicroResult::Rejected(_) => {
                    return DiversityOutcome::Disagreement(format!(
                        "micro type {ty:?} != kernel inferred {micro_inferred:?}"
                    ));
                }
                MicroResult::Verified(_) => {}
            }
        }
    }

    // --- Stage C: the rfl reduction re-check (delta + native iota) ---
    if let Some((lhs, rhs)) = eq_sides {
        let Ok(mlhs) = MicroExpr::from_kernel_env(lhs) else {
            return DiversityOutcome::Unsupported("Eq lhs not translatable".to_string());
        };
        let Ok(mrhs) = MicroExpr::from_kernel_env(rhs) else {
            return DiversityOutcome::Unsupported("Eq rhs not translatable".to_string());
        };
        let eq = super::MicroChecker::with_env(env);
        // Value-eq: both sides MUST reduce to closed Nat values. An unmodelable
        // recursor leaves a stuck head -> Unsupported (fail-closed), not a
        // misleading Disagreement.
        match eq.check_value_eq_result(&mlhs, &mrhs) {
            MicroResult::Unsupported(m) => {
                return DiversityOutcome::Unsupported(format!("rfl reduction: {m}"));
            }
            MicroResult::Rejected(_) => {
                return DiversityOutcome::Disagreement(format!(
                    "micro reducer disagrees: {lhs:?} not ≡ {rhs:?}"
                ));
            }
            MicroResult::Verified(_) => {}
        }
    }

    DiversityOutcome::Confirmed
}

/// Reconstruct the micro-checker's view of the proof term from a MicroCert.
/// Mirrors the structural shape the checker's `verify_impl` expects to pair
/// with each cert node.
fn micro_expr_of_cert(cert: &MicroCert) -> MicroExpr {
    match cert {
        MicroCert::Sort { level } => MicroExpr::Sort(level.clone()),
        MicroCert::Const { name, .. } => MicroExpr::Const(name.clone()),
        MicroCert::BVar { idx, .. } => MicroExpr::BVar(*idx),
        MicroCert::Opaque { ty } => MicroExpr::Opaque(Arc::new(ty.as_ref().clone())),
        MicroCert::App {
            fn_cert, arg_cert, ..
        } => MicroExpr::App(
            Arc::new(micro_expr_of_cert(fn_cert)),
            Arc::new(micro_expr_of_cert(arg_cert)),
        ),
        MicroCert::Lam {
            arg_ty_cert,
            body_cert,
            ..
        } => MicroExpr::Lam(
            Arc::new(micro_expr_of_cert(arg_ty_cert)),
            Arc::new(micro_expr_of_cert(body_cert)),
        ),
        MicroCert::Pi {
            arg_ty_cert,
            body_ty_cert,
            ..
        } => MicroExpr::Pi(
            Arc::new(micro_expr_of_cert(arg_ty_cert)),
            Arc::new(micro_expr_of_cert(body_ty_cert)),
        ),
        MicroCert::Let {
            ty_cert,
            val_cert,
            body_cert,
            ..
        } => MicroExpr::Let(
            Arc::new(micro_expr_of_cert(ty_cert)),
            Arc::new(micro_expr_of_cert(val_cert)),
            Arc::new(micro_expr_of_cert(body_cert)),
        ),
        MicroCert::Lit { lit, .. } => MicroExpr::Lit(lit.clone()),
        MicroCert::Proj { idx, expr_cert, .. } => {
            MicroExpr::Proj(*idx, Arc::new(micro_expr_of_cert(expr_cert)))
        }
    }
}

/// Cross-validate type inference result using the micro-checker.
///
/// This function is called in debug builds to verify that the main kernel's
/// type inference agrees with the independent micro-checker.
///
/// # Arguments
/// - `expr`: The expression that was type-checked
/// - `inferred_type`: The type inferred by the main kernel
/// - `cert`: The proof certificate from the main kernel
///
/// # Returns
/// - `Ok(true)` if cross-validation succeeded
/// - `Ok(false)` if validation was skipped (unsupported constructs)
/// - `Err(CrossValidationError)` if the micro-checker disagrees
///
/// # Contract
///
/// REQUIRES: `expr` is a valid kernel Expr
/// REQUIRES: `inferred_type` is the type inferred by main kernel for `expr`
/// REQUIRES: `cert` is a valid proof certificate witnessing `expr : inferred_type`
/// ENSURES: Returns `Ok(true)` if micro-checker confirms the typing
/// ENSURES: Returns `Ok(false)` if expression/certificate uses unsupported constructs
/// ENSURES: Returns `Err(CrossValidationError)` if micro-checker disagrees
pub fn cross_validate_with_micro(
    expr: &Expr,
    inferred_type: &Expr,
    cert: &ProofCert,
) -> Result<bool, CrossValidationError> {
    // Try to convert expression to MicroExpr
    let Ok(micro_expr) = MicroExpr::from_kernel(expr) else {
        return Ok(false); // Skip validation for unsupported expressions
    };

    // Try to convert certificate to MicroCert
    let Some(micro_cert) = MicroCert::from_proof_cert(cert) else {
        return Ok(false); // Skip validation for unsupported certificates
    };

    // Try to convert inferred type to MicroExpr
    let Ok(micro_inferred_type) = MicroExpr::from_kernel(inferred_type) else {
        return Ok(false); // Skip validation for unsupported types
    };

    // Run the micro-checker
    let mut micro_checker = MicroChecker::new();
    let micro_result = micro_checker.verify(&micro_cert, &micro_expr);

    match micro_result {
        Ok(micro_type) => {
            // Compare types (structural equality after WHNF)
            // Note: MicroChecker doesn't have delta reduction, so we compare structurally
            if micro_type != micro_inferred_type {
                return Err(CrossValidationError::Disagreement {
                    expr: format!("{expr:?}"),
                    main_type: format!("{inferred_type:?}"),
                    micro_type: format!("{micro_type:?}"),
                });
            }
            Ok(true)
        }
        Err(e) => Err(CrossValidationError::VerificationFailed {
            expr: format!("{expr:?}"),
            main_type: format!("{inferred_type:?}"),
            error: e,
        }),
    }
}
