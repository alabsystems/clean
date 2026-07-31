// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Mode-specific certificate rules: ZFC set theory, SProp, Squash.
//!
//! Handles: ZFCSet, ZFCMem, ZFCComprehension, SProp, Squash.

use crate::expr::{Expr, ExprKind, ZFCSetExpr};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;
use std::sync::LazyLock;

use super::super::types::{CertError, ProofCert, ZFCSetCertKind};
use super::CertVerifier;

static NAME_ZFC_SET: LazyLock<Name> = LazyLock::new(|| Name::from_string("ZFC.Set"));

impl<'env> CertVerifier<'env> {
    /// ZFC Set: various set expressions : Set
    pub(crate) fn verify_zfc_set_expr(
        &mut self,
        kind: &ZFCSetCertKind,
        set_expr: &ZFCSetExpr,
    ) -> Result<Expr, CertError> {
        if self.mode != CleanMode::SetTheoretic {
            return Err(CertError::ModeRequired {
                feature: "ZFCSet".to_string(),
                required_mode: CleanMode::SetTheoretic,
                current_mode: self.mode,
            });
        }

        // Verify the specific set construction matches and sub-expressions type-check
        self.verify_zfc_set(kind, set_expr)?;

        // ZFC sets always have type ZFC.Set — independently derived, not from cert
        Ok(Expr::const_(NAME_ZFC_SET.clone(), vec![]))
    }

    /// ZFC Membership: element ∈ set : Prop
    pub(crate) fn verify_zfc_mem(
        &mut self,
        elem_cert: &ProofCert,
        set_cert: &ProofCert,
        element: &Expr,
        set: &Expr,
    ) -> Result<Expr, CertError> {
        if self.mode != CleanMode::SetTheoretic {
            return Err(CertError::ModeRequired {
                feature: "ZFCMem".to_string(),
                required_mode: CleanMode::SetTheoretic,
                current_mode: self.mode,
            });
        }

        // Verify element and set have type ZFC.Set
        let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
        let elem_ty = self.verify_recurse(elem_cert, element)?;
        if !self.def_eq_impl(&elem_ty, &expected_set_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_set_ty.clone()),
                actual: Box::new(elem_ty),
                location: "ZFCMem element type".to_string(),
            });
        }
        let set_ty = self.verify_recurse(set_cert, set)?;
        if !self.def_eq_impl(&set_ty, &expected_set_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_set_ty),
                actual: Box::new(set_ty),
                location: "ZFCMem set type".to_string(),
            });
        }

        // Membership is a proposition
        Ok(Expr::from_kind(ExprKind::Sort(Level::zero())))
    }

    /// ZFC Comprehension: { x ∈ domain | P(x) } : Set
    pub(crate) fn verify_zfc_comprehension(
        &mut self,
        var_ty_cert: &ProofCert,
        pred_cert: &ProofCert,
        domain: &Expr,
        pred: &Expr,
    ) -> Result<Expr, CertError> {
        if self.mode != CleanMode::SetTheoretic {
            return Err(CertError::ModeRequired {
                feature: "ZFCComprehension".to_string(),
                required_mode: CleanMode::SetTheoretic,
                current_mode: self.mode,
            });
        }

        // Verify domain has type ZFC.Set
        let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
        let domain_ty = self.verify_recurse(var_ty_cert, domain)?;
        if !self.def_eq_impl(&domain_ty, &expected_set_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_set_ty),
                actual: Box::new(domain_ty),
                location: "ZFCComprehension domain type".to_string(),
            });
        }

        // Verify pred : Set -> Prop
        let pred_ty = self.verify_recurse(pred_cert, pred)?;
        let expected_pred_ty =
            Expr::arrow(Expr::const_(NAME_ZFC_SET.clone(), vec![]), Expr::prop());
        if !self.def_eq_impl(&pred_ty, &expected_pred_ty) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected_pred_ty),
                actual: Box::new(pred_ty),
                location: "ZFCComprehension predicate type".to_string(),
            });
        }

        // Comprehension always produces ZFC.Set — independently derived
        Ok(Expr::const_(NAME_ZFC_SET.clone(), vec![]))
    }

    /// SProp: SProp : Type 1 (strict propositions)
    pub(crate) fn verify_sprop(&self) -> Result<Expr, CertError> {
        if self.mode != CleanMode::Impredicative
            && self.mode != CleanMode::Classical
            && self.mode != CleanMode::SetTheoretic
        {
            return Err(CertError::ModeRequired {
                feature: "SProp".to_string(),
                required_mode: CleanMode::Impredicative,
                current_mode: self.mode,
            });
        }
        Ok(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))))
    }

    /// Squash: Squash(A) : SProp (when A : Sort u)
    pub(crate) fn verify_squash(
        &mut self,
        inner_cert: &ProofCert,
        inner: &Expr,
    ) -> Result<Expr, CertError> {
        if self.mode != CleanMode::Impredicative
            && self.mode != CleanMode::Classical
            && self.mode != CleanMode::SetTheoretic
        {
            return Err(CertError::ModeRequired {
                feature: "Squash".to_string(),
                required_mode: CleanMode::Impredicative,
                current_mode: self.mode,
            });
        }
        // Verify inner expression is a type (Sort u)
        let inner_ty = self.verify_recurse(inner_cert, inner)?;
        let inner_ty_whnf = self.whnf_impl(&inner_ty);
        if !matches!(inner_ty_whnf.kind, ExprKind::Sort(_)) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
                actual: Box::new(inner_ty),
                location: "Squash inner type".to_string(),
            });
        }
        // Squash A : SProp
        Ok(Expr::from_kind(ExprKind::SProp))
    }

    /// Verify a sub-expression has type ZFC.Set, returning an error if not.
    fn verify_zfc_set_operand(
        &mut self,
        cert: &ProofCert,
        expr: &Expr,
        location: &str,
    ) -> Result<(), CertError> {
        let expected = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
        let actual = self.verify_recurse(cert, expr)?;
        if !self.def_eq_impl(&actual, &expected) {
            return Err(CertError::TypeMismatch {
                expected: Box::new(expected),
                actual: Box::new(actual),
                location: location.to_string(),
            });
        }
        Ok(())
    }

    /// Helper to verify ZFC set expression matches certificate kind
    fn verify_zfc_set(
        &mut self,
        kind: &ZFCSetCertKind,
        expr: &ZFCSetExpr,
    ) -> Result<(), CertError> {
        match (kind, expr) {
            (ZFCSetCertKind::Empty, ZFCSetExpr::Empty) => Ok(()),
            (ZFCSetCertKind::Infinity, ZFCSetExpr::Infinity) => Ok(()),
            (ZFCSetCertKind::Singleton(cert), ZFCSetExpr::Singleton(e)) => {
                self.verify_zfc_set_operand(cert, e, "ZFC Singleton element")
            }
            (ZFCSetCertKind::Pair(c1, c2), ZFCSetExpr::Pair(e1, e2)) => {
                self.verify_zfc_set_operand(c1, e1, "ZFC Pair first")?;
                self.verify_zfc_set_operand(c2, e2, "ZFC Pair second")
            }
            (ZFCSetCertKind::Union(cert), ZFCSetExpr::Union(e)) => {
                self.verify_zfc_set_operand(cert, e, "ZFC Union operand")
            }
            (ZFCSetCertKind::PowerSet(cert), ZFCSetExpr::PowerSet(e)) => {
                self.verify_zfc_set_operand(cert, e, "ZFC PowerSet operand")
            }
            (
                ZFCSetCertKind::Separation {
                    set_cert,
                    pred_cert,
                },
                ZFCSetExpr::Separation { set, pred },
            ) => {
                self.verify_zfc_set_operand(set_cert, set, "ZFC Separation set")?;
                // Verify pred : Set -> Prop
                let pred_ty = self.verify_recurse(pred_cert, pred)?;
                let expected_pred_ty =
                    Expr::arrow(Expr::const_(NAME_ZFC_SET.clone(), vec![]), Expr::prop());
                if !self.def_eq_impl(&pred_ty, &expected_pred_ty) {
                    return Err(CertError::TypeMismatch {
                        expected: Box::new(expected_pred_ty),
                        actual: Box::new(pred_ty),
                        location: "ZFC Separation predicate type".to_string(),
                    });
                }
                Ok(())
            }
            (
                ZFCSetCertKind::Replacement {
                    set_cert,
                    func_cert,
                },
                ZFCSetExpr::Replacement { set, func },
            ) => {
                self.verify_zfc_set_operand(set_cert, set, "ZFC Replacement set")?;
                // Verify func : Set -> Set
                let func_ty = self.verify_recurse(func_cert, func)?;
                let expected_func_ty = Expr::arrow(
                    Expr::const_(NAME_ZFC_SET.clone(), vec![]),
                    Expr::const_(NAME_ZFC_SET.clone(), vec![]),
                );
                if !self.def_eq_impl(&func_ty, &expected_func_ty) {
                    return Err(CertError::TypeMismatch {
                        expected: Box::new(expected_func_ty),
                        actual: Box::new(func_ty),
                        location: "ZFC Replacement function type".to_string(),
                    });
                }
                Ok(())
            }
            (ZFCSetCertKind::Choice(cert), ZFCSetExpr::Choice(e)) => {
                self.verify_zfc_set_operand(cert, e, "ZFC Choice operand")
            }
            _ => Err(CertError::StructureMismatch {
                expected: format!("{kind:?}"),
                actual: format!("{expr:?}"),
            }),
        }
    }
}
