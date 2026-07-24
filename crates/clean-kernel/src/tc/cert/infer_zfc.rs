// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ZFC set certificate generation.
//!
//! Handles certificate construction for ZFC set expression variants
//! (Empty, Infinity, Singleton, Pair, Union, PowerSet, Separation,
//! Replacement, Choice).

use crate::cert::ZFCSetCertKind;
use crate::expr::{Expr, ZFCSetExpr};
use crate::tc::TypeChecker;
use crate::TypeError;

impl<'env> TypeChecker<'env> {
    /// Generate a certificate for a ZFC set expression.
    pub(crate) fn infer_zfc_set_cert(
        &self,
        set_expr: &ZFCSetExpr,
    ) -> Result<ZFCSetCertKind, TypeError> {
        match set_expr {
            ZFCSetExpr::Empty => Ok(ZFCSetCertKind::Empty),
            ZFCSetExpr::Infinity => Ok(ZFCSetCertKind::Infinity),
            ZFCSetExpr::Singleton(e) => {
                let (_, cert) = self.infer_type_with_cert_impl(e)?;
                Ok(ZFCSetCertKind::Singleton(Box::new(cert)))
            }
            ZFCSetExpr::Pair(a, b) => {
                let (_, a_cert) = self.infer_type_with_cert_impl(a)?;
                let (_, b_cert) = self.infer_type_with_cert_impl(b)?;
                Ok(ZFCSetCertKind::Pair(Box::new(a_cert), Box::new(b_cert)))
            }
            ZFCSetExpr::Union(e) => {
                let (_, cert) = self.infer_type_with_cert_impl(e)?;
                Ok(ZFCSetCertKind::Union(Box::new(cert)))
            }
            ZFCSetExpr::PowerSet(e) => {
                let (_, cert) = self.infer_type_with_cert_impl(e)?;
                Ok(ZFCSetCertKind::PowerSet(Box::new(cert)))
            }
            ZFCSetExpr::Separation { set, pred } => {
                let (set_ty, set_cert) = self.infer_type_with_cert_impl(set)?;
                let expected_set_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&set_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(set_ty),
                        location: None,
                    });
                }
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
                Ok(ZFCSetCertKind::Separation {
                    set_cert: Box::new(set_cert),
                    pred_cert: Box::new(pred_cert),
                })
            }
            ZFCSetExpr::Replacement { set, func } => {
                let (set_ty, set_cert) = self.infer_type_with_cert_impl(set)?;
                let expected_set_ty = Expr::const_(super::NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&set_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(set_ty),
                        location: None,
                    });
                }
                let (func_ty, func_cert) = self.infer_type_with_cert_impl(func)?;
                let expected_func_ty = Expr::arrow(
                    Expr::const_(super::NAME_ZFC_SET.clone(), vec![]),
                    Expr::const_(super::NAME_ZFC_SET.clone(), vec![]),
                );
                if !self.is_def_eq(&func_ty, &expected_func_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_func_ty),
                        inferred: Box::new(func_ty),
                        location: None,
                    });
                }
                Ok(ZFCSetCertKind::Replacement {
                    set_cert: Box::new(set_cert),
                    func_cert: Box::new(func_cert),
                })
            }
            ZFCSetExpr::Choice(e) => {
                let (_, cert) = self.infer_type_with_cert_impl(e)?;
                Ok(ZFCSetCertKind::Choice(Box::new(cert)))
            }
        }
    }
}
