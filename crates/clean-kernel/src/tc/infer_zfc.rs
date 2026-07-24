// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ZFC set-theoretic and impredicative mode type inference helpers.
//!
//! Extracted from `infer.rs` (#2594) — no logic changes.
//! SProp/Squash are grouped with ZFC because they share the mode-extension
//! pattern and are too small to justify a separate file.

#[cfg(not(debug_assertions))]
use crate::expr::{Expr, ExprKind, ZFCSetExpr};
#[cfg(not(debug_assertions))]
use crate::level::Level;
#[cfg(not(debug_assertions))]
use crate::name::Name;
use crate::tc::TypeChecker;
#[cfg(not(debug_assertions))]
use crate::tc::TypeError;
#[cfg(not(debug_assertions))]
use std::sync::LazyLock;

/// Pre-interned ZFC.Set name (avoids repeated allocation in ZFC type checks).
#[cfg(not(debug_assertions))]
static NAME_ZFC_SET: LazyLock<Name> = LazyLock::new(|| Name::from_string("ZFC.Set"));

impl<'env> TypeChecker<'env> {
    /// Infer the type of `ZFCSet(set_expr)`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_zfc_set(&self, set_expr: &ZFCSetExpr) -> Result<Expr, TypeError> {
        if self.mode != crate::mode::CleanMode::SetTheoretic {
            return Err(TypeError::ModeRequired {
                feature: "ZFCSet".to_string(),
                mode: "SetTheoretic".to_string(),
            });
        }
        // Validate Separation/Replacement operand types (pred : Set -> Prop,
        // func : Set -> Set). Other variants' sub-expressions must be ZFC.Set
        // but are checked by the cert path — the fast path defers.
        match set_expr {
            ZFCSetExpr::Separation { set, pred } => {
                let set_ty = self.infer_type_fast_impl(set)?;
                let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&set_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(set_ty),
                        location: None,
                    });
                }
                let pred_ty = self.infer_type_fast_impl(pred)?;
                let expected_pred_ty =
                    Expr::arrow(Expr::const_(NAME_ZFC_SET.clone(), vec![]), Expr::prop());
                if !self.is_def_eq(&pred_ty, &expected_pred_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_pred_ty),
                        inferred: Box::new(pred_ty),
                        location: None,
                    });
                }
            }
            ZFCSetExpr::Replacement { set, func } => {
                let set_ty = self.infer_type_fast_impl(set)?;
                let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
                if !self.is_def_eq(&set_ty, &expected_set_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_set_ty),
                        inferred: Box::new(set_ty),
                        location: None,
                    });
                }
                let func_ty = self.infer_type_fast_impl(func)?;
                let expected_func_ty = Expr::arrow(
                    Expr::const_(NAME_ZFC_SET.clone(), vec![]),
                    Expr::const_(NAME_ZFC_SET.clone(), vec![]),
                );
                if !self.is_def_eq(&func_ty, &expected_func_ty) {
                    return Err(TypeError::TypeMismatch {
                        expected: Box::new(expected_func_ty),
                        inferred: Box::new(func_ty),
                        location: None,
                    });
                }
            }
            _ => {} // Other variants: cert path validates sub-expressions
        }
        Ok(Expr::const_(NAME_ZFC_SET.clone(), vec![]))
    }

    /// Infer the type of `ZFCMem { element, set }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_zfc_mem(&self, element: &Expr, set: &Expr) -> Result<Expr, TypeError> {
        if self.mode != crate::mode::CleanMode::SetTheoretic {
            return Err(TypeError::ModeRequired {
                feature: "ZFCMem".to_string(),
                mode: "SetTheoretic".to_string(),
            });
        }

        let elem_ty = self.infer_type_fast_impl(element)?;
        let set_ty = self.infer_type_fast_impl(set)?;
        let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
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
        Ok(Expr::from_kind(ExprKind::Sort(Level::zero())))
    }

    /// Infer the type of `ZFCComprehension { domain, pred }`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_zfc_comprehension(
        &self,
        domain: &Expr,
        pred: &Expr,
    ) -> Result<Expr, TypeError> {
        if self.mode != crate::mode::CleanMode::SetTheoretic {
            return Err(TypeError::ModeRequired {
                feature: "ZFCComprehension".to_string(),
                mode: "SetTheoretic".to_string(),
            });
        }

        let domain_ty = self.infer_type_fast_impl(domain)?;
        let expected_set_ty = Expr::const_(NAME_ZFC_SET.clone(), vec![]);
        if !self.is_def_eq(&domain_ty, &expected_set_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_set_ty),
                inferred: Box::new(domain_ty),
                location: None,
            });
        }
        let pred_ty = self.infer_type_fast_impl(pred)?;
        let expected_pred_ty =
            Expr::arrow(Expr::const_(NAME_ZFC_SET.clone(), vec![]), Expr::prop());
        if !self.is_def_eq(&pred_ty, &expected_pred_ty) {
            return Err(TypeError::TypeMismatch {
                expected: Box::new(expected_pred_ty),
                inferred: Box::new(pred_ty),
                location: None,
            });
        }
        Ok(Expr::const_(NAME_ZFC_SET.clone(), vec![]))
    }

    /// Infer `SProp : Type 1`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_sprop(&self) -> Result<Expr, TypeError> {
        // SProp : Type 1 (strict propositions live at the same level as Prop)
        if self.mode != crate::mode::CleanMode::Impredicative
            && self.mode != crate::mode::CleanMode::Classical
            && self.mode != crate::mode::CleanMode::SetTheoretic
        {
            return Err(TypeError::ModeRequired {
                feature: "SProp".to_string(),
                mode: "Impredicative".to_string(),
            });
        }
        // SProp is a sort like Prop, so SProp : Type 1
        Ok(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))))
    }

    /// Infer the type of `Squash(inner)`.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_squash(&self, inner: &Expr) -> Result<Expr, TypeError> {
        // Squash A : SProp (when A : Sort u)
        if self.mode != crate::mode::CleanMode::Impredicative
            && self.mode != crate::mode::CleanMode::Classical
            && self.mode != crate::mode::CleanMode::SetTheoretic
        {
            return Err(TypeError::ModeRequired {
                feature: "Squash".to_string(),
                mode: "Impredicative".to_string(),
            });
        }
        // Check inner is a type
        let inner_ty = self.infer_type_fast_impl(inner)?;
        let inner_ty_whnf = self.whnf_impl(&inner_ty);
        if !matches!(inner_ty_whnf.kind, ExprKind::Sort(_)) {
            return Err(TypeError::ExpectedSort {
                ty: Box::new(inner_ty),
                location: None,
            });
        }
        // Squash A : SProp
        Ok(Expr::from_kind(ExprKind::SProp))
    }
}
