// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate-to-expression reification.
//!
//! Converts `ProofCert` nodes back into `Expr` values, needed when
//! the builder must reference sub-expressions during construction
//! (e.g., substituting an argument into a codomain).

use std::sync::Arc;

use crate::expr::{stack_safe, Expr, ExprKind, ZFCSetExpr};
use crate::name::Name;

use super::super::{ProofCert, ZFCSetCertKind};
use super::state::CertBuilder;

impl<'env> CertBuilder<'env> {
    pub(super) fn cert_to_expr(&self, cert: &ProofCert) -> Expr {
        stack_safe(|| self.cert_to_expr_impl(cert))
    }

    fn cert_to_expr_impl(&self, cert: &ProofCert) -> Expr {
        match cert {
            ProofCert::Sort { level } => Expr::from_kind(ExprKind::Sort(level.clone())),
            ProofCert::BVar { idx, .. } => Expr::from_kind(ExprKind::BVar(*idx)),
            ProofCert::FVar { id, .. } => Expr::from_kind(ExprKind::FVar(*id)),
            ProofCert::Const { name, levels, .. } => {
                Expr::from_kind(ExprKind::Const(name.clone(), levels.clone().into()))
            }
            ProofCert::App {
                fn_cert, arg_cert, ..
            } => {
                let f = self.cert_to_expr(fn_cert);
                let a = self.cert_to_expr(arg_cert);
                Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
            }
            ProofCert::Lam {
                binder_info,
                arg_type_cert,
                body_cert,
                ..
            } => {
                let arg_type = self.cert_to_expr(arg_type_cert);
                let body = self.cert_to_expr(body_cert);
                Expr::from_kind(ExprKind::Lam(
                    (*binder_info).into(),
                    Arc::new(arg_type),
                    Arc::new(body),
                ))
            }
            ProofCert::Pi {
                binder_info,
                arg_type_cert,
                body_type_cert,
                ..
            } => {
                let arg_type = self.cert_to_expr(arg_type_cert);
                let body_type = self.cert_to_expr(body_type_cert);
                Expr::from_kind(ExprKind::Pi(
                    (*binder_info).into(),
                    Arc::new(arg_type),
                    Arc::new(body_type),
                ))
            }
            ProofCert::Let {
                type_cert,
                value_cert,
                body_cert,
                ..
            } => {
                let ty = self.cert_to_expr(type_cert);
                let val = self.cert_to_expr(value_cert);
                let body = self.cert_to_expr(body_cert);
                Expr::from_kind(ExprKind::Let(
                    Name::anon(),
                    Arc::new(ty),
                    Arc::new(val),
                    Arc::new(body),
                    false,
                ))
            }
            ProofCert::Lit { lit, .. } => Expr::from_kind(ExprKind::Lit(lit.clone())),
            ProofCert::DefEq { inner, .. } => self.cert_to_expr(inner),
            ProofCert::MData {
                metadata,
                inner_cert,
                ..
            } => {
                let inner = self.cert_to_expr(inner_cert);
                Expr::from_kind(ExprKind::MData(metadata.clone(), Arc::new(inner)))
            }
            ProofCert::Proj {
                struct_name,
                idx,
                expr_cert,
                ..
            } => {
                let expr = self.cert_to_expr(expr_cert);
                Expr::from_kind(ExprKind::Proj(struct_name.clone(), *idx, Arc::new(expr)))
            }
            ProofCert::CubicalInterval => Expr::from_kind(ExprKind::CubicalInterval),
            ProofCert::CubicalEndpoint { is_one } => {
                if *is_one {
                    Expr::from_kind(ExprKind::CubicalI1)
                } else {
                    Expr::from_kind(ExprKind::CubicalI0)
                }
            }
            ProofCert::CubicalPath {
                ty_cert,
                left_cert,
                right_cert,
                ..
            } => Expr::from_kind(ExprKind::CubicalPath {
                ty: Arc::new(self.cert_to_expr(ty_cert)),
                left: Arc::new(self.cert_to_expr(left_cert)),
                right: Arc::new(self.cert_to_expr(right_cert)),
            }),
            ProofCert::CubicalPathLam { body_cert, .. } => {
                Expr::from_kind(ExprKind::CubicalPathLam {
                    body: Arc::new(self.cert_to_expr(body_cert)),
                })
            }
            ProofCert::CubicalPathApp {
                path_cert,
                arg_cert,
                ..
            } => Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(self.cert_to_expr(path_cert)),
                arg: Arc::new(self.cert_to_expr(arg_cert)),
            }),
            ProofCert::CubicalHComp {
                ty_cert,
                phi_cert,
                u_cert,
                base_cert,
                ..
            } => Expr::from_kind(ExprKind::CubicalHComp {
                ty: Arc::new(self.cert_to_expr(ty_cert)),
                phi: Arc::new(self.cert_to_expr(phi_cert)),
                u: Arc::new(self.cert_to_expr(u_cert)),
                base: Arc::new(self.cert_to_expr(base_cert)),
            }),
            ProofCert::CubicalTransp {
                ty_cert,
                phi_cert,
                base_cert,
                ..
            } => Expr::from_kind(ExprKind::CubicalTransp {
                ty: Arc::new(self.cert_to_expr(ty_cert)),
                phi: Arc::new(self.cert_to_expr(phi_cert)),
                base: Arc::new(self.cert_to_expr(base_cert)),
            }),
            ProofCert::CubicalCoe {
                ty_cert,
                r_cert,
                s_cert,
                base_cert,
                ..
            } => Expr::from_kind(ExprKind::CubicalCoe {
                ty: Arc::new(self.cert_to_expr(ty_cert)),
                r: Arc::new(self.cert_to_expr(r_cert)),
                s: Arc::new(self.cert_to_expr(s_cert)),
                base: Arc::new(self.cert_to_expr(base_cert)),
            }),
            ProofCert::ZFCSet { kind, .. } => {
                Expr::from_kind(ExprKind::ZFCSet(self.zfc_expr_from_cert(kind)))
            }
            ProofCert::ZFCMem {
                elem_cert,
                set_cert,
            } => Expr::from_kind(ExprKind::ZFCMem {
                element: Arc::new(self.cert_to_expr(elem_cert)),
                set: Arc::new(self.cert_to_expr(set_cert)),
            }),
            ProofCert::ZFCComprehension {
                var_ty_cert,
                pred_cert,
                ..
            } => Expr::from_kind(ExprKind::ZFCComprehension {
                domain: Arc::new(self.cert_to_expr(var_ty_cert)),
                pred: Arc::new(self.cert_to_expr(pred_cert)),
            }),
            ProofCert::SProp => Expr::from_kind(ExprKind::SProp),
            ProofCert::Squash { inner_cert } => {
                Expr::from_kind(ExprKind::Squash(Arc::new(self.cert_to_expr(inner_cert))))
            }
        }
    }

    pub(super) fn zfc_expr_from_cert(&self, kind: &ZFCSetCertKind) -> ZFCSetExpr {
        match kind {
            ZFCSetCertKind::Empty => ZFCSetExpr::Empty,
            ZFCSetCertKind::Infinity => ZFCSetExpr::Infinity,
            ZFCSetCertKind::Singleton(cert) => {
                ZFCSetExpr::Singleton(Arc::new(self.cert_to_expr(cert)))
            }
            ZFCSetCertKind::Pair(left, right) => ZFCSetExpr::Pair(
                Arc::new(self.cert_to_expr(left)),
                Arc::new(self.cert_to_expr(right)),
            ),
            ZFCSetCertKind::Union(cert) => ZFCSetExpr::Union(Arc::new(self.cert_to_expr(cert))),
            ZFCSetCertKind::PowerSet(cert) => {
                ZFCSetExpr::PowerSet(Arc::new(self.cert_to_expr(cert)))
            }
            ZFCSetCertKind::Separation {
                set_cert,
                pred_cert,
            } => ZFCSetExpr::Separation {
                set: Arc::new(self.cert_to_expr(set_cert)),
                pred: Arc::new(self.cert_to_expr(pred_cert)),
            },
            ZFCSetCertKind::Replacement {
                set_cert,
                func_cert,
            } => ZFCSetExpr::Replacement {
                set: Arc::new(self.cert_to_expr(set_cert)),
                func: Arc::new(self.cert_to_expr(func_cert)),
            },
            ZFCSetCertKind::Choice(cert) => ZFCSetExpr::Choice(Arc::new(self.cert_to_expr(cert))),
        }
    }
}
