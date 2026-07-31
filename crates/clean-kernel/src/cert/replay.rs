// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Proof Replay - reconstructs expressions from certificates.

use super::{CertError, CertVerifier, ProofCert, ZFCSetCertKind};
use crate::expr::{stack_safe, Expr, ExprKind, ZFCSetExpr};
use crate::name::Name;
use std::sync::Arc;

/// Reconstructs an expression from a proof certificate.
///
/// Stack-safe: every recursive descent re-enters this `stack_safe` boundary so
/// `stacker::maybe_grow` can allocate another segment before the current one is
/// exhausted. A single boundary around the root is insufficient because one
/// grown segment is still finite for adversarially deep certificate trees.
///
/// The verifier's `verify()` follows the same guarded-recursion pattern.
pub fn replay_cert(cert: &ProofCert) -> Expr {
    stack_safe(|| replay_cert_impl(cert))
}

/// Inner implementation — dispatches to sub-functions for each certificate family.
fn replay_cert_impl(cert: &ProofCert) -> Expr {
    match cert {
        ProofCert::Sort { .. }
        | ProofCert::BVar { .. }
        | ProofCert::FVar { .. }
        | ProofCert::Const { .. }
        | ProofCert::App { .. }
        | ProofCert::Lam { .. }
        | ProofCert::Pi { .. }
        | ProofCert::Let { .. }
        | ProofCert::Lit { .. }
        | ProofCert::DefEq { .. }
        | ProofCert::MData { .. }
        | ProofCert::Proj { .. } => replay_cert_core(cert),
        ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::CubicalPath { .. }
        | ProofCert::CubicalPathLam { .. }
        | ProofCert::CubicalPathApp { .. }
        | ProofCert::CubicalHComp { .. }
        | ProofCert::CubicalTransp { .. }
        | ProofCert::CubicalCoe { .. } => replay_cert_cubical(cert),
        ProofCert::ZFCSet { .. }
        | ProofCert::ZFCMem { .. }
        | ProofCert::ZFCComprehension { .. }
        | ProofCert::SProp
        | ProofCert::Squash { .. } => replay_cert_modes(cert),
    }
}

/// Replay core certificate forms: Sort, BVar, FVar, Const, App, Lam, Pi, Let, Lit, DefEq, MData, Proj.
fn replay_cert_core(cert: &ProofCert) -> Expr {
    match cert {
        ProofCert::Sort { level } => Expr::from_kind(ExprKind::Sort(level.clone())),
        ProofCert::BVar { idx, .. } => Expr::from_kind(ExprKind::BVar(*idx)),
        ProofCert::FVar { id, .. } => Expr::from_kind(ExprKind::FVar(*id)),
        ProofCert::Const { name, levels, .. } => Expr::const_(name.clone(), levels.clone()),
        ProofCert::App {
            fn_cert, arg_cert, ..
        } => Expr::from_kind(ExprKind::App(
            replay_cert(fn_cert).into(),
            replay_cert(arg_cert).into(),
        )),
        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => {
            let domain = match &result_type.as_ref().kind {
                ExprKind::Pi(_, dom, _) => dom.as_ref().clone(),
                _ => extract_type_from_sort_cert(arg_type_cert),
            };
            Expr::from_kind(ExprKind::Lam(
                (*binder_info).into(),
                Arc::new(domain),
                Arc::new(replay_cert(body_cert)),
            ))
        }
        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            body_type_cert,
            ..
        } => Expr::from_kind(ExprKind::Pi(
            (*binder_info).into(),
            Arc::new(extract_type_from_sort_cert(arg_type_cert)),
            Arc::new(extract_type_from_sort_cert(body_type_cert)),
        )),
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            ..
        } => Expr::let_named(
            Name::anon(),
            extract_type_from_sort_cert(type_cert),
            replay_cert(value_cert),
            replay_cert(body_cert),
            false,
        ),
        ProofCert::Lit { lit, .. } => Expr::from_kind(ExprKind::Lit(lit.clone())),
        ProofCert::DefEq { inner, .. } => replay_cert(inner),
        ProofCert::MData {
            metadata,
            inner_cert,
            ..
        } => Expr::from_kind(ExprKind::MData(
            metadata.clone(),
            replay_cert(inner_cert).into(),
        )),
        ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            ..
        } => Expr::proj(struct_name.clone(), *idx, replay_cert(expr_cert)),
        _ => unreachable!("replay_cert_core only handles core variants"),
    }
}

/// Replay cubical certificate forms.
fn replay_cert_cubical(cert: &ProofCert) -> Expr {
    match cert {
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
            ty: replay_cert(ty_cert).into(),
            left: replay_cert(left_cert).into(),
            right: replay_cert(right_cert).into(),
        }),
        ProofCert::CubicalPathLam { body_cert, .. } => Expr::from_kind(ExprKind::CubicalPathLam {
            body: replay_cert(body_cert).into(),
        }),
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            ..
        } => Expr::from_kind(ExprKind::CubicalPathApp {
            path: replay_cert(path_cert).into(),
            arg: replay_cert(arg_cert).into(),
        }),
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            ..
        } => Expr::from_kind(ExprKind::CubicalHComp {
            ty: replay_cert(ty_cert).into(),
            phi: replay_cert(phi_cert).into(),
            u: replay_cert(u_cert).into(),
            base: replay_cert(base_cert).into(),
        }),
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            ..
        } => Expr::from_kind(ExprKind::CubicalTransp {
            ty: replay_cert(ty_cert).into(),
            phi: replay_cert(phi_cert).into(),
            base: replay_cert(base_cert).into(),
        }),
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            ..
        } => Expr::from_kind(ExprKind::CubicalCoe {
            ty: replay_cert(ty_cert).into(),
            r: replay_cert(r_cert).into(),
            s: replay_cert(s_cert).into(),
            base: replay_cert(base_cert).into(),
        }),
        _ => unreachable!("replay_cert_cubical only handles cubical variants"),
    }
}

/// Replay mode-specific certificate forms: ZFC, SProp, Squash.
fn replay_cert_modes(cert: &ProofCert) -> Expr {
    match cert {
        ProofCert::ZFCSet { kind, .. } => Expr::from_kind(ExprKind::ZFCSet(replay_zfc_set(kind))),
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => Expr::from_kind(ExprKind::ZFCMem {
            element: replay_cert(elem_cert).into(),
            set: replay_cert(set_cert).into(),
        }),
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            ..
        } => Expr::from_kind(ExprKind::ZFCComprehension {
            domain: replay_cert(var_ty_cert).into(),
            pred: replay_cert(pred_cert).into(),
        }),
        ProofCert::SProp => Expr::from_kind(ExprKind::SProp),
        ProofCert::Squash { inner_cert } => {
            Expr::from_kind(ExprKind::Squash(replay_cert(inner_cert).into()))
        }
        _ => unreachable!("replay_cert_modes only handles mode-specific variants"),
    }
}

fn replay_zfc_set(kind: &ZFCSetCertKind) -> ZFCSetExpr {
    match kind {
        ZFCSetCertKind::Empty => ZFCSetExpr::Empty,
        ZFCSetCertKind::Infinity => ZFCSetExpr::Infinity,
        ZFCSetCertKind::Singleton(cert) => ZFCSetExpr::Singleton(replay_cert(cert).into()),
        ZFCSetCertKind::Pair(c1, c2) => {
            ZFCSetExpr::Pair(replay_cert(c1).into(), replay_cert(c2).into())
        }
        ZFCSetCertKind::Union(cert) => ZFCSetExpr::Union(replay_cert(cert).into()),
        ZFCSetCertKind::PowerSet(cert) => ZFCSetExpr::PowerSet(replay_cert(cert).into()),
        ZFCSetCertKind::Separation {
            set_cert,
            pred_cert,
        } => ZFCSetExpr::Separation {
            set: replay_cert(set_cert).into(),
            pred: replay_cert(pred_cert).into(),
        },
        ZFCSetCertKind::Replacement {
            set_cert,
            func_cert,
        } => ZFCSetExpr::Replacement {
            set: replay_cert(set_cert).into(),
            func: replay_cert(func_cert).into(),
        },
        ZFCSetCertKind::Choice(cert) => ZFCSetExpr::Choice(replay_cert(cert).into()),
    }
}

fn extract_type_from_sort_cert(cert: &ProofCert) -> Expr {
    stack_safe(|| extract_type_from_sort_cert_impl(cert))
}

fn extract_type_from_sort_cert_impl(cert: &ProofCert) -> Expr {
    match cert {
        ProofCert::Sort { level } => Expr::from_kind(ExprKind::Sort(level.clone())),
        ProofCert::BVar { idx, .. } => Expr::from_kind(ExprKind::BVar(*idx)),
        ProofCert::FVar { id, .. } => Expr::from_kind(ExprKind::FVar(*id)),
        ProofCert::Const { name, levels, .. } => Expr::const_(name.clone(), levels.clone()),
        ProofCert::App { .. }
        | ProofCert::Lam { .. }
        | ProofCert::Pi { .. }
        | ProofCert::Let { .. }
        | ProofCert::Proj { .. } => replay_cert(cert),
        ProofCert::Lit { lit, .. } => Expr::from_kind(ExprKind::Lit(lit.clone())),
        ProofCert::DefEq { inner, .. } => extract_type_from_sort_cert(inner),
        ProofCert::MData {
            metadata,
            inner_cert,
            ..
        } => Expr::from_kind(ExprKind::MData(
            metadata.clone(),
            extract_type_from_sort_cert(inner_cert).into(),
        )),
        _ => replay_cert(cert),
    }
}

impl<'env> CertVerifier<'env> {
    /// Replay a certificate and verify the result.
    ///
    /// REQUIRES: `cert` is a well-formed proof certificate
    /// REQUIRES: All Consts in `cert` are defined in the verifier's environment
    /// ENSURES: On success, `result.0` is the expression reconstructed from `cert`
    /// ENSURES: On success, `result.1` is the verified type of `result.0`
    /// ENSURES: `verify(cert, result.0)` would return `result.1`
    pub fn replay_and_verify(&mut self, cert: &ProofCert) -> Result<(Expr, Expr), CertError> {
        let expr = replay_cert(cert);
        let ty = self.verify(cert, &expr)?;
        Ok((expr, ty))
    }
}
