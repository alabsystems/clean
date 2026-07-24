// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hash functions for certificate compression (hash-consing).

use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use super::super::{ProofCert, ZFCSetCertKind};

/// Get a descriptive name for an expression variant (for error messages).
pub(crate) fn expr_name(expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::BVar(_) => "BVar",
        ExprKind::FVar(_) => "FVar",
        ExprKind::Sort(_) => "Sort",
        ExprKind::Const(_, _) => "Const",
        ExprKind::App(_, _) => "App",
        ExprKind::Lam(_, _, _) => "Lam",
        ExprKind::Pi(_, _, _) => "Pi",
        ExprKind::Let(_, _, _, _, _) => "Let",
        ExprKind::Lit(_) => "Lit",
        ExprKind::Proj(_, _, _) => "Proj",
        ExprKind::MData(_, _) => "MData",
        ExprKind::CubicalInterval => "CubicalInterval",
        ExprKind::CubicalI0 => "CubicalI0",
        ExprKind::CubicalI1 => "CubicalI1",
        ExprKind::CubicalPath { .. } => "CubicalPath",
        ExprKind::CubicalPathLam { .. } => "CubicalPathLam",
        ExprKind::CubicalPathApp { .. } => "CubicalPathApp",
        ExprKind::CubicalHComp { .. } => "CubicalHComp",
        ExprKind::CubicalTransp { .. } => "CubicalTransp",
        ExprKind::CubicalCoe { .. } => "CubicalCoe",
        ExprKind::ZFCSet(_) => "ZFCSet",
        ExprKind::ZFCMem { .. } => "ZFCMem",
        ExprKind::ZFCComprehension { .. } => "ZFCComprehension",
        ExprKind::SProp => "SProp",
        ExprKind::Squash(_) => "Squash",
    }
    .to_string()
}

// ---- Level hashing ----

/// Hash a level for deduplication.
pub(crate) fn hash_level(level: &Level) -> u64 {
    let mut hasher = DefaultHasher::new();
    hash_level_into(level, &mut hasher);
    hasher.finish()
}

fn hash_level_into(level: &Level, h: &mut DefaultHasher) {
    match level {
        Level::Zero => 0u8.hash(h),
        Level::Succ(l) => {
            1u8.hash(h);
            hash_level(l).hash(h);
        }
        Level::Max(l1, l2) => {
            2u8.hash(h);
            hash_level(l1).hash(h);
            hash_level(l2).hash(h);
        }
        Level::IMax(l1, l2) => {
            3u8.hash(h);
            hash_level(l1).hash(h);
            hash_level(l2).hash(h);
        }
        Level::Param(n) => {
            4u8.hash(h);
            n.hash(h);
        }
    }
}

// ---- Expression hashing ----

/// Hash an expression for deduplication.
pub(crate) fn hash_expr(expr: &Expr) -> u64 {
    let mut hasher = DefaultHasher::new();
    hash_expr_core(&expr.kind, &mut hasher);
    hasher.finish()
}

fn hash_expr_core(kind: &ExprKind, h: &mut DefaultHasher) {
    match kind {
        ExprKind::BVar(idx) => {
            0u8.hash(h);
            idx.hash(h);
        }
        ExprKind::FVar(id) => {
            1u8.hash(h);
            id.hash(h);
        }
        ExprKind::Sort(l) => {
            2u8.hash(h);
            hash_level(l).hash(h);
        }
        ExprKind::Const(n, ls) => {
            3u8.hash(h);
            n.hash(h);
            for l in ls {
                hash_level(l).hash(h);
            }
        }
        ExprKind::App(f, a) => {
            4u8.hash(h);
            hash_expr(f).hash(h);
            hash_expr(a).hash(h);
        }
        ExprKind::Lam(bi, ty, body) => {
            5u8.hash(h);
            bi.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(body).hash(h);
        }
        ExprKind::Pi(bi, ty, body) => {
            6u8.hash(h);
            bi.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(body).hash(h);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            7u8.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(val).hash(h);
            hash_expr(body).hash(h);
        }
        ExprKind::Lit(lit) => {
            8u8.hash(h);
            lit.hash(h);
        }
        ExprKind::Proj(n, idx, e) => {
            9u8.hash(h);
            n.hash(h);
            idx.hash(h);
            hash_expr(e).hash(h);
        }
        ExprKind::MData(md, e) => {
            10u8.hash(h);
            md.len().hash(h);
            hash_expr(e).hash(h);
        }
        _ => hash_expr_mode_specific(kind, h),
    }
}

fn hash_expr_mode_specific(kind: &ExprKind, h: &mut DefaultHasher) {
    match kind {
        ExprKind::CubicalInterval => 11u8.hash(h),
        ExprKind::CubicalI0 => 12u8.hash(h),
        ExprKind::CubicalI1 => 13u8.hash(h),
        ExprKind::CubicalPath { ty, left, right } => {
            14u8.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(left).hash(h);
            hash_expr(right).hash(h);
        }
        ExprKind::CubicalPathLam { body } => {
            15u8.hash(h);
            hash_expr(body).hash(h);
        }
        ExprKind::CubicalPathApp { path, arg } => {
            16u8.hash(h);
            hash_expr(path).hash(h);
            hash_expr(arg).hash(h);
        }
        ExprKind::CubicalHComp { ty, phi, u, base } => {
            17u8.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(phi).hash(h);
            hash_expr(u).hash(h);
            hash_expr(base).hash(h);
        }
        ExprKind::CubicalTransp { ty, phi, base } => {
            18u8.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(phi).hash(h);
            hash_expr(base).hash(h);
        }
        ExprKind::CubicalCoe { ty, r, s, base } => {
            26u8.hash(h);
            hash_expr(ty).hash(h);
            hash_expr(r).hash(h);
            hash_expr(s).hash(h);
            hash_expr(base).hash(h);
        }
        ExprKind::ZFCSet(set_expr) => {
            21u8.hash(h);
            std::mem::discriminant(set_expr).hash(h);
        }
        ExprKind::ZFCMem { element, set } => {
            22u8.hash(h);
            hash_expr(element).hash(h);
            hash_expr(set).hash(h);
        }
        ExprKind::ZFCComprehension { domain, pred } => {
            23u8.hash(h);
            hash_expr(domain).hash(h);
            hash_expr(pred).hash(h);
        }
        ExprKind::SProp => 24u8.hash(h),
        ExprKind::Squash(inner) => {
            25u8.hash(h);
            hash_expr(inner).hash(h);
        }
        _ => {} // Core cases handled by hash_expr_core
    }
}

// ---- Certificate hashing ----

/// Hash a certificate for deduplication.
pub(crate) fn hash_cert(cert: &ProofCert) -> u64 {
    let mut hasher = DefaultHasher::new();
    hash_cert_core(cert, &mut hasher);
    hasher.finish()
}

/// Hash core certificate variants (Sort through Lam).
fn hash_cert_core(cert: &ProofCert, h: &mut DefaultHasher) {
    match cert {
        ProofCert::Sort { level } => {
            0u8.hash(h);
            hash_level(level).hash(h);
        }
        ProofCert::BVar { idx, expected_type } => {
            1u8.hash(h);
            idx.hash(h);
            hash_expr(expected_type).hash(h);
        }
        ProofCert::FVar { id, type_ } => {
            2u8.hash(h);
            id.hash(h);
            hash_expr(type_).hash(h);
        }
        ProofCert::Const {
            name,
            levels,
            type_,
        } => {
            3u8.hash(h);
            name.hash(h);
            for l in levels {
                hash_level(l).hash(h);
            }
            hash_expr(type_).hash(h);
        }
        ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => {
            4u8.hash(h);
            hash_cert(fn_cert).hash(h);
            hash_expr(fn_type).hash(h);
            hash_cert(arg_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => {
            5u8.hash(h);
            binder_info.hash(h);
            hash_cert(arg_type_cert).hash(h);
            hash_cert(body_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        _ => hash_cert_compound(cert, h),
    }
}

/// Hash compound certificate variants (Pi through Proj).
fn hash_cert_compound(cert: &ProofCert, h: &mut DefaultHasher) {
    match cert {
        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => {
            6u8.hash(h);
            binder_info.hash(h);
            hash_cert(arg_type_cert).hash(h);
            hash_level(arg_level).hash(h);
            hash_cert(body_type_cert).hash(h);
            hash_level(body_level).hash(h);
        }
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => {
            7u8.hash(h);
            hash_cert(type_cert).hash(h);
            hash_cert(value_cert).hash(h);
            hash_cert(body_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::Lit { lit, type_ } => {
            8u8.hash(h);
            lit.hash(h);
            hash_expr(type_).hash(h);
        }
        ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => {
            9u8.hash(h);
            hash_cert(inner).hash(h);
            hash_expr(expected_type).hash(h);
            hash_expr(actual_type).hash(h);
            eq_steps.len().hash(h);
        }
        ProofCert::MData {
            metadata,
            inner_cert,
            result_type,
        } => {
            10u8.hash(h);
            metadata.len().hash(h);
            hash_cert(inner_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => {
            11u8.hash(h);
            struct_name.hash(h);
            idx.hash(h);
            hash_cert(expr_cert).hash(h);
            hash_expr(expr_type).hash(h);
            hash_expr(field_type).hash(h);
        }
        _ => hash_cert_mode_specific(cert, h),
    }
}

/// Hash cubical certificate variants.
fn hash_cert_mode_specific(cert: &ProofCert, h: &mut DefaultHasher) {
    match cert {
        ProofCert::CubicalInterval => 12u8.hash(h),
        ProofCert::CubicalEndpoint { is_one } => {
            13u8.hash(h);
            is_one.hash(h);
        }
        ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => {
            14u8.hash(h);
            hash_cert(ty_cert).hash(h);
            hash_level(ty_level).hash(h);
            hash_cert(left_cert).hash(h);
            hash_cert(right_cert).hash(h);
        }
        ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => {
            15u8.hash(h);
            hash_cert(body_cert).hash(h);
            hash_expr(body_type).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => {
            16u8.hash(h);
            hash_cert(path_cert).hash(h);
            hash_cert(arg_cert).hash(h);
            hash_expr(path_type).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => {
            17u8.hash(h);
            hash_cert(ty_cert).hash(h);
            hash_cert(phi_cert).hash(h);
            hash_cert(u_cert).hash(h);
            hash_cert(base_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => {
            18u8.hash(h);
            hash_cert(ty_cert).hash(h);
            hash_cert(phi_cert).hash(h);
            hash_cert(base_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => {
            26u8.hash(h);
            hash_cert(ty_cert).hash(h);
            hash_cert(r_cert).hash(h);
            hash_cert(s_cert).hash(h);
            hash_cert(base_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        _ => hash_cert_mode_zfc(cert, h),
    }
}

/// Hash ZFC/SProp certificate variants.
fn hash_cert_mode_zfc(cert: &ProofCert, h: &mut DefaultHasher) {
    match cert {
        ProofCert::ZFCSet { kind, result_type } => {
            21u8.hash(h);
            hash_zfc_set_kind(kind).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => {
            22u8.hash(h);
            hash_cert(elem_cert).hash(h);
            hash_cert(set_cert).hash(h);
        }
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => {
            23u8.hash(h);
            hash_cert(var_ty_cert).hash(h);
            hash_cert(pred_cert).hash(h);
            hash_expr(result_type).hash(h);
        }
        ProofCert::SProp => 24u8.hash(h),
        ProofCert::Squash { inner_cert } => {
            25u8.hash(h);
            hash_cert(inner_cert).hash(h);
        }
        _ => {} // Core cases handled by hash_cert_core
    }
}

// ---- ZFC set kind hashing ----

fn hash_zfc_set_kind(kind: &ZFCSetCertKind) -> u64 {
    let mut hasher = DefaultHasher::new();
    match kind {
        ZFCSetCertKind::Empty => 0u8.hash(&mut hasher),
        ZFCSetCertKind::Infinity => 1u8.hash(&mut hasher),
        ZFCSetCertKind::Singleton(c) => {
            2u8.hash(&mut hasher);
            hash_cert(c).hash(&mut hasher);
        }
        ZFCSetCertKind::Pair(c1, c2) => {
            3u8.hash(&mut hasher);
            hash_cert(c1).hash(&mut hasher);
            hash_cert(c2).hash(&mut hasher);
        }
        ZFCSetCertKind::Union(c) => {
            4u8.hash(&mut hasher);
            hash_cert(c).hash(&mut hasher);
        }
        ZFCSetCertKind::PowerSet(c) => {
            5u8.hash(&mut hasher);
            hash_cert(c).hash(&mut hasher);
        }
        ZFCSetCertKind::Separation {
            set_cert,
            pred_cert,
        } => {
            6u8.hash(&mut hasher);
            hash_cert(set_cert).hash(&mut hasher);
            hash_cert(pred_cert).hash(&mut hasher);
        }
        ZFCSetCertKind::Replacement {
            set_cert,
            func_cert,
        } => {
            7u8.hash(&mut hasher);
            hash_cert(set_cert).hash(&mut hasher);
            hash_cert(func_cert).hash(&mut hasher);
        }
        ZFCSetCertKind::Choice(c) => {
            8u8.hash(&mut hasher);
            hash_cert(c).hash(&mut hasher);
        }
    }
    hasher.finish()
}
