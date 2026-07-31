// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FVar→BVar certificate conversion.
//!
//! When the type checker processes a lambda/pi/let body, it opens BVars into FVars.
//! The certificate produced refers to FVars, but the original expression uses BVars.
//! These functions convert FVar certificates back to BVar certificates so verification
//! can proceed against the original expression.

use crate::cert::ProofCert;
use crate::expr::{stack_safe, FVarId};
use crate::tc::local_context::checked_add_u32;

/// Convert FVar certificates back to BVar certificates.
/// Stack-safe wrapper for deeply nested proof certificates.
pub(crate) fn convert_fvar_cert_to_bvar(cert: ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    convert_fvar_cert_to_bvar_ref(&cert, fvar_id, depth)
}

fn convert_fvar_cert_to_bvar_ref(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    stack_safe(|| convert_fvar_cert_to_bvar_impl(cert, fvar_id, depth))
}

fn convert_fvar_cert_to_bvar_impl(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    match cert {
        // Leaf cases: no recursive cert conversion, only abstract types
        ProofCert::FVar { .. }
        | ProofCert::Sort { .. }
        | ProofCert::BVar { .. }
        | ProofCert::Const { .. }
        | ProofCert::Lit { .. } => rebind_leaf(cert, fvar_id, depth),
        // Core CIC binder forms (depth-incrementing)
        ProofCert::Lam { .. } | ProofCert::Pi { .. } | ProofCert::Let { .. } => {
            rebind_binder(cert, fvar_id, depth)
        }
        // Core CIC compound forms
        ProofCert::App { .. }
        | ProofCert::DefEq { .. }
        | ProofCert::MData { .. }
        | ProofCert::Proj { .. } => rebind_compound(cert, fvar_id, depth),
        // Cubical mode extensions
        ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::CubicalPath { .. }
        | ProofCert::CubicalPathLam { .. }
        | ProofCert::CubicalPathApp { .. }
        | ProofCert::CubicalHComp { .. }
        | ProofCert::CubicalTransp { .. }
        | ProofCert::CubicalCoe { .. } => rebind_cubical(cert, fvar_id, depth),
        // ZFC and Impredicative mode extensions
        _ => rebind_zfc_impredicative(cert, fvar_id, depth),
    }
}

/// Leaf cert cases: FVar, Sort, BVar, Const, Lit — abstract types only.
fn rebind_leaf(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    match cert {
        ProofCert::FVar { id, type_ } if *id == fvar_id => ProofCert::BVar {
            idx: depth,
            expected_type: Box::new(type_.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::FVar { id, type_ } => ProofCert::FVar {
            id: *id,
            type_: Box::new(type_.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::Sort { level } => ProofCert::Sort {
            level: level.clone(),
        },
        ProofCert::BVar { idx, expected_type } => ProofCert::BVar {
            idx: if *idx >= depth {
                checked_add_u32(*idx, 1, "abstract_fvar bvar shift")
            } else {
                *idx
            },
            expected_type: Box::new(expected_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::Const {
            name,
            levels,
            type_,
        } => ProofCert::Const {
            name: name.clone(),
            levels: levels.clone(),
            type_: Box::new(type_.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::Lit { lit, type_ } => ProofCert::Lit {
            lit: lit.clone(),
            type_: Box::new(type_.abstract_fvar_at(fvar_id, depth)),
        },
        _ => unreachable!("rebind_leaf called with non-leaf cert"),
    }
}

/// Binder cert cases: Lam, Pi, Let — depth-incrementing body recursion.
fn rebind_binder(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
    match cert {
        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => ProofCert::Lam {
            binder_info: *binder_info,
            arg_type_cert: Box::new(convert_fvar_cert_to_bvar_ref(arg_type_cert, fvar_id, depth)),
            body_cert: Box::new(convert_fvar_cert_to_bvar_ref(body_cert, fvar_id, d1)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => ProofCert::Pi {
            binder_info: *binder_info,
            arg_type_cert: Box::new(convert_fvar_cert_to_bvar_ref(arg_type_cert, fvar_id, depth)),
            arg_level: arg_level.clone(),
            body_type_cert: Box::new(convert_fvar_cert_to_bvar_ref(body_type_cert, fvar_id, d1)),
            body_level: body_level.clone(),
        },
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => ProofCert::Let {
            type_cert: Box::new(convert_fvar_cert_to_bvar_ref(type_cert, fvar_id, depth)),
            value_cert: Box::new(convert_fvar_cert_to_bvar_ref(value_cert, fvar_id, depth)),
            body_cert: Box::new(convert_fvar_cert_to_bvar_ref(body_cert, fvar_id, d1)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        _ => unreachable!("rebind_binder called with non-binder cert"),
    }
}

/// Compound cert cases: App, DefEq, MData, Proj — recursive on subcerts and types.
fn rebind_compound(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    match cert {
        ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => ProofCert::App {
            fn_cert: Box::new(convert_fvar_cert_to_bvar_ref(fn_cert, fvar_id, depth)),
            fn_type: Box::new(fn_type.abstract_fvar_at(fvar_id, depth)),
            arg_cert: Box::new(convert_fvar_cert_to_bvar_ref(arg_cert, fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => ProofCert::DefEq {
            inner: Box::new(convert_fvar_cert_to_bvar_ref(inner, fvar_id, depth)),
            expected_type: Box::new(expected_type.abstract_fvar_at(fvar_id, depth)),
            actual_type: Box::new(actual_type.abstract_fvar_at(fvar_id, depth)),
            eq_steps: eq_steps.clone(),
        },
        ProofCert::MData {
            metadata,
            inner_cert,
            result_type,
        } => ProofCert::MData {
            metadata: metadata.clone(),
            inner_cert: Box::new(convert_fvar_cert_to_bvar_ref(inner_cert, fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::Proj {
            struct_name,
            idx,
            expr_cert,
            expr_type,
            field_type,
        } => ProofCert::Proj {
            struct_name: struct_name.clone(),
            idx: *idx,
            expr_cert: Box::new(convert_fvar_cert_to_bvar_ref(expr_cert, fvar_id, depth)),
            expr_type: Box::new(expr_type.abstract_fvar_at(fvar_id, depth)),
            field_type: Box::new(field_type.abstract_fvar_at(fvar_id, depth)),
        },
        _ => unreachable!("rebind_compound called with non-compound cert"),
    }
}

/// Mode-specific cert cases: Cubical extensions.
fn rebind_cubical(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    match cert {
        ProofCert::CubicalInterval => ProofCert::CubicalInterval,
        ProofCert::CubicalEndpoint { is_one } => ProofCert::CubicalEndpoint { is_one: *is_one },
        ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => ProofCert::CubicalPath {
            ty_cert: Box::new(convert_fvar_cert_to_bvar_ref(ty_cert, fvar_id, depth)),
            ty_level: ty_level.clone(),
            left_cert: Box::new(convert_fvar_cert_to_bvar_ref(left_cert, fvar_id, depth)),
            right_cert: Box::new(convert_fvar_cert_to_bvar_ref(right_cert, fvar_id, depth)),
        },
        ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ProofCert::CubicalPathLam {
                body_cert: Box::new(convert_fvar_cert_to_bvar_ref(body_cert, fvar_id, d1)),
                body_type: Box::new(body_type.abstract_fvar_at(fvar_id, depth)),
                result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
            }
        }
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => ProofCert::CubicalPathApp {
            path_cert: Box::new(convert_fvar_cert_to_bvar_ref(path_cert, fvar_id, depth)),
            arg_cert: Box::new(convert_fvar_cert_to_bvar_ref(arg_cert, fvar_id, depth)),
            path_type: Box::new(path_type.abstract_fvar_at(fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalHComp {
            ty_cert: Box::new(convert_fvar_cert_to_bvar_ref(ty_cert, fvar_id, depth)),
            phi_cert: Box::new(convert_fvar_cert_to_bvar_ref(phi_cert, fvar_id, depth)),
            u_cert: Box::new(convert_fvar_cert_to_bvar_ref(u_cert, fvar_id, depth)),
            base_cert: Box::new(convert_fvar_cert_to_bvar_ref(base_cert, fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalTransp {
            ty_cert: Box::new(convert_fvar_cert_to_bvar_ref(ty_cert, fvar_id, depth)),
            phi_cert: Box::new(convert_fvar_cert_to_bvar_ref(phi_cert, fvar_id, depth)),
            base_cert: Box::new(convert_fvar_cert_to_bvar_ref(base_cert, fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalCoe {
            ty_cert: Box::new(convert_fvar_cert_to_bvar_ref(ty_cert, fvar_id, depth)),
            r_cert: Box::new(convert_fvar_cert_to_bvar_ref(r_cert, fvar_id, depth)),
            s_cert: Box::new(convert_fvar_cert_to_bvar_ref(s_cert, fvar_id, depth)),
            base_cert: Box::new(convert_fvar_cert_to_bvar_ref(base_cert, fvar_id, depth)),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        _ => unreachable!("rebind_cubical called with non-Cubical cert"),
    }
}

/// Mode-specific cert cases: ZFC and Impredicative extensions.
fn rebind_zfc_impredicative(cert: &ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    match cert {
        ProofCert::ZFCSet { kind, result_type } => ProofCert::ZFCSet {
            kind: convert_fvar_in_zfc_set_kind(kind, fvar_id, depth),
            result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
        },
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => ProofCert::ZFCMem {
            elem_cert: Box::new(convert_fvar_cert_to_bvar_ref(elem_cert, fvar_id, depth)),
            set_cert: Box::new(convert_fvar_cert_to_bvar_ref(set_cert, fvar_id, depth)),
        },
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ProofCert::ZFCComprehension {
                var_ty_cert: Box::new(convert_fvar_cert_to_bvar_ref(var_ty_cert, fvar_id, depth)),
                pred_cert: Box::new(convert_fvar_cert_to_bvar_ref(pred_cert, fvar_id, d1)),
                result_type: Box::new(result_type.abstract_fvar_at(fvar_id, depth)),
            }
        }
        ProofCert::SProp => ProofCert::SProp,
        ProofCert::Squash { inner_cert } => ProofCert::Squash {
            inner_cert: Box::new(convert_fvar_cert_to_bvar_ref(inner_cert, fvar_id, depth)),
        },
        _ => unreachable!("rebind_zfc_impredicative called with non-ZFC/Impredicative cert"),
    }
}

/// Helper to convert FVar occurrences in ZFC set certificate kind
fn convert_fvar_in_zfc_set_kind(
    kind: &crate::cert::ZFCSetCertKind,
    fvar_id: FVarId,
    depth: u32,
) -> crate::cert::ZFCSetCertKind {
    use crate::cert::ZFCSetCertKind;
    match kind {
        ZFCSetCertKind::Empty => ZFCSetCertKind::Empty,
        ZFCSetCertKind::Infinity => ZFCSetCertKind::Infinity,
        ZFCSetCertKind::Singleton(c) => {
            ZFCSetCertKind::Singleton(Box::new(convert_fvar_cert_to_bvar_ref(c, fvar_id, depth)))
        }
        ZFCSetCertKind::Pair(c1, c2) => ZFCSetCertKind::Pair(
            Box::new(convert_fvar_cert_to_bvar_ref(c1, fvar_id, depth)),
            Box::new(convert_fvar_cert_to_bvar_ref(c2, fvar_id, depth)),
        ),
        ZFCSetCertKind::Union(c) => {
            ZFCSetCertKind::Union(Box::new(convert_fvar_cert_to_bvar_ref(c, fvar_id, depth)))
        }
        ZFCSetCertKind::PowerSet(c) => {
            ZFCSetCertKind::PowerSet(Box::new(convert_fvar_cert_to_bvar_ref(c, fvar_id, depth)))
        }
        ZFCSetCertKind::Separation {
            set_cert,
            pred_cert,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ZFCSetCertKind::Separation {
                set_cert: Box::new(convert_fvar_cert_to_bvar_ref(set_cert, fvar_id, depth)),
                pred_cert: Box::new(convert_fvar_cert_to_bvar_ref(pred_cert, fvar_id, d1)),
            }
        }
        ZFCSetCertKind::Replacement {
            set_cert,
            func_cert,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ZFCSetCertKind::Replacement {
                set_cert: Box::new(convert_fvar_cert_to_bvar_ref(set_cert, fvar_id, depth)),
                func_cert: Box::new(convert_fvar_cert_to_bvar_ref(func_cert, fvar_id, d1)),
            }
        }
        ZFCSetCertKind::Choice(c) => {
            ZFCSetCertKind::Choice(Box::new(convert_fvar_cert_to_bvar_ref(c, fvar_id, depth)))
        }
    }
}
