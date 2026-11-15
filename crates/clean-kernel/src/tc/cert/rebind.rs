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
use crate::expr::{stack_safe, Expr, FVarAbstraction, FVarId};
use crate::tc::local_context::checked_add_u32;
use std::collections::HashMap;
use std::sync::Arc;

#[path = "rebind_support.rs"]
mod support;
use support::SupportContext;
#[path = "rebind_closed_memo.rs"]
mod closed_memo;
pub(in crate::tc) use closed_memo::RebindClosedMemo;

/// Convert FVar certificates back to BVar certificates.
/// Stack-safe wrapper for deeply nested proof certificates.
pub(crate) fn convert_fvar_cert_to_bvar(cert: ProofCert, fvar_id: FVarId, depth: u32) -> ProofCert {
    let mut context = RebindContext::new(fvar_id);
    if context.support.cert(&cert).unchanged_at(depth) {
        drop(context);
        cert
    } else {
        context.convert_ref(&cert, depth)
    }
}

pub(super) fn convert_with_closed_memo(
    cert: ProofCert,
    fvar_id: FVarId,
    depth: u32,
    memo: &mut RebindClosedMemo,
    cap: usize,
) -> ProofCert {
    let mut context = RebindContext {
        fvar_id,
        memo: HashMap::new(),
        support: SupportContext::with_closed_memo(fvar_id, Some((memo, cap))),
        expressions: FVarAbstraction::new(fvar_id),
    };
    if context.support.cert(&cert).unchanged_at(depth) {
        drop(context);
        cert
    } else {
        context.convert_ref(&cert, depth)
    }
}

/// One abstraction, with a fixed FVar and memoized Arc edges.
///
/// SOUNDNESS: rebinding is a pure function of the certificate, FVar and binder
/// depth. The FVar is fixed for this call; depth is part of every key because
/// both FVar replacement and pre-existing BVar shifts depend on it. Borrowed
/// input Arcs keep the keyed allocations alive for the entire memo lifetime.
/// Only actual Arc child edges are cached, never a temporary/root value's
/// address. Hits share the converted Arc, not a freshly rebuilt subtree.
///
/// This preserves the existing traversal's fields and checked index arithmetic;
/// it is not a typing cache or an acceptance shortcut. In particular, absence
/// of the target FVar does not imply unchanged BVars or certificate type fields.
struct RebindContext<'a, 'memo> {
    fvar_id: FVarId,
    memo: HashMap<(*const ProofCert, u32), (&'a Arc<ProofCert>, Arc<ProofCert>)>,
    support: SupportContext<'a, 'memo>,
    expressions: FVarAbstraction<'a>,
}

impl<'a, 'memo> RebindContext<'a, 'memo> {
    fn new(fvar_id: FVarId) -> Self {
        Self {
            fvar_id,
            memo: HashMap::new(),
            support: SupportContext::new(fvar_id),
            expressions: FVarAbstraction::new(fvar_id),
        }
    }

    fn convert_ref(&mut self, cert: &'a ProofCert, depth: u32) -> ProofCert {
        stack_safe(|| convert_fvar_cert_to_bvar_impl(cert, self, depth))
    }

    fn abstract_expr(&mut self, expr: &'a Expr, depth: u32) -> Expr {
        self.expressions.at(expr, depth)
    }

    fn convert_arc(&mut self, cert: &'a Arc<ProofCert>, depth: u32) -> Arc<ProofCert> {
        // Reusing an unaffected node also preserves sharing across DIFFERENT
        // binder depths and successive abstractions. The summary accounts for
        // certificate BVars, every transformed type field and checked depth.
        if self.support.arc(cert).unchanged_at(depth) {
            return Arc::clone(cert);
        }
        let key = (Arc::as_ptr(cert), depth);
        if let Some((_, converted)) = self.memo.get(&key) {
            return Arc::clone(converted);
        }
        let converted = Arc::new(self.convert_ref(cert.as_ref(), depth));
        self.memo.insert(key, (cert, Arc::clone(&converted)));
        converted
    }
}

fn convert_fvar_cert_to_bvar_impl<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    // One unit per certificate node rebuilt (`crate::work_meter`); the
    // expression fields it abstracts pay for their own nodes.
    crate::work_meter::charge(crate::work_meter::Walk::Fold, 1);
    match cert {
        // Leaf cases: no recursive cert conversion, only abstract types
        ProofCert::FVar { .. }
        | ProofCert::Sort { .. }
        | ProofCert::BVar { .. }
        | ProofCert::Const { .. }
        | ProofCert::Lit { .. } => rebind_leaf(cert, context, depth),
        // Core CIC binder forms (depth-incrementing)
        ProofCert::Lam { .. } | ProofCert::Pi { .. } | ProofCert::Let { .. } => {
            rebind_binder(cert, context, depth)
        }
        // Core CIC compound forms
        ProofCert::App { .. }
        | ProofCert::DefEq { .. }
        | ProofCert::MData { .. }
        | ProofCert::Proj { .. } => rebind_compound(cert, context, depth),
        // Cubical mode extensions
        ProofCert::CubicalInterval
        | ProofCert::CubicalEndpoint { .. }
        | ProofCert::CubicalPath { .. }
        | ProofCert::CubicalPathLam { .. }
        | ProofCert::CubicalPathApp { .. }
        | ProofCert::CubicalHComp { .. }
        | ProofCert::CubicalTransp { .. }
        | ProofCert::CubicalCoe { .. } => rebind_cubical(cert, context, depth),
        // ZFC and Impredicative mode extensions
        _ => rebind_zfc_impredicative(cert, context, depth),
    }
}

/// Leaf cert cases: FVar, Sort, BVar, Const, Lit — abstract types only.
fn rebind_leaf<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    let fvar_id = context.fvar_id;
    match cert {
        ProofCert::FVar { id, type_ } if *id == fvar_id => ProofCert::BVar {
            idx: depth,
            expected_type: Box::new(context.abstract_expr(type_, depth)),
        },
        ProofCert::FVar { id, type_ } => ProofCert::FVar {
            id: *id,
            type_: Box::new(context.abstract_expr(type_, depth)),
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
            expected_type: Box::new(context.abstract_expr(expected_type, depth)),
        },
        ProofCert::Const {
            name,
            levels,
            type_,
        } => ProofCert::Const {
            name: name.clone(),
            levels: levels.clone(),
            type_: Box::new(context.abstract_expr(type_, depth)),
        },
        ProofCert::Lit { lit, type_ } => ProofCert::Lit {
            lit: lit.clone(),
            type_: Box::new(context.abstract_expr(type_, depth)),
        },
        _ => unreachable!("rebind_leaf called with non-leaf cert"),
    }
}

/// Binder cert cases: Lam, Pi, Let — depth-incrementing body recursion.
fn rebind_binder<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
    match cert {
        ProofCert::Lam {
            binder_info,
            arg_type_cert,
            body_cert,
            result_type,
        } => ProofCert::Lam {
            binder_info: *binder_info,
            arg_type_cert: context.convert_arc(arg_type_cert, depth),
            body_cert: context.convert_arc(body_cert, d1),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::Pi {
            binder_info,
            arg_type_cert,
            arg_level,
            body_type_cert,
            body_level,
        } => ProofCert::Pi {
            binder_info: *binder_info,
            arg_type_cert: context.convert_arc(arg_type_cert, depth),
            arg_level: arg_level.clone(),
            body_type_cert: context.convert_arc(body_type_cert, d1),
            body_level: body_level.clone(),
        },
        ProofCert::Let {
            type_cert,
            value_cert,
            body_cert,
            result_type,
        } => ProofCert::Let {
            type_cert: context.convert_arc(type_cert, depth),
            value_cert: context.convert_arc(value_cert, depth),
            body_cert: context.convert_arc(body_cert, d1),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        _ => unreachable!("rebind_binder called with non-binder cert"),
    }
}

/// Compound cert cases: App, DefEq, MData, Proj — recursive on subcerts and types.
fn rebind_compound<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    match cert {
        ProofCert::App {
            fn_cert,
            fn_type,
            arg_cert,
            result_type,
        } => ProofCert::App {
            fn_cert: context.convert_arc(fn_cert, depth),
            fn_type: Box::new(context.abstract_expr(fn_type, depth)),
            arg_cert: context.convert_arc(arg_cert, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::DefEq {
            inner,
            expected_type,
            actual_type,
            eq_steps,
        } => ProofCert::DefEq {
            inner: context.convert_arc(inner, depth),
            expected_type: Box::new(context.abstract_expr(expected_type, depth)),
            actual_type: Box::new(context.abstract_expr(actual_type, depth)),
            eq_steps: eq_steps.clone(),
        },
        ProofCert::MData {
            metadata,
            inner_cert,
            result_type,
        } => ProofCert::MData {
            metadata: metadata.clone(),
            inner_cert: context.convert_arc(inner_cert, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
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
            expr_cert: context.convert_arc(expr_cert, depth),
            expr_type: Box::new(context.abstract_expr(expr_type, depth)),
            field_type: Box::new(context.abstract_expr(field_type, depth)),
        },
        _ => unreachable!("rebind_compound called with non-compound cert"),
    }
}

/// Mode-specific cert cases: Cubical extensions.
fn rebind_cubical<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    match cert {
        ProofCert::CubicalInterval => ProofCert::CubicalInterval,
        ProofCert::CubicalEndpoint { is_one } => ProofCert::CubicalEndpoint { is_one: *is_one },
        ProofCert::CubicalPath {
            ty_cert,
            ty_level,
            left_cert,
            right_cert,
        } => ProofCert::CubicalPath {
            ty_cert: context.convert_arc(ty_cert, depth),
            ty_level: ty_level.clone(),
            left_cert: context.convert_arc(left_cert, depth),
            right_cert: context.convert_arc(right_cert, depth),
        },
        ProofCert::CubicalPathLam {
            body_cert,
            body_type,
            result_type,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ProofCert::CubicalPathLam {
                body_cert: context.convert_arc(body_cert, d1),
                body_type: Box::new(context.abstract_expr(body_type, depth)),
                result_type: Box::new(context.abstract_expr(result_type, depth)),
            }
        }
        ProofCert::CubicalPathApp {
            path_cert,
            arg_cert,
            path_type,
            result_type,
        } => ProofCert::CubicalPathApp {
            path_cert: context.convert_arc(path_cert, depth),
            arg_cert: context.convert_arc(arg_cert, depth),
            path_type: Box::new(context.abstract_expr(path_type, depth)),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::CubicalHComp {
            ty_cert,
            phi_cert,
            u_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalHComp {
            ty_cert: context.convert_arc(ty_cert, depth),
            phi_cert: context.convert_arc(phi_cert, depth),
            u_cert: context.convert_arc(u_cert, depth),
            base_cert: context.convert_arc(base_cert, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::CubicalTransp {
            ty_cert,
            phi_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalTransp {
            ty_cert: context.convert_arc(ty_cert, depth),
            phi_cert: context.convert_arc(phi_cert, depth),
            base_cert: context.convert_arc(base_cert, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::CubicalCoe {
            ty_cert,
            r_cert,
            s_cert,
            base_cert,
            result_type,
        } => ProofCert::CubicalCoe {
            ty_cert: context.convert_arc(ty_cert, depth),
            r_cert: context.convert_arc(r_cert, depth),
            s_cert: context.convert_arc(s_cert, depth),
            base_cert: context.convert_arc(base_cert, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        _ => unreachable!("rebind_cubical called with non-Cubical cert"),
    }
}

/// Mode-specific cert cases: ZFC and Impredicative extensions.
fn rebind_zfc_impredicative<'a>(
    cert: &'a ProofCert,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> ProofCert {
    match cert {
        ProofCert::ZFCSet { kind, result_type } => ProofCert::ZFCSet {
            kind: convert_fvar_in_zfc_set_kind(kind, context, depth),
            result_type: Box::new(context.abstract_expr(result_type, depth)),
        },
        ProofCert::ZFCMem {
            elem_cert,
            set_cert,
        } => ProofCert::ZFCMem {
            elem_cert: context.convert_arc(elem_cert, depth),
            set_cert: context.convert_arc(set_cert, depth),
        },
        ProofCert::ZFCComprehension {
            var_ty_cert,
            pred_cert,
            result_type,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ProofCert::ZFCComprehension {
                var_ty_cert: context.convert_arc(var_ty_cert, depth),
                pred_cert: context.convert_arc(pred_cert, d1),
                result_type: Box::new(context.abstract_expr(result_type, depth)),
            }
        }
        ProofCert::SProp => ProofCert::SProp,
        ProofCert::Squash { inner_cert } => ProofCert::Squash {
            inner_cert: context.convert_arc(inner_cert, depth),
        },
        _ => unreachable!("rebind_zfc_impredicative called with non-ZFC/Impredicative cert"),
    }
}

/// Helper to convert FVar occurrences in ZFC set certificate kind
fn convert_fvar_in_zfc_set_kind<'a>(
    kind: &'a crate::cert::ZFCSetCertKind,
    context: &mut RebindContext<'a, '_>,
    depth: u32,
) -> crate::cert::ZFCSetCertKind {
    use crate::cert::ZFCSetCertKind;
    match kind {
        ZFCSetCertKind::Empty => ZFCSetCertKind::Empty,
        ZFCSetCertKind::Infinity => ZFCSetCertKind::Infinity,
        ZFCSetCertKind::Singleton(c) => ZFCSetCertKind::Singleton(context.convert_arc(c, depth)),
        ZFCSetCertKind::Pair(c1, c2) => ZFCSetCertKind::Pair(
            context.convert_arc(c1, depth),
            context.convert_arc(c2, depth),
        ),
        ZFCSetCertKind::Union(c) => ZFCSetCertKind::Union(context.convert_arc(c, depth)),
        ZFCSetCertKind::PowerSet(c) => ZFCSetCertKind::PowerSet(context.convert_arc(c, depth)),
        ZFCSetCertKind::Separation {
            set_cert,
            pred_cert,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ZFCSetCertKind::Separation {
                set_cert: context.convert_arc(set_cert, depth),
                pred_cert: context.convert_arc(pred_cert, d1),
            }
        }
        ZFCSetCertKind::Replacement {
            set_cert,
            func_cert,
        } => {
            let d1 = checked_add_u32(depth, 1, "abstract_fvar depth");
            ZFCSetCertKind::Replacement {
                set_cert: context.convert_arc(set_cert, depth),
                func_cert: context.convert_arc(func_cert, d1),
            }
        }
        ZFCSetCertKind::Choice(c) => ZFCSetCertKind::Choice(context.convert_arc(c, depth)),
    }
}

#[cfg(test)]
#[path = "rebind_dag_tests.rs"]
mod dag_tests;

// The inference/replay half of the same suite, split out 2026-09-16 when
// `rebind_dag_tests.rs` crossed 1000 lines. It reaches `core_allocations`
// through `dag_tests` rather than redefining it.
#[cfg(test)]
#[path = "rebind_dag_infer_tests.rs"]
mod dag_infer_tests;

#[cfg(test)]
#[path = "rebind_expression_memo_tests.rs"]
mod expression_memo_tests;
