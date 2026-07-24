// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fast-path unread-field cleanup for reset/reuse expansion.
//!
//! Lean 4 releases unread object fields before reusing an allocation. We infer
//! the field layout from the current reuse arguments plus local LCNF type
//! bindings so the fast path can emit `proj + _dec` for object-typed fields
//! that were never projected along the current path.

use std::collections::{HashMap, HashSet};

use super::mask::ProjMask;
use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, LetDecl, LetValue, Param};
use crate::rc::pseudo_op;
use crate::to_ir::expr_to_ir_type;
use clean_kernel::{Expr, ExprKind, FVarId, Name};

pub(crate) type TypeMap = HashMap<FVarId, Expr>;

#[derive(Clone, Debug, Default)]
struct FieldLayoutInfo {
    is_object: Option<bool>,
    ty: Option<Expr>,
}

pub(crate) fn build_type_map_for_decl(decl: &Decl) -> TypeMap {
    let mut types = TypeMap::new();
    insert_param_types(&decl.params, &mut types);
    if let DeclValue::Code(code) = &decl.body {
        collect_code_types(code, &mut types);
    }
    types
}

pub(crate) fn build_type_map_for_code(code: &Code) -> TypeMap {
    let mut types = TypeMap::new();
    collect_code_types(code, &mut types);
    types
}

pub(crate) fn prepend_unread_field_cleanup_for_args(
    body: Code,
    obj_fvar: FVarId,
    reuse_args: &[Arg],
    mask: &ProjMask,
    alloc: &mut FVarIdAllocator,
    type_map: &TypeMap,
) -> Code {
    let layout = infer_field_layout(reuse_args, type_map);
    let read_fields: HashSet<u32> = mask.values().copied().collect();
    let type_name = object_type_name(obj_fvar, type_map);
    let mut result = body;

    for (idx, info) in layout.iter().enumerate().rev() {
        if info.is_object != Some(true) || read_fields.contains(&(idx as u32)) {
            continue;
        }

        let proj_fvar = alloc.fresh().expect("FVarId allocation overflow");
        let dec_fvar = alloc.fresh().expect("FVarId allocation overflow");
        let field_ty = info.ty.clone().unwrap_or_else(|| Expr::const_str("_"));

        result = Code::let_bind(
            LetDecl::new(
                proj_fvar,
                pseudo_op::NAME_UNUSED_FIELD.clone(),
                field_ty,
                LetValue::Proj {
                    type_name: type_name.clone(),
                    idx: idx as u32,
                    structure: obj_fvar,
                },
            ),
            Code::let_bind(
                LetDecl::new(
                    dec_fvar,
                    pseudo_op::NAME_DEC.clone(),
                    Expr::const_str("_"),
                    LetValue::Const {
                        name: pseudo_op::NAME_DEC.clone(),
                        levels: vec![],
                        args: vec![Arg::FVar(proj_fvar)],
                    },
                ),
                result,
            ),
        );
    }

    result
}

fn insert_param_types(params: &[Param], types: &mut TypeMap) {
    for param in params {
        types.insert(param.fvar_id, param.ty.clone());
    }
}

fn collect_code_types(code: &Code, types: &mut TypeMap) {
    match code {
        Code::Let(decl, body) => {
            types.insert(decl.fvar_id, decl.ty.clone());
            collect_code_types(body, types);
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            insert_param_types(&fun_decl.params, types);
            collect_code_types(&fun_decl.body, types);
            collect_code_types(body, types);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { params, body, .. } => {
                        insert_param_types(params, types);
                        collect_code_types(body, types);
                    }
                    Alt::Default(body) => collect_code_types(body, types),
                }
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

fn infer_field_layout(args: &[Arg], type_map: &TypeMap) -> Vec<FieldLayoutInfo> {
    args.iter()
        .map(|arg| field_layout_info(arg, type_map))
        .collect()
}

fn field_layout_info(arg: &Arg, type_map: &TypeMap) -> FieldLayoutInfo {
    match arg {
        Arg::FVar(fvar) => {
            let ty = type_map.get(fvar).cloned();
            let is_object = ty
                .as_ref()
                .and_then(|expr| expr_to_ir_type(expr).ok())
                .map(|ir_ty| ir_ty.is_object());
            FieldLayoutInfo { is_object, ty }
        }
        Arg::Erased | Arg::Type(_) | Arg::Index(_) => FieldLayoutInfo {
            is_object: Some(false),
            ty: None,
        },
    }
}

fn object_type_name(obj_fvar: FVarId, type_map: &TypeMap) -> Name {
    type_map
        .get(&obj_fvar)
        .and_then(type_head_name)
        .unwrap_or_else(|| Name::from_string("_"))
}

fn type_head_name(expr: &Expr) -> Option<Name> {
    match expr.strip_mdata().get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}
