// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{Environment, Expr, FVarId, Name};

use super::default_cases_to_mono;
use crate::to_mono::let_code::code_to_mono_with_depth;
use crate::to_mono::names::special_names;
use crate::to_mono::names::TrivialStructureInfo;
use crate::to_mono::{any_expr, erased_expr, to_mono_type, ToMonoState};

/// Transform UInt cases (single constructor) to let binding.
///
/// UInt types have a single constructor, so pattern match becomes extraction.
pub(crate) fn cases_uint_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
    to_bit_vec_name: Name,
) -> Code {
    // UInt has single constructor with single param
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_bits"));

        // let p := UIntN.toBitVec scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: to_bit_vec_name,
                levels: vec![],
                args: vec![Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    // Fallback to default
    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform Array cases (single constructor) to let binding.
///
/// Array has single constructor, extract with toList.
pub(crate) fn cases_array_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_list"));

        // let p := Array.toList ◇ scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::array_to_list(),
                levels: vec![],
                args: vec![Arg::Erased, Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform String cases (single constructor) to let binding.
///
/// String has single constructor, extract with toList.
pub(crate) fn cases_string_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_chars"));

        // let p := String.toList scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::string_to_list(),
                levels: vec![],
                args: vec![Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform ByteArray cases (single constructor) to let binding.
///
/// ByteArray has single constructor, extract with data accessor.
pub(crate) fn cases_byte_array_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_data"));

        // let p := ByteArray.data scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::byte_array_data(),
                levels: vec![],
                args: vec![Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform FloatArray cases (single constructor) to let binding.
///
/// FloatArray has single constructor, extract with data accessor.
pub(crate) fn cases_float_array_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_data"));

        // let p := FloatArray.data scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::float_array_data(),
                levels: vec![],
                args: vec![Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform Thunk cases (single constructor) to fun decl.
///
/// Thunk has single constructor. The extracted value needs to be wrapped in a
/// function taking PUnit and calling Thunk.get, matching Lean4's behavior.
pub(crate) fn cases_thunk_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_thunk_val"));

        // Create a let for the Thunk.get call result
        let get_fvar = FVarId::new(*next_fvar);
        *next_fvar += 1;
        let get_decl = LetDecl {
            fvar_id: get_fvar,
            name: Name::from_string("_x"),
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::thunk_get(),
                levels: vec![],
                args: vec![Arg::Erased, Arg::FVar(cases.scrutinee)],
            },
        };

        // Create aux param for PUnit
        let punit_param_fvar = FVarId::new(*next_fvar);
        *next_fvar += 1;
        let punit_param = Param {
            fvar_id: punit_param_fvar,
            name: Name::from_string("_u"),
            ty: Expr::const_(Name::from_string("PUnit"), vec![]),
            borrow: false,
        };

        // Build the fun decl: fun (_u : PUnit) => let _x := Thunk.get ◇ scrutinee; return _x
        let fun_body = Code::Let(get_decl, Box::new(Code::Return(get_fvar)));
        // Function type is PUnit → lcAny (matches Lean 4's mkArrow paramType anyExpr)
        let punit_ty = Expr::const_(Name::from_string("PUnit"), vec![]);
        let fun_ty = Expr::arrow(punit_ty, any_expr());
        let fun_decl = FunDecl {
            fvar_id: p_fvar,
            name: p_name,
            params: vec![punit_param],
            ty: fun_ty,
            body: Box::new(fun_body),
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Fun(fun_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform Task cases (single constructor) to let binding.
///
/// Task has single constructor, extract with get.
pub(crate) fn cases_task_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    if let Some(Alt::Ctor { params, body, .. }) = cases.alts.first() {
        let p = params.first();
        let p_fvar = p.map(|p| p.fvar_id).unwrap_or_else(|| {
            let fvar = FVarId::new(*next_fvar);
            *next_fvar += 1;
            fvar
        });
        let p_name = p
            .map(|p| p.name.clone())
            .unwrap_or_else(|| Name::from_string("_task_val"));

        // let p := Task.get ◇ scrutinee
        let extract_decl = LetDecl {
            fvar_id: p_fvar,
            name: p_name,
            ty: any_expr(), // LCNF mono placeholder for unknown types
            value: LetValue::Const {
                name: special_names::task_get(),
                levels: vec![],
                args: vec![Arg::Erased, Arg::FVar(cases.scrutinee)],
            },
        };

        let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        return Code::Let(extract_decl, Box::new(mono_body));
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

/// Transform trivial structure cases to simple let binding.
///
/// A trivial structure has a single constructor with a single computationally
/// relevant field. Pattern matching can be eliminated by directly assigning
/// the scrutinee to the field binding.
///
/// Example:
/// ```text
/// cases x of | TrivialStruct.mk val => body
/// ```
/// Becomes:
/// ```text
/// let val := x; body
/// ```
pub fn trivial_struct_to_mono(
    info: &TrivialStructureInfo,
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    // Trivial structures have exactly one alternative (single constructor)
    if let Some(Alt::Ctor {
        ctor_name,
        params,
        body,
    }) = cases.alts.first()
    {
        // Validate this matches our expected constructor
        if *ctor_name != info.ctor_name {
            return default_cases_to_mono(cases, state, next_fvar, env, depth);
        }

        // `to_lcnf`'s generic `casesOn` lowering emits alts with EMPTY
        // params — the fields are read via `Proj` bindings inside the body.
        // There is no tag to dispatch on (single constructor, and the
        // scrutinee IS the bare field at runtime), so the cases collapses to
        // the body; the body's `Proj`s are rewritten by `letvalue_to_mono`'s
        // trivial-projection arm (identity on the relevant field, erased on
        // proof/type fields). Before this, `Fin.val` kept a real tag switch
        // plus `clean_ctor_get` over what the C5b scalar-carrier world flows
        // as a bare `Nat` (R3).
        if params.is_empty() {
            return code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
        }

        // The relevant field is at info.field_idx
        if info.field_idx < params.len() {
            let p = &params[info.field_idx];

            // Create a let binding: let p := scrutinee
            // The scrutinee has the same runtime representation as the field
            let extract_decl = LetDecl {
                fvar_id: p.fvar_id,
                name: p.name.clone(),
                ty: to_mono_type(&p.ty),
                value: LetValue::FVar {
                    fvar: cases.scrutinee,
                    args: vec![],
                },
            };

            let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth + 1);
            let mut result = Code::Let(extract_decl, Box::new(mono_body));

            // Bind irrelevant params to erased values so their fvar_ids are
            // defined if the body still references them. Earlier LCNF passes
            // should erase these references, but this provides safety in case
            // erasure is incomplete.
            for (i, param) in params.iter().enumerate().rev() {
                if i != info.field_idx {
                    let erased_decl = LetDecl {
                        fvar_id: param.fvar_id,
                        name: param.name.clone(),
                        ty: erased_expr(),
                        value: LetValue::Erased,
                    };
                    result = Code::Let(erased_decl, Box::new(result));
                }
            }

            return result;
        }
    }

    default_cases_to_mono(cases, state, next_fvar, env, depth)
}
