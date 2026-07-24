// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Case expression transformation for monomorphization.

use crate::lcnf::{Alt, Cases, Code};
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};

use super::args::param_to_mono;
use super::let_code::code_to_mono_with_depth;
use super::names::has_trivial_structure;
use super::names::special_names;
use super::{impl_name, to_mono_type, ToMonoState};

mod numeric;
mod wrapper;

pub(crate) use numeric::{cases_int_to_mono, cases_nat_to_mono};
pub(crate) use wrapper::{
    cases_array_to_mono, cases_byte_array_to_mono, cases_float_array_to_mono, cases_string_to_mono,
    cases_task_to_mono, cases_thunk_to_mono, cases_uint_to_mono, trivial_struct_to_mono,
};

/// Transform case expression to monomorphic form.
///
/// Dispatches to type-specific handlers for optimized transformations:
/// - Decidable → Bool (same runtime representation, proof params erased)
///
/// Future handlers (documented in designs/2026-02-03-to-mono-pass.md):
/// - Nat/Int elimination (not yet implemented)
/// - Trivial structure elimination (not yet implemented)
///
/// See #1068 for implementation tracking.
pub fn cases_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
) -> Code {
    cases_to_mono_with_depth(cases, state, next_fvar, env, 0)
}

pub(super) fn cases_to_mono_with_depth(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    // Dispatch by type_name for type-specific elimination
    if cases.type_name == special_names::decidable_() {
        return dec_to_mono(cases, state, next_fvar, env, depth);
    }

    if cases.type_name == special_names::nat_() {
        return cases_nat_to_mono(cases, state, next_fvar, env, depth);
    }

    if cases.type_name == special_names::int_() {
        return cases_int_to_mono(cases, state, next_fvar, env, depth);
    }

    // UInt types: single constructor, extract with toBitVec
    if cases.type_name == special_names::uint8_() {
        return cases_uint_to_mono(
            cases,
            state,
            next_fvar,
            env,
            depth,
            special_names::uint8_to_bit_vec(),
        );
    }
    if cases.type_name == special_names::uint16_() {
        return cases_uint_to_mono(
            cases,
            state,
            next_fvar,
            env,
            depth,
            special_names::uint16_to_bit_vec(),
        );
    }
    if cases.type_name == special_names::uint32_() {
        return cases_uint_to_mono(
            cases,
            state,
            next_fvar,
            env,
            depth,
            special_names::uint32_to_bit_vec(),
        );
    }
    if cases.type_name == special_names::uint64_() {
        return cases_uint_to_mono(
            cases,
            state,
            next_fvar,
            env,
            depth,
            special_names::uint64_to_bit_vec(),
        );
    }

    // Array: single constructor, extract with toList
    if cases.type_name == special_names::array_() {
        return cases_array_to_mono(cases, state, next_fvar, env, depth);
    }

    // String: single constructor, extract with toList
    if cases.type_name == special_names::string_() {
        return cases_string_to_mono(cases, state, next_fvar, env, depth);
    }

    // ByteArray: single constructor, extract with data
    if cases.type_name == special_names::byte_array_() {
        return cases_byte_array_to_mono(cases, state, next_fvar, env, depth);
    }

    // FloatArray: single constructor, extract with data
    if cases.type_name == special_names::float_array_() {
        return cases_float_array_to_mono(cases, state, next_fvar, env, depth);
    }

    // Thunk: single constructor, extract with get (lazy eval)
    if cases.type_name == special_names::thunk_() {
        return cases_thunk_to_mono(cases, state, next_fvar, env, depth);
    }

    // Task: single constructor, extract with get (async)
    if cases.type_name == special_names::task_() {
        return cases_task_to_mono(cases, state, next_fvar, env, depth);
    }

    // Trivial structure: single constructor, single relevant field
    if let Some(info) = has_trivial_structure(&cases.type_name, env) {
        return trivial_struct_to_mono(&info, cases, state, next_fvar, env, depth);
    }

    if let Some(code) = computed_field_cases_to_mono(cases, state, next_fvar, env, depth) {
        return code;
    }

    // Fallback: check constructor names for Decidable (legacy detection)
    let is_decidable = cases.alts.iter().any(|alt| {
        if let Alt::Ctor { ctor_name, .. } = alt {
            *ctor_name == special_names::decidable_is_true()
                || *ctor_name == special_names::decidable_is_false()
        } else {
            false
        }
    });

    if is_decidable {
        return dec_to_mono(cases, state, next_fvar, env, depth);
    }

    // Default transformation: recurse into alternatives
    default_cases_to_mono(cases, state, next_fvar, env, depth)
}

fn computed_field_cases_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Option<Code> {
    let impl_type_name = impl_name(&cases.type_name);
    env.get_inductive(&impl_type_name)?;

    let result_type = to_mono_type(&cases.result_type);
    let alts = cases
        .alts
        .iter()
        .map(|alt| computed_field_alt_to_mono(alt, state, next_fvar, env, depth + 1))
        .collect::<Option<Vec<_>>>()?;

    Some(Code::Cases(Cases {
        type_name: impl_type_name,
        result_type,
        scrutinee: cases.scrutinee,
        alts,
    }))
}

fn computed_field_alt_to_mono(
    alt: &Alt,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Option<Alt> {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => {
            let impl_ctor_name = impl_name(ctor_name);
            let impl_ctor = env.get_constructor(&impl_ctor_name)?;
            let num_new_fields = (impl_ctor.num_fields as usize).saturating_sub(params.len());
            let mono_params = mk_field_params_for_computed_fields(
                &impl_ctor.type_,
                impl_ctor.num_params,
                num_new_fields,
                params,
                next_fvar,
            )?;
            let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth);
            Some(Alt::Ctor {
                ctor_name: impl_ctor_name,
                params: mono_params,
                body: Box::new(mono_body),
            })
        }
        Alt::Default(body) => Some(Alt::Default(Box::new(code_to_mono_with_depth(
            body, state, next_fvar, env, depth,
        )))),
    }
}

fn mk_field_params_for_computed_fields(
    ctor_type: &Expr,
    num_params: u32,
    num_new_fields: usize,
    old_fields: &[crate::lcnf::Param],
    next_fvar: &mut u64,
) -> Option<Vec<crate::lcnf::Param>> {
    let mut ty = ctor_type;

    for _ in 0..num_params {
        match ty.kind() {
            ExprKind::Pi(_, _, body) => ty = body.as_ref(),
            _ => return None,
        }
    }

    let mut new_fields = Vec::with_capacity(num_new_fields + old_fields.len());
    for field_idx in 0..num_new_fields {
        let (field_type, body) = match ty.kind() {
            ExprKind::Pi(_, field_type, body) => (field_type, body),
            _ => return None,
        };
        let raw_param = crate::lcnf::Param {
            fvar_id: FVarId::new(*next_fvar),
            name: Name::from_string(&format!("_cf{field_idx}")),
            ty: field_type.as_ref().clone(),
            borrow: false,
        };
        *next_fvar += 1;
        new_fields.push(crate::lcnf::Param {
            ty: to_mono_type(&raw_param.ty),
            ..raw_param
        });
        ty = body.as_ref();
    }

    new_fields.extend(old_fields.iter().cloned());
    Some(new_fields)
}

/// Transform Decidable cases to Bool cases.
///
/// Decidable and Bool have the same runtime representation:
/// - `Decidable.isTrue h` → `Bool.true` (proof param erased)
/// - `Decidable.isFalse h` → `Bool.false` (proof param erased)
pub(crate) fn dec_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    let result_type = to_mono_type(&cases.result_type);

    let alts: Vec<_> = cases
        .alts
        .iter()
        .map(|alt| match alt {
            Alt::Ctor {
                ctor_name,
                params: _, // Proof params are erased
                body,
            } => {
                // Map Decidable constructors to Bool constructors
                let new_ctor_name = if *ctor_name == special_names::decidable_is_true() {
                    special_names::bool_true()
                } else if *ctor_name == special_names::decidable_is_false() {
                    special_names::bool_false()
                } else {
                    // Unexpected constructor in Decidable case - keep it as-is
                    // This shouldn't happen with well-formed LCNF, but defensive
                    return Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: vec![],
                        body: Box::new(code_to_mono_with_depth(
                            body,
                            state,
                            next_fvar,
                            env,
                            depth + 1,
                        )),
                    };
                };

                Alt::Ctor {
                    ctor_name: new_ctor_name,
                    params: vec![], // Bool constructors have no params
                    body: Box::new(code_to_mono_with_depth(
                        body,
                        state,
                        next_fvar,
                        env,
                        depth + 1,
                    )),
                }
            }
            Alt::Default(body) => Alt::Default(Box::new(code_to_mono_with_depth(
                body,
                state,
                next_fvar,
                env,
                depth + 1,
            ))),
        })
        .collect();

    Code::Cases(Cases {
        type_name: special_names::bool_(), // Decidable → Bool
        result_type,
        scrutinee: cases.scrutinee,
        alts,
    })
}

/// Default case transformation: recurse into alternatives.
fn default_cases_to_mono(
    cases: &Cases,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Code {
    let result_type = to_mono_type(&cases.result_type);

    let alts: Vec<_> = cases
        .alts
        .iter()
        .map(|alt| alt_to_mono(alt, state, next_fvar, env, depth + 1))
        .collect();

    Code::Cases(Cases {
        type_name: cases.type_name.clone(),
        result_type,
        scrutinee: cases.scrutinee,
        alts,
    })
}

/// Transform a case alternative to monomorphic form.
fn alt_to_mono(
    alt: &Alt,
    state: &mut ToMonoState,
    next_fvar: &mut u64,
    env: &Environment,
    depth: usize,
) -> Alt {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => {
            let mono_params: Vec<_> = params.iter().map(|p| param_to_mono(p, state)).collect();
            let mono_body = code_to_mono_with_depth(body, state, next_fvar, env, depth);

            Alt::Ctor {
                ctor_name: ctor_name.clone(),
                params: mono_params,
                body: Box::new(mono_body),
            }
        }

        Alt::Default(body) => Alt::Default(Box::new(code_to_mono_with_depth(
            body, state, next_fvar, env, depth,
        ))),
    }
}
