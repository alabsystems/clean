// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewrite operations for reset/reuse expansion.
//!
//! Contains the reuse site discovery and the fast/slow path rewriting
//! that transforms reuse operations into either set operations (fast path)
//! or constructor calls (slow path).

use super::cleanup::{build_type_map_for_code, prepend_unread_field_cleanup_for_args, TypeMap};
use super::is_reuse_op;
use super::mask::{is_dec_of, is_inc_of_masked, mask_for_target, ProjMask, ProjSources};
use super::slow_path::rewrite_reuse_to_ctor;
use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use crate::rc::pseudo_op;
use clean_kernel::{FVarId, Name};

/// Information about a reuse site (used for test verification of site discovery).
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct ReuseSite {
    /// The fvar that receives the reused value.
    pub(crate) result_fvar: FVarId,
    /// The constructor name.
    pub(crate) ctor_name: Name,
    /// Constructor arguments (excluding reset_var).
    pub(crate) args: Vec<Arg>,
}

/// Find all reuse sites that use the given reset variable.
#[cfg(test)]
pub(crate) fn find_reuse_sites(code: &Code, reset_var: FVarId) -> Vec<ReuseSite> {
    let mut sites = Vec::new();
    find_reuse_sites_impl(code, reset_var, &mut sites);
    sites
}

#[cfg(test)]
fn find_reuse_sites_impl(code: &Code, reset_var: FVarId, sites: &mut Vec<ReuseSite>) {
    match code {
        Code::Let(decl, body) => {
            if is_reuse_op(&decl.value) {
                // Handle legacy LetValue::Const { name: "_reuse", .. }
                if let LetValue::Const { args, .. } = &decl.value {
                    // Check if first arg is the reset_var
                    if let Some(Arg::FVar(fvar)) = args.first() {
                        if *fvar == reset_var {
                            // Convention: reuse w ctor_name arg1 arg2 ...
                            let remaining_args: Vec<Arg> = args.iter().skip(1).cloned().collect();
                            sites.push(ReuseSite {
                                result_fvar: decl.fvar_id,
                                ctor_name: pseudo_op::NAME_CTOR.clone(),
                                args: remaining_args,
                            });
                        }
                    }
                }
                // Handle native LetValue::Reuse { slot, ctor_name, args, .. }
                if let LetValue::Reuse {
                    slot,
                    ctor_name,
                    args,
                    ..
                } = &decl.value
                {
                    if *slot == reset_var {
                        sites.push(ReuseSite {
                            result_fvar: decl.fvar_id,
                            ctor_name: ctor_name.clone(),
                            args: args.clone(),
                        });
                    }
                }
            }
            find_reuse_sites_impl(body, reset_var, sites);
        }

        Code::Fun(fun_decl, body) => {
            find_reuse_sites_impl(&fun_decl.body, reset_var, sites);
            find_reuse_sites_impl(body, reset_var, sites);
        }

        Code::JoinPoint(jp_decl, body) => {
            find_reuse_sites_impl(&jp_decl.body, reset_var, sites);
            find_reuse_sites_impl(body, reset_var, sites);
        }

        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => find_reuse_sites_impl(body, reset_var, sites),
                    Alt::Default(body) => find_reuse_sites_impl(body, reset_var, sites),
                }
            }
        }

        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

pub(crate) fn make_fast_path_with_types(
    reset_var: FVarId,
    obj_fvar: FVarId,
    body: &Code,
    alloc: &mut FVarIdAllocator,
    type_map: &TypeMap,
    proj_sources: &ProjSources,
) -> Code {
    // In fast path, reset_var = obj_fvar (reuse the memory)
    // Reuse operations become Set operations

    // Seed the fast path with projections computed before the reset; projections
    // introduced after the reset are tracked path-locally during rewriting.
    let mask = mask_for_target(proj_sources, obj_fvar);
    let mut combined_type_map = type_map.clone();
    combined_type_map.extend(build_type_map_for_code(body));

    let inner = rewrite_reuse_to_set(body, reset_var, obj_fvar, alloc, &mask, &combined_type_map);
    Code::let_bind(
        LetDecl::new(
            reset_var,
            Name::from_string(pseudo_op::REUSE_SLOT),
            clean_kernel::Expr::const_str("_"),
            LetValue::FVar {
                fvar: obj_fvar,
                args: vec![],
            },
        ),
        inner,
    )
}

/// Generate the slow path: allocate new, dec old.
pub(crate) fn make_slow_path(obj_fvar: FVarId, body: &Code, alloc: &mut FVarIdAllocator) -> Code {
    // In slow path:
    // 1. Dec the original object
    // 2. Reuse operations become regular constructor calls

    let inner = rewrite_reuse_to_ctor(body);

    // Prepend dec for the original object
    Code::let_bind(
        LetDecl::new(
            alloc.fresh().expect("FVarId allocation overflow"),
            pseudo_op::NAME_DEC.clone(),
            clean_kernel::Expr::const_str("_"),
            LetValue::Const {
                name: pseudo_op::NAME_DEC.clone(),
                levels: vec![],
                args: vec![Arg::FVar(obj_fvar)],
            },
        ),
        inner,
    )
}

/// Rewrite reuse operations to set operations on the fast path.
///
/// `mask` tracks the projections currently known to come from the reused
/// object so we can erase redundant `_inc`, skip self-sets, and release only
/// unread object fields for the current reuse site.
fn rewrite_reuse_to_set(
    code: &Code,
    reset_var: FVarId,
    obj_fvar: FVarId,
    alloc: &mut FVarIdAllocator,
    mask: &ProjMask,
    type_map: &TypeMap,
) -> Code {
    match code {
        Code::Let(decl, body) => {
            if is_reuse_op(&decl.value) {
                // Extract slot, args, and ctor_name from either legacy or native reuse.
                // ctor_name is used for setTag on cross-constructor reuse (Bug 18 / #2059).
                let reuse_info: Option<(FVarId, Vec<Arg>, Option<Name>)> = match &decl.value {
                    LetValue::Const { args, .. } => {
                        if let Some(Arg::FVar(fvar)) = args.first() {
                            Some((*fvar, args.iter().skip(1).cloned().collect(), None))
                        } else {
                            None
                        }
                    }
                    LetValue::Reuse {
                        slot,
                        ctor_name,
                        args,
                        ..
                    } => Some((*slot, args.clone(), Some(ctor_name.clone()))),
                    _ => None,
                };

                if let Some((slot, remaining_args, ctor_name)) = reuse_info {
                    if slot == reset_var {
                        // Replace reuse with set operations
                        let new_body =
                            rewrite_reuse_to_set(body, reset_var, obj_fvar, alloc, mask, type_map);
                        let mut result = new_body;

                        for (idx, arg) in remaining_args.iter().enumerate().rev() {
                            // Only FVar args need set operations - Erased/Type args
                            // are computationally irrelevant and don't occupy memory slots
                            if let Arg::FVar(arg_fvar) = arg {
                                // Lean 4 partitionSelfSets: writing a projected value back
                                // to the same slot is a no-op on the fast path.
                                if mask.get(arg_fvar) == Some(&(idx as u32)) {
                                    continue;
                                }

                                result = Code::let_bind(
                                    LetDecl::new(
                                        alloc.fresh().expect("FVarId allocation overflow"),
                                        pseudo_op::NAME_SET.clone(),
                                        clean_kernel::Expr::const_str("_"),
                                        LetValue::Const {
                                            name: pseudo_op::NAME_SET.clone(),
                                            levels: vec![],
                                            args: vec![
                                                Arg::FVar(obj_fvar),
                                                Arg::Index(idx as u32),
                                                Arg::FVar(*arg_fvar),
                                            ],
                                        },
                                    ),
                                    result,
                                );
                            }
                        }

                        // Lean 4 emits `setTag` for cross-constructor reuse; same-tag
                        // updates are a runtime no-op.
                        if let Some(ref ctor) = ctor_name {
                            result = Code::let_bind(
                                LetDecl::new(
                                    alloc.fresh().expect("FVarId allocation overflow"),
                                    pseudo_op::NAME_SET_TAG.clone(),
                                    clean_kernel::Expr::const_str("_"),
                                    LetValue::Const {
                                        name: pseudo_op::NAME_SET_TAG.clone(),
                                        levels: vec![],
                                        args: vec![
                                            Arg::FVar(obj_fvar),
                                            Arg::Type(clean_kernel::Expr::const_str(
                                                &ctor.to_string(),
                                            )),
                                        ],
                                    },
                                ),
                                result,
                            );
                        }

                        let result = Code::let_bind(
                            LetDecl::new(
                                decl.fvar_id,
                                decl.name.clone(),
                                decl.ty.clone(),
                                LetValue::FVar {
                                    fvar: obj_fvar,
                                    args: vec![],
                                },
                            ),
                            result,
                        );

                        return prepend_unread_field_cleanup_for_args(
                            result,
                            obj_fvar,
                            &remaining_args,
                            mask,
                            alloc,
                            type_map,
                        );
                    }
                }
            }

            // Lean 4 turns `dec token` into `del token` on the fast path because
            // refcount is known to be 1.
            if is_dec_of(&decl.value, reset_var) {
                let new_body =
                    rewrite_reuse_to_set(body, reset_var, obj_fvar, alloc, mask, type_map);
                return Code::let_bind(
                    LetDecl::new(
                        decl.fvar_id,
                        pseudo_op::NAME_DEL.clone(),
                        decl.ty.clone(),
                        LetValue::Const {
                            name: pseudo_op::NAME_DEL.clone(),
                            levels: vec![],
                            args: vec![Arg::FVar(reset_var)],
                        },
                    ),
                    new_body,
                );
            }

            // Lean 4 eraseProjIncFor: projected values stay alive through the
            // reused object, so the fast path can erase their `_inc`.
            if is_inc_of_masked(&decl.value, mask) {
                return rewrite_reuse_to_set(body, reset_var, obj_fvar, alloc, mask, type_map);
            }

            let mut next_mask = mask.clone();
            if let LetValue::Proj { structure, idx, .. } = &decl.value {
                if *structure == obj_fvar {
                    next_mask.insert(decl.fvar_id, *idx);
                }
            }

            Code::Let(
                decl.clone(),
                Box::new(rewrite_reuse_to_set(
                    body, reset_var, obj_fvar, alloc, &next_mask, type_map,
                )),
            )
        }

        Code::Fun(fun_decl, body) => {
            let new_fun_body =
                rewrite_reuse_to_set(&fun_decl.body, reset_var, obj_fvar, alloc, mask, type_map);
            Code::Fun(
                FunDecl {
                    body: Box::new(new_fun_body),
                    ..fun_decl.clone()
                },
                Box::new(rewrite_reuse_to_set(
                    body, reset_var, obj_fvar, alloc, mask, type_map,
                )),
            )
        }

        Code::JoinPoint(jp_decl, body) => {
            let new_jp_body =
                rewrite_reuse_to_set(&jp_decl.body, reset_var, obj_fvar, alloc, mask, type_map);
            Code::JoinPoint(
                FunDecl {
                    body: Box::new(new_jp_body),
                    ..jp_decl.clone()
                },
                Box::new(rewrite_reuse_to_set(
                    body, reset_var, obj_fvar, alloc, mask, type_map,
                )),
            )
        }

        Code::Cases(cases) => {
            let mut new_alts = Vec::with_capacity(cases.alts.len());
            for alt in &cases.alts {
                let new_alt = match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: params.clone(),
                        body: Box::new(rewrite_reuse_to_set(
                            body, reset_var, obj_fvar, alloc, mask, type_map,
                        )),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(rewrite_reuse_to_set(
                        body, reset_var, obj_fvar, alloc, mask, type_map,
                    ))),
                };
                new_alts.push(new_alt);
            }

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }

        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}
