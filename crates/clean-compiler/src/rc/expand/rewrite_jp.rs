// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Join-point-based rewrite for reset/reuse expansion (Bug 15 / #2059).
//!
//! Within a `resetjp` body, transforms:
//! - `dec token` → `del token`
//! - `reuse token ctor args; k` → `reusejp(final)` join point with fast/slow dispatch
//!
//! Reference: Lean 4 LCNF ExpandResetReuse.lean:187-353

use super::cleanup::{prepend_unread_field_cleanup_for_args, TypeMap};
use super::is_reuse_op;
use super::mask::{is_dec_of, ProjMask};
use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue, Param};
use crate::rc::pseudo_op;
use clean_kernel::{Expr, FVarId, Name};

/// Shared context for processing reset continuation bodies.
pub(crate) struct ResetContContext<'a> {
    pub(crate) reset_var: FVarId,
    pub(crate) is_shared: FVarId,
    pub(crate) alloc: &'a mut FVarIdAllocator,
    pub(crate) type_map: &'a TypeMap,
    pub(crate) mask: &'a ProjMask,
}

fn is_inc_of_masked(value: &LetValue, mask: &ProjMask) -> bool {
    match value {
        LetValue::Const { name, args, .. } => {
            name.to_string() == pseudo_op::INC
                && matches!(args.first(), Some(Arg::FVar(fvar)) if mask.contains_key(fvar))
        }
        _ => false,
    }
}

/// Extract reuse info: `(slot, remaining_args, ctor_name)`.
fn extract_reuse_info(value: &LetValue) -> Option<(FVarId, Vec<Arg>, Option<Name>)> {
    match value {
        LetValue::Const { name, args, .. } if name.to_string() == pseudo_op::REUSE => {
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
    }
}

/// Process the body after a reset, transforming dec/reuse sites into JP patterns.
///
/// Within the `resetjp` body:
/// - `dec token` becomes `del token` (refcount known to be 1 on fast path;
///   on slow path, token is erased so del is a no-op)
/// - `reuse token ctor args; k` becomes a `reusejp(final)` join point
///   with fast/slow dispatch on `is_shared`
///
/// Reference: Lean 4 LCNF ExpandResetReuse.lean:187-236 (processResetCont)
pub(crate) fn process_reset_cont(code: &Code, ctx: &mut ResetContContext) -> Code {
    match code {
        Code::Let(decl, body) => {
            // Convert dec of reset_var to del (Bug 19 parity within JP body)
            if is_dec_of(&decl.value, ctx.reset_var) {
                let processed = process_reset_cont(body, ctx);
                return Code::let_bind(
                    LetDecl::new(
                        decl.fvar_id,
                        pseudo_op::NAME_DEL.clone(),
                        decl.ty.clone(),
                        LetValue::Const {
                            name: pseudo_op::NAME_DEL.clone(),
                            levels: vec![],
                            args: vec![Arg::FVar(ctx.reset_var)],
                        },
                    ),
                    processed,
                );
            }

            // Bug 16 parity: projected fields already stay alive on the fast path
            // through the reused object. The slow path prefixes the required `_inc`
            // before decrementing the original object, so the shared JP body must
            // erase these masked projection increments.
            if is_inc_of_masked(&decl.value, ctx.mask) {
                return process_reset_cont(body, ctx);
            }

            // Handle reuse of reset_var → expand into reusejp
            if is_reuse_op(&decl.value) {
                if let Some((slot, remaining_args, ctor_name)) = extract_reuse_info(&decl.value) {
                    if slot == ctx.reset_var {
                        return expand_reuse_as_jp(decl, body, &remaining_args, ctor_name, ctx);
                    }
                }
            }

            // Other lets: recurse into body
            Code::Let(decl.clone(), Box::new(process_reset_cont(body, ctx)))
        }

        Code::Fun(fun_decl, body) => {
            let new_fun_body = process_reset_cont(&fun_decl.body, ctx);
            Code::Fun(
                FunDecl {
                    body: Box::new(new_fun_body),
                    ..fun_decl.clone()
                },
                Box::new(process_reset_cont(body, ctx)),
            )
        }

        Code::JoinPoint(jp_decl, body) => {
            let new_jp_body = process_reset_cont(&jp_decl.body, ctx);
            Code::JoinPoint(
                FunDecl {
                    body: Box::new(new_jp_body),
                    ..jp_decl.clone()
                },
                Box::new(process_reset_cont(body, ctx)),
            )
        }

        Code::Cases(cases) => process_reset_cont_cases(cases, ctx),

        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Recurse into all case alternatives for `process_reset_cont`.
fn process_reset_cont_cases(cases: &Cases, ctx: &mut ResetContContext) -> Code {
    let new_alts: Vec<Alt> = cases
        .alts
        .iter()
        .map(|alt| match alt {
            Alt::Ctor {
                ctor_name,
                params,
                body,
            } => Alt::Ctor {
                ctor_name: ctor_name.clone(),
                params: params.clone(),
                body: Box::new(process_reset_cont(body, ctx)),
            },
            Alt::Default(body) => Alt::Default(Box::new(process_reset_cont(body, ctx))),
        })
        .collect();

    Code::Cases(Cases {
        type_name: cases.type_name.clone(),
        result_type: cases.result_type.clone(),
        scrutinee: cases.scrutinee,
        alts: new_alts,
    })
}

/// Expand a reuse site into a `reusejp` join-point pattern.
///
/// Transforms:
/// ```text
/// let y := reuse w ctor args
/// k
/// ```
/// Into:
/// ```text
/// jp reusejp(final):
///   k                       // shared continuation
/// cases isShared of
/// | false =>                // fast path: mutate in place
///   [unread field cleanup]
///   _setTag token ctor      (if cross-ctor)
///   _set token[i] arg_i     (skip self-sets)
///   jmp reusejp(token)
/// | true =>                 // slow path: fresh allocation
///   let new := ctor(args)
///   jmp reusejp(new)
/// ```
///
/// Reference: Lean 4 LCNF ExpandResetReuse.lean:199-266
fn expand_reuse_as_jp(
    decl: &LetDecl,
    body: &Code,
    remaining_args: &[Arg],
    ctor_name: Option<Name>,
    ctx: &mut ResetContContext,
) -> Code {
    // Process continuation for nested reuse/dec sites
    let processed_body = process_reset_cont(body, ctx);

    // Create reusejp(final) — the JP parameter reuses decl.fvar_id so the
    // continuation body references the correct variable without substitution.
    let reusejp_id = ctx.alloc.fresh().expect("FVarId allocation overflow");
    let reusejp = FunDecl::new(
        reusejp_id,
        Name::from_string("reusejp"),
        vec![Param::new(decl.fvar_id, decl.name.clone(), decl.ty.clone())],
        Expr::const_str("_"),
        processed_body,
    );

    // --- Fast path: set fields on token + jmp reusejp(token) ---
    let mut fast_path = Code::Jmp {
        jp: reusejp_id,
        args: vec![Arg::FVar(ctx.reset_var)],
    };

    // Set operations for non-self fields (reverse order for correct prepend)
    for (idx, arg) in remaining_args.iter().enumerate().rev() {
        if let Arg::FVar(arg_fvar) = arg {
            // Bug 17: skip self-sets (writing projected value back to same slot)
            if ctx.mask.get(arg_fvar) == Some(&(idx as u32)) {
                continue;
            }
            fast_path = Code::let_bind(
                LetDecl::new(
                    ctx.alloc.fresh().expect("FVarId allocation overflow"),
                    pseudo_op::NAME_SET.clone(),
                    Expr::const_str("_"),
                    LetValue::Const {
                        name: pseudo_op::NAME_SET.clone(),
                        levels: vec![],
                        args: vec![
                            Arg::FVar(ctx.reset_var),
                            Arg::Index(idx as u32),
                            Arg::FVar(*arg_fvar),
                        ],
                    },
                ),
                fast_path,
            );
        }
    }

    // Bug 18: setTag for cross-constructor reuse
    if let Some(ref ctor) = ctor_name {
        fast_path = Code::let_bind(
            LetDecl::new(
                ctx.alloc.fresh().expect("FVarId allocation overflow"),
                pseudo_op::NAME_SET_TAG.clone(),
                Expr::const_str("_"),
                LetValue::Const {
                    name: pseudo_op::NAME_SET_TAG.clone(),
                    levels: vec![],
                    args: vec![
                        Arg::FVar(ctx.reset_var),
                        Arg::Type(Expr::const_str(&ctor.to_string())),
                    ],
                },
            ),
            fast_path,
        );
    }

    // Bug 20: unread field cleanup on fast path
    fast_path = prepend_unread_field_cleanup_for_args(
        fast_path,
        ctx.reset_var,
        remaining_args,
        ctx.mask,
        ctx.alloc,
        ctx.type_map,
    );

    // --- Slow path: allocate new ctor + jmp reusejp(new) ---
    let new_alloc_var = ctx.alloc.fresh().expect("FVarId allocation overflow");
    let ctor_value = match ctor_name {
        Some(ref name) => LetValue::Ctor {
            name: name.clone(),
            levels: vec![],
            args: remaining_args.to_vec(),
        },
        None => LetValue::Ctor {
            name: pseudo_op::NAME_CTOR.clone(),
            levels: vec![],
            args: remaining_args.to_vec(),
        },
    };
    let slow_path = Code::let_bind(
        LetDecl::new(
            new_alloc_var,
            decl.name.clone(),
            decl.ty.clone(),
            ctor_value,
        ),
        Code::Jmp {
            jp: reusejp_id,
            args: vec![Arg::FVar(new_alloc_var)],
        },
    );

    // Combine: jp reusejp(final) { continuation } in cases isShared { fast | slow }
    Code::JoinPoint(
        reusejp,
        Box::new(Code::Cases(Cases {
            type_name: Name::from_string("Bool"),
            result_type: Expr::const_str("_"),
            scrutinee: ctx.is_shared,
            alts: vec![
                Alt::Ctor {
                    ctor_name: Name::from_string("Bool.false"),
                    params: vec![],
                    body: Box::new(fast_path),
                },
                Alt::Ctor {
                    ctor_name: Name::from_string("Bool.true"),
                    params: vec![],
                    body: Box::new(slow_path),
                },
            ],
        })),
    )
}
