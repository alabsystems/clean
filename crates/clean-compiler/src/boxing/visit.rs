// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IR body visitor and transform core for the boxing pass.

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRExpr, IRLiteral, IRType, VarId};
use crate::mangle::mangle_boxed_name;
use clean_kernel::Name;

use super::boxed_version::mk_boxed_version;
use super::cast::{box_args, cast_arg_if_needed, cast_args, cast_var_if_needed, wrap_with_prefix};
use super::context::BoxingContext;

pub fn try_correct_vdecl_type(ty: &IRType, value: &IRExpr, ctx: &BoxingContext) -> IRType {
    match value {
        IRExpr::Apply { fn_id, .. } => ctx
            .get_decl(fn_id)
            .map(|d| d.return_type.clone())
            .unwrap_or_else(|| ty.clone()),
        IRExpr::PartialApply { .. } => IRType::Object,
        IRExpr::ClosureApply { .. } => IRType::Object,
        IRExpr::Tag(_) => IRType::USize,
        IRExpr::Proj { ty: proj_ty, .. } => proj_ty.clone(),
        IRExpr::UProj { .. } => IRType::USize,
        IRExpr::SProj { ty: sproj_ty, .. } => sproj_ty.clone(),
        IRExpr::IsShared(_) => IRType::UInt8,
        IRExpr::Unbox { ty: unbox_ty, .. } => unbox_ty.clone(),
        IRExpr::Box { .. } => IRType::Object,
        _ => ty.clone(),
    }
}

pub fn visit_body(body: &IRBody, ctx: &mut BoxingContext) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let corrected_ty = try_correct_vdecl_type(ty, value, ctx);
            ctx.set_var_type(*var, corrected_ty.clone());
            ctx.set_var_value(*var, value.clone());
            let rest = visit_body(rest, ctx);
            visit_vdecl_expr(*var, &corrected_ty, value, rest, ctx)
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            ctx.set_jp_params(*jp, params.iter().map(|(_, t)| t.clone()).collect());
            for (v, t) in params {
                ctx.set_var_type(*v, t.clone());
            }
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(visit_body(jp_body, ctx)),
                rest: Box::new(visit_body(rest, ctx)),
            }
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => visit_body_case(*scrutinee, alts, default, ctx),
        IRBody::Ret(arg) => {
            let expected = ctx.result_type().clone();
            cast_arg_if_needed(arg, &expected, ctx, IRBody::Ret)
        }
        IRBody::Jmp { jp, args } => {
            let params = ctx.get_jp_params(*jp);
            let (cast_args_vec, prefix) = cast_args(args, &params, ctx);
            wrap_with_prefix(
                prefix,
                IRBody::Jmp {
                    jp: *jp,
                    args: cast_args_vec,
                },
            )
        }
        _ => visit_body_passthrough(body, ctx),
    }
}

/// Handle IRBody variants that pass through the boxing pass unchanged
/// (only recursing into their `rest` continuation).
fn visit_body_passthrough(body: &IRBody, ctx: &mut BoxingContext) -> IRBody {
    match body {
        // Inc/Dec are RC ops inserted at L5CNF (rc::insert), BEFORE the boxing
        // pass assigns final IRTypes. A Nat literal that the RC pass conservatively
        // treats as a possibly-boxed BigNum can later be lowered to a pure scalar
        // (e.g. USize) by to_ir + boxing. The boxing pass is the first stage that
        // knows every var's final IRType (var_types is populated top-down as
        // VDecls/params are walked, and an Inc/Dec always follows its var's VDecl),
        // so it is the authoritative place to drop RC ops that landed on a
        // provably-scalar var. is_scalar() is true ONLY for Bool/UIntN/USize/FloatN
        // — never Object/Struct/Union — and get_var_type defaults unknown vars to
        // Object, so this can only ever drop an op on an affirmatively-scalar var,
        // never on an object or an unknown. Dropping inc/dec on a scalar is a no-op
        // (Lean's lean_inc/lean_dec are scalar-guarded) and preserves refcount
        // discipline. This keeps the IR checker's V5 rule intact.
        IRBody::Inc { var, n, rest } => {
            let rest = visit_body(rest, ctx);
            if ctx.get_var_type(*var).is_scalar() {
                rest
            } else {
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest),
                }
            }
        }
        IRBody::Dec { var, rest } => {
            let rest = visit_body(rest, ctx);
            if ctx.get_var_type(*var).is_scalar() {
                rest
            } else {
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest),
                }
            }
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::Unreachable => IRBody::Unreachable,
        // The remaining variants are dispatched by `visit_body` before this
        // helper is ever called, so they never reach here. Enumerating them
        // explicitly (instead of a catch-all `_`) keeps the match exhaustive:
        // if `IRBody` gains a variant, the compiler forces it to be classified
        // here rather than silently routing it into a runtime panic.
        IRBody::VDecl { .. }
        | IRBody::JDecl { .. }
        | IRBody::Case { .. }
        | IRBody::Ret(_)
        | IRBody::Jmp { .. } => {
            unreachable!("non-passthrough body variant in visit_body_passthrough")
        }
    }
}

/// Handle Case in the boxing pass (extracted from visit_body for size).
fn visit_body_case(
    scrutinee: VarId,
    alts: &[IRAlt],
    default: &Option<Box<IRBody>>,
    ctx: &mut BoxingContext,
) -> IRBody {
    let alts: Vec<_> = alts
        .iter()
        .map(|a| IRAlt {
            ctor: a.ctor.clone(),
            body: Box::new(visit_body(&a.body, ctx)),
        })
        .collect();
    let default = default.as_ref().map(|d| Box::new(visit_body(d, ctx)));
    let expected = BoxingContext::expected_case_scrutinee_type(&alts, default.is_some());
    cast_var_if_needed(scrutinee, &expected, ctx, |s| IRBody::Case {
        scrutinee: s,
        alts,
        default,
    })
}

/// Box arguments for an Apply expression, resolving parameter types if known.
fn visit_vdecl_apply(
    var: VarId,
    ty: &IRType,
    fn_id: &FnId,
    args: &[IRArg],
    rest: IRBody,
    ctx: &mut BoxingContext,
) -> IRBody {
    let (cast_args_vec, prefix) = if let Some(decl) = ctx.get_decl(fn_id) {
        let param_tys: Vec<_> = decl.params.iter().map(|(_, t)| t.clone()).collect();
        cast_args(args, &param_tys, ctx)
    } else {
        box_args(args, ctx)
    };
    wrap_with_prefix(
        prefix,
        IRBody::VDecl {
            var,
            ty: ty.clone(),
            value: IRExpr::Apply {
                fn_id: fn_id.clone(),
                args: cast_args_vec,
            },
            rest: Box::new(rest),
        },
    )
}

/// Box arguments for a PartialApply, redirecting to boxed wrapper if needed.
fn visit_vdecl_partial_apply(
    var: VarId,
    ty: &IRType,
    fn_id: &FnId,
    incoming_arity: u16,
    args: &[IRArg],
    rest: IRBody,
    ctx: &mut BoxingContext,
) -> IRBody {
    let arity = ctx
        .get_decl(fn_id)
        .map(|d| d.params.len() as u16)
        .unwrap_or(incoming_arity);
    let actual_fn_id = if ctx.requires_boxed_version_for_pap(fn_id) {
        // CORRECTNESS: a PartialApply over a scalar-signature callee is lowered
        // to a closure over the callee's `_boxed` wrapper, which adapts the
        // uniform boxed closure calling convention (unbox scalar args, call the
        // real function, box the scalar result). That wrapper MUST be defined or
        // the emitted C references an undeclared symbol — the higher-order
        // `Nat.ble` / `Bool.decEq` `clean_alloc_closure` link failure. When
        // `generate_boxed_versions` is on the driver emits every such wrapper
        // module-wide; when it is off (e.g. `--opt-level 0`) it emits none, so
        // synthesize exactly the wrapper this redirect needs here. The driver
        // deduplicates it module-wide (a callee captured as a closure from
        // several sites is recorded once per site).
        if !ctx.config.generate_boxed_versions {
            if let Some(wrapper) = ctx.get_decl(fn_id).map(mk_boxed_version) {
                ctx.add_aux_decl(wrapper);
            }
        }
        let mangled = crate::mangle::mangle_name(&fn_id.0);
        FnId(Name::from_string(&mangle_boxed_name(&mangled)))
    } else {
        fn_id.clone()
    };
    let (boxed_args, prefix) = box_args(args, ctx);
    wrap_with_prefix(
        prefix,
        IRBody::VDecl {
            var,
            ty: ty.clone(),
            value: IRExpr::PartialApply {
                fn_id: actual_fn_id,
                arity,
                args: boxed_args,
            },
            rest: Box::new(rest),
        },
    )
}

/// Box closure and all arguments for a ClosureApply.
fn visit_vdecl_closure_apply(
    var: VarId,
    ty: &IRType,
    closure: &IRArg,
    args: &[IRArg],
    rest: IRBody,
    ctx: &mut BoxingContext,
) -> IRBody {
    let all_args: Vec<IRArg> = std::iter::once(closure.clone())
        .chain(args.iter().cloned())
        .collect();
    let (boxed_all, prefix) = box_args(&all_args, ctx);
    let boxed_closure = boxed_all[0].clone();
    let boxed_args = boxed_all[1..].to_vec();
    wrap_with_prefix(
        prefix,
        IRBody::VDecl {
            var,
            ty: ty.clone(),
            value: IRExpr::ClosureApply {
                closure: boxed_closure,
                args: boxed_args,
            },
            rest: Box::new(rest),
        },
    )
}

fn visit_vdecl_expr(
    var: VarId,
    ty: &IRType,
    value: &IRExpr,
    rest: IRBody,
    ctx: &mut BoxingContext,
) -> IRBody {
    match value {
        IRExpr::Ctor { info, args } => {
            if info.num_objects == 0 && info.num_scalars <= 1 && ty.is_scalar() {
                IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: IRExpr::Lit(IRLiteral::UInt32(info.tag)),
                    rest: Box::new(rest),
                }
            } else {
                let (boxed_args, prefix) = box_args(args, ctx);
                wrap_with_prefix(
                    prefix,
                    IRBody::VDecl {
                        var,
                        ty: ty.clone(),
                        value: IRExpr::Ctor {
                            info: info.clone(),
                            args: boxed_args,
                        },
                        rest: Box::new(rest),
                    },
                )
            }
        }
        IRExpr::Apply { fn_id, args } => visit_vdecl_apply(var, ty, fn_id, args, rest, ctx),
        IRExpr::PartialApply { fn_id, arity, args } => {
            visit_vdecl_partial_apply(var, ty, fn_id, *arity, args, rest, ctx)
        }
        IRExpr::ClosureApply { closure, args } => {
            visit_vdecl_closure_apply(var, ty, closure, args, rest, ctx)
        }
        IRExpr::Reuse {
            var: reuse_var,
            ctor,
            args,
        } => {
            let (boxed_args, prefix) = box_args(args, ctx);
            wrap_with_prefix(
                prefix,
                IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: IRExpr::Reuse {
                        var: *reuse_var,
                        ctor: ctor.clone(),
                        args: boxed_args,
                    },
                    rest: Box::new(rest),
                },
            )
        }
        // Scalar-carrier rebox (`UInt{8,16,32,64}/USize.toBitVec` and the RUNG-B
        // `clean_nat_of_u64` Nat producer): projecting a field out of an unboxed
        // SCALAR carrier reboxes it as a FRESH, uniquely-owned Nat object.
        // `rc::insert` models every projection as a BORROWED field read and so
        // inserts a borrow->own `Inc` on the result — correct for a real
        // object-field projection, but SPURIOUS for a fresh rebox (the value is
        // already owned; `Ret`/the sole consumer transfers that one reference).
        // It was harmless while the rebox was the tagged immediate (`clean_inc`
        // is scalar-guarded), but is a genuine refcount leak once the carrier is
        // `>= 2^63` and the rebox is a heap Nat cell. Strip exactly that one
        // baseline `Inc` unit when it immediately follows the rebox. Conditioned
        // on the carrier being scalar and the result pointer-class, so it never
        // touches a genuine object projection; capped at one unit, so a rebox
        // dup'd for multiple owners keeps every legitimate `Inc`.
        IRExpr::Proj {
            arg: IRArg::Var(carrier),
            ..
        } if ctx.get_var_type(*carrier).is_scalar() && ty.lowers_to_ptr() => {
            let rest = match rest {
                IRBody::Inc {
                    var: iv,
                    n,
                    rest: r,
                } if iv == var => {
                    if n <= 1 {
                        *r
                    } else {
                        IRBody::Inc {
                            var: iv,
                            n: n - 1,
                            rest: r,
                        }
                    }
                }
                other => other,
            };
            IRBody::VDecl {
                var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(rest),
            }
        }
        _ => IRBody::VDecl {
            var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(rest),
        },
    }
}
