// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Body visitor and VDecl expression transformation for the explicit boxing pass.

use super::cast::{box_args, cast_arg_if_needed, cast_args, cast_var_if_needed, wrap_with_prefix};
use super::BoxingContext;
use crate::ir::{
    FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::mangle::mangle_boxed_name;
use clean_kernel::Name;

use super::boxed_version::requires_boxed_version;

pub(crate) fn try_correct_vdecl_type(ty: &IRType, value: &IRExpr, ctx: &BoxingContext) -> IRType {
    match value {
        IRExpr::Apply { fn_id, .. } => ctx
            .get_decl(fn_id)
            .map(|d| d.return_type.clone())
            .unwrap_or_else(|| ty.clone()),
        IRExpr::PartialApply { .. } => IRType::Object,
        IRExpr::ClosureApply { .. } => IRType::Object,
        IRExpr::Tag(_) => IRType::USize,
        IRExpr::Unbox { .. } => ty.clone(),
        IRExpr::Box { .. } => IRType::TObject,
        // Proj's result type is determined by its ty field (the projected
        // field's type), not the VDecl's declared type.
        IRExpr::Proj { ty: proj_ty, .. } => proj_ty.clone(),
        // Variants whose result type is the declared VDecl type.
        // Exhaustive so adding a new IRExpr variant forces a compile error here.
        IRExpr::Ctor { .. }
        | IRExpr::Lit(_)
        | IRExpr::String(_)
        | IRExpr::Reset(_)
        | IRExpr::Reuse { .. } => ty.clone(),
    }
}

/// Check if a variable holds an expensive constant that should be boxed once.
/// Returns Some(aux_call_expr) if an aux decl was created, None otherwise.
pub(crate) fn expensive_constant_boxing(
    var: VarId,
    var_type: &IRType,
    ctx: &mut BoxingContext,
) -> Option<IRExpr> {
    // Skip cheap types - small integers fit in tagged pointers
    match var_type {
        IRType::UInt8 | IRType::UInt16 | IRType::Bool => return None,
        _ if !var_type.is_scalar() => return None,
        _ => {}
    }

    let value = ctx.get_var_value(var)?.clone();
    let is_expensive = match &value {
        IRExpr::Lit(_) => true,
        IRExpr::Apply { args, .. } if args.is_empty() => true,
        _ => false,
    };
    if !is_expensive {
        return None;
    }

    // Create aux decl that boxes once at init time
    let aux_name = ctx.mk_aux_name();
    let aux_body = IRBody::VDecl {
        var: VarId(0),
        ty: var_type.clone(),
        value,
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::TObject,
            value: IRExpr::Box {
                ty: var_type.clone(),
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        }),
    };
    let aux_decl = IRDecl {
        name: aux_name.clone(),
        params: vec![],
        return_type: IRType::TObject,
        body: aux_body,
    };
    ctx.add_aux_decl(aux_decl);
    Some(IRExpr::Apply {
        fn_id: FnId(aux_name),
        args: vec![],
    })
}

/// Check if function needs boxed version for partial application.
pub(crate) fn requires_boxed_version_for_pap(fn_id: &FnId, ctx: &BoxingContext) -> bool {
    ctx.get_decl(fn_id)
        .map(requires_boxed_version)
        .unwrap_or(false)
}

/// Compute expected scrutinee type for case analysis based on constructors.
pub(crate) fn expected_case_scrutinee_type(alts: &[IRAlt]) -> IRType {
    // If all alternatives are scalar constructors (no object fields), scrutinee can stay scalar
    if alts
        .iter()
        .all(|a| a.ctor.num_objects == 0 && a.ctor.num_scalars <= 1)
    {
        IRType::USize // Tag value is enough
    } else {
        IRType::Object
    }
}

pub(crate) fn visit_body(body: &IRBody, ctx: &mut BoxingContext) -> IRBody {
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
        IRBody::Jmp { jp, args } => visit_body_jmp(*jp, args, ctx),
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(visit_body(rest, ctx)),
        },
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
        IRBody::SSet {
            var,
            offset,
            ty,
            value,
            rest,
        } => IRBody::SSet {
            var: *var,
            offset: *offset,
            ty: ty.clone(),
            value: *value,
            rest: Box::new(visit_body(rest, ctx)),
        },
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

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
    let expected = expected_case_scrutinee_type(&alts);
    cast_var_if_needed(scrutinee, &expected, ctx, |s| IRBody::Case {
        scrutinee: s,
        alts,
        default,
    })
}

fn visit_body_jmp(jp: JoinPointId, args: &[IRArg], ctx: &mut BoxingContext) -> IRBody {
    let params = ctx.get_jp_params(jp);
    let (cast_args_vec, prefix) = cast_args(args, &params, ctx);
    wrap_with_prefix(
        prefix,
        IRBody::Jmp {
            jp,
            args: cast_args_vec,
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
                // Use field_types for type-aware casting: scalar args stay
                // unboxed, only object args get boxed. (#1979)
                let (cast_args_vec, prefix) = cast_args(args, &info.field_types, ctx);
                wrap_with_prefix(
                    prefix,
                    IRBody::VDecl {
                        var,
                        ty: ty.clone(),
                        value: IRExpr::Ctor {
                            info: info.clone(),
                            args: cast_args_vec,
                        },
                        rest: Box::new(rest),
                    },
                )
            }
        }
        IRExpr::Apply { fn_id, args } => {
            let (cast_args_vec, prefix) = if let Some(decl) = ctx.get_decl(fn_id) {
                cast_args(
                    args,
                    &decl
                        .params
                        .iter()
                        .map(|(_, t)| t.clone())
                        .collect::<Vec<_>>(),
                    ctx,
                )
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
        IRExpr::PartialApply { fn_id, arity, args } => {
            // Use boxed version if function has scalar params/return
            let actual_fn_id = if requires_boxed_version_for_pap(fn_id, ctx) {
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
                        arity: *arity,
                        args: boxed_args,
                    },
                    rest: Box::new(rest),
                },
            )
        }
        IRExpr::ClosureApply { closure, args } => {
            // All args must be boxed to Object — closure application is dynamic dispatch.
            let (boxed_args, args_prefix) = box_args(args, ctx);
            // Closure itself is already Object type, but ensure it's cast.
            let (boxed_closure, closure_prefix) =
                cast_args(std::slice::from_ref(closure), &[IRType::Object], ctx);
            let mut all_prefix = closure_prefix;
            all_prefix.extend(args_prefix);
            wrap_with_prefix(
                all_prefix,
                IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: IRExpr::ClosureApply {
                        closure: boxed_closure
                            .into_iter()
                            .next()
                            .expect("invariant: cast_args returns one element per input"),
                        args: boxed_args,
                    },
                    rest: Box::new(rest),
                },
            )
        }
        IRExpr::Reuse {
            var: reuse_var,
            ctor,
            args,
        } => {
            // Use ctor field_types for type-aware casting: scalar args stay
            // unboxed, only object args get boxed. (#1979)
            let (cast_args_vec, prefix) = cast_args(args, &ctor.field_types, ctx);
            wrap_with_prefix(
                prefix,
                IRBody::VDecl {
                    var,
                    ty: ty.clone(),
                    value: IRExpr::Reuse {
                        var: *reuse_var,
                        ctor: ctor.clone(),
                        args: cast_args_vec,
                    },
                    rest: Box::new(rest),
                },
            )
        }
        // Variants with no Vec<IRArg> that needs boxing — pass through as-is.
        // Exhaustive so adding a new IRExpr variant forces a compile error here.
        IRExpr::Proj { .. }
        | IRExpr::Tag(_)
        | IRExpr::Box { .. }
        | IRExpr::Unbox { .. }
        | IRExpr::Lit(_)
        | IRExpr::String(_)
        | IRExpr::Reset(_) => IRBody::VDecl {
            var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(rest),
        },
    }
}
