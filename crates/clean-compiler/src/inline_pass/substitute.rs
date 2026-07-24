// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Argument substitution and body splicing for L5IR function inlining.
//!
//! When a call `let v := f(a, b); rest` is inlined, the callee's body
//! needs two transformations:
//!
//! 1. **Substitution** -- replace parameter VarIds with the call-site
//!    argument VarIds, and shift local VarIds to avoid collisions.
//! 2. **Splicing** -- replace `Ret(x)` in the inlined body with
//!    `let v := x; rest` so the continuation is properly connected.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashMap;

// -----------------------------------------------------------------------
// Argument substitution
// -----------------------------------------------------------------------

/// Substitute function parameters with call-site arguments in a body.
///
/// Remaps `VarId`s: parameters are replaced by the corresponding argument
/// `VarId`s. Local `VarId`s defined inside the body are shifted by `offset`
/// to avoid collisions with the caller's namespace.
pub(crate) fn substitute_args(
    body: &IRBody,
    param_vars: &[(VarId, IRType)],
    args: &[IRArg],
    offset: u32,
) -> IRBody {
    let mut subst: HashMap<VarId, IRArg> = HashMap::new();
    for (param, arg) in param_vars.iter().zip(args.iter()) {
        subst.insert(param.0, arg.clone());
    }
    let mut local_remap: HashMap<VarId, VarId> = HashMap::new();
    substitute_body(body, &subst, &mut local_remap, offset)
}

fn remap_var(
    v: VarId,
    subst: &HashMap<VarId, IRArg>,
    local_remap: &HashMap<VarId, VarId>,
) -> IRArg {
    if let Some(arg) = subst.get(&v) {
        arg.clone()
    } else if let Some(&remapped) = local_remap.get(&v) {
        IRArg::Var(remapped)
    } else {
        IRArg::Var(v)
    }
}

fn remap_arg(
    arg: &IRArg,
    subst: &HashMap<VarId, IRArg>,
    local_remap: &HashMap<VarId, VarId>,
) -> IRArg {
    match arg {
        IRArg::Var(v) => remap_var(*v, subst, local_remap),
        IRArg::Erased => IRArg::Erased,
    }
}

fn remap_args(
    args: &[IRArg],
    subst: &HashMap<VarId, IRArg>,
    local_remap: &HashMap<VarId, VarId>,
) -> Vec<IRArg> {
    args.iter()
        .map(|a| remap_arg(a, subst, local_remap))
        .collect()
}

/// Resolve a VarId for contexts that require a plain VarId (not IRArg).
/// Falls back to the original VarId if substitution yields Erased.
fn resolve_var(
    v: VarId,
    subst: &HashMap<VarId, IRArg>,
    local_remap: &HashMap<VarId, VarId>,
) -> VarId {
    if let Some(arg) = subst.get(&v) {
        match arg {
            IRArg::Var(w) => *w,
            IRArg::Erased => v,
        }
    } else if let Some(&remapped) = local_remap.get(&v) {
        remapped
    } else {
        v
    }
}

fn fresh_local(v: VarId, offset: u32, local_remap: &mut HashMap<VarId, VarId>) -> VarId {
    let new_v = VarId(v.0 + offset);
    local_remap.insert(v, new_v);
    new_v
}

fn substitute_body(
    body: &IRBody,
    subst: &HashMap<VarId, IRArg>,
    local_remap: &mut HashMap<VarId, VarId>,
    offset: u32,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_var = fresh_local(*var, offset, local_remap);
            let new_value = substitute_expr(value, subst, local_remap);
            let new_rest = substitute_body(rest, subst, local_remap, offset);
            IRBody::VDecl {
                var: new_var,
                ty: ty.clone(),
                value: new_value,
                rest: Box::new(new_rest),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let new_params: Vec<(VarId, IRType)> = params
                .iter()
                .map(|(v, t)| (fresh_local(*v, offset, local_remap), t.clone()))
                .collect();
            let new_jp_body = substitute_body(jp_body, subst, local_remap, offset);
            let new_rest = substitute_body(rest, subst, local_remap, offset);
            IRBody::JDecl {
                jp: *jp,
                params: new_params,
                body: Box::new(new_jp_body),
                rest: Box::new(new_rest),
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: resolve_var(*var, subst, local_remap),
            n: *n,
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: resolve_var(*var, subst, local_remap),
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: resolve_var(*var, subst, local_remap),
            idx: *idx,
            value: resolve_var(*value, subst, local_remap),
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: resolve_var(*var, subst, local_remap),
            tag: *tag,
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: resolve_var(*var, subst, local_remap),
            idx: *idx,
            value: resolve_var(*value, subst, local_remap),
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::SSet {
            var,
            n,
            offset: soff,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: resolve_var(*var, subst, local_remap),
            n: *n,
            offset: *soff,
            value: resolve_var(*value, subst, local_remap),
            ty: ty.clone(),
            rest: Box::new(substitute_body(rest, subst, local_remap, offset)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: resolve_var(*scrutinee, subst, local_remap),
            alts: alts
                .iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor.clone(),
                    body: Box::new(substitute_body(&alt.body, subst, local_remap, offset)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(substitute_body(d, subst, local_remap, offset))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: remap_args(args, subst, local_remap),
        },
        IRBody::Ret(arg) => IRBody::Ret(remap_arg(arg, subst, local_remap)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

fn substitute_expr(
    expr: &IRExpr,
    subst: &HashMap<VarId, IRArg>,
    local_remap: &HashMap<VarId, VarId>,
) -> IRExpr {
    match expr {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: remap_args(args, subst, local_remap),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: remap_arg(arg, subst, local_remap),
        },
        IRExpr::Tag(arg) => IRExpr::Tag(remap_arg(arg, subst, local_remap)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: remap_arg(arg, subst, local_remap),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: remap_arg(arg, subst, local_remap),
        },
        IRExpr::Lit(lit) => IRExpr::Lit(lit.clone()),
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: remap_args(args, subst, local_remap),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: remap_args(args, subst, local_remap),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: remap_arg(closure, subst, local_remap),
            args: remap_args(args, subst, local_remap),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: resolve_var(*var, subst, local_remap),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: resolve_var(*var, subst, local_remap),
            ty: ty.clone(),
        },
        IRExpr::IsShared(var) => IRExpr::IsShared(resolve_var(*var, subst, local_remap)),
        IRExpr::String(s) => IRExpr::String(s.clone()),
        IRExpr::Reset(var) => IRExpr::Reset(resolve_var(*var, subst, local_remap)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: resolve_var(*var, subst, local_remap),
            ctor: ctor.clone(),
            args: remap_args(args, subst, local_remap),
        },
    }
}

// -----------------------------------------------------------------------
// Splicing
// -----------------------------------------------------------------------

/// Replace `Ret(arg)` in the inlined body with `let result_var := <arg>; rest`.
///
/// This connects the inlined callee's return value to the caller's
/// continuation code.
pub(crate) fn splice_inlined(
    inlined: IRBody,
    result_var: VarId,
    result_ty: IRType,
    continuation: &IRBody,
) -> IRBody {
    match inlined {
        IRBody::Ret(arg) => match arg {
            IRArg::Var(v) => IRBody::VDecl {
                var: result_var,
                ty: result_ty,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("_identity")),
                    args: vec![IRArg::Var(v)],
                },
                rest: Box::new(continuation.clone()),
            },
            IRArg::Erased => continuation.clone(),
        },
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var,
            ty,
            value,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => IRBody::JDecl {
            jp,
            params,
            body: Box::new(splice_inlined(
                *body,
                result_var,
                result_ty.clone(),
                continuation,
            )),
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var,
            n,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var,
            idx,
            value,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var,
            tag,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var,
            idx,
            value,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest: Box::new(splice_inlined(*rest, result_var, result_ty, continuation)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee,
            alts: alts
                .into_iter()
                .map(|alt| IRAlt {
                    ctor: alt.ctor,
                    body: Box::new(splice_inlined(
                        *alt.body,
                        result_var,
                        result_ty.clone(),
                        continuation,
                    )),
                })
                .collect(),
            default: default.map(|d| {
                Box::new(splice_inlined(
                    *d,
                    result_var,
                    result_ty.clone(),
                    continuation,
                ))
            }),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp { jp, args },
        IRBody::Unreachable => IRBody::Unreachable,
    }
}
