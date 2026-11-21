// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Variable renaming over final L5IR, for `tail_loop`'s fresh loop
//! parameters.

use crate::ir::{IRAlt, IRArg, IRBody, IRExpr, VarId};

/// The largest variable id `body` binds or mentions (0 when none).
pub(super) fn max_var_id(body: &IRBody) -> u32 {
    let max = std::cell::Cell::new(0u32);
    map_vars(body, &|v| {
        max.set(max.get().max(v.0));
        v
    });
    max.get()
}

/// `body` with every variable occurrence (binders included) mapped by `f`.
pub(super) fn map_vars(body: &IRBody, f: &dyn Fn(VarId) -> VarId) -> IRBody {
    let arg = |a: &IRArg| match a {
        IRArg::Var(v) => IRArg::Var(f(*v)),
        IRArg::Erased => IRArg::Erased,
    };
    let args = |xs: &[IRArg]| xs.iter().map(arg).collect::<Vec<_>>();
    let rest = |r: &IRBody| Box::new(map_vars(r, f));
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest: r,
        } => IRBody::VDecl {
            var: f(*var),
            ty: ty.clone(),
            value: map_expr_vars(value, f),
            rest: rest(r),
        },
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest: r,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.iter().map(|(v, t)| (f(*v), t.clone())).collect(),
            body: rest(b),
            rest: rest(r),
        },
        IRBody::Inc { var, n, rest: r } => IRBody::Inc {
            var: f(*var),
            n: *n,
            rest: rest(r),
        },
        IRBody::Dec { var, rest: r } => IRBody::Dec {
            var: f(*var),
            rest: rest(r),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest: r,
        } => IRBody::Set {
            var: f(*var),
            idx: *idx,
            value: f(*value),
            rest: rest(r),
        },
        IRBody::SetTag { var, tag, rest: r } => IRBody::SetTag {
            var: f(*var),
            tag: *tag,
            rest: rest(r),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest: r,
        } => IRBody::USet {
            var: f(*var),
            idx: *idx,
            value: f(*value),
            rest: rest(r),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest: r,
        } => IRBody::SSet {
            var: f(*var),
            n: *n,
            offset: *offset,
            value: f(*value),
            ty: ty.clone(),
            rest: rest(r),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: f(*scrutinee),
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: rest(&a.body),
                })
                .collect(),
            default: default.as_ref().map(|d| rest(d)),
        },
        IRBody::Jmp { jp, args: a } => IRBody::Jmp {
            jp: *jp,
            args: args(a),
        },
        IRBody::Ret(a) => IRBody::Ret(arg(a)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

fn map_expr_vars(expr: &IRExpr, f: &dyn Fn(VarId) -> VarId) -> IRExpr {
    let arg = |a: &IRArg| match a {
        IRArg::Var(v) => IRArg::Var(f(*v)),
        IRArg::Erased => IRArg::Erased,
    };
    let args = |xs: &[IRArg]| xs.iter().map(arg).collect::<Vec<_>>();
    match expr {
        IRExpr::Ctor { info, args: a } => IRExpr::Ctor {
            info: info.clone(),
            args: args(a),
        },
        IRExpr::Proj { idx, ty, arg: a } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: arg(a),
        },
        IRExpr::Tag(a) => IRExpr::Tag(arg(a)),
        IRExpr::Box { ty, arg: a } => IRExpr::Box {
            ty: ty.clone(),
            arg: arg(a),
        },
        IRExpr::Unbox { ty, arg: a } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: arg(a),
        },
        IRExpr::Apply { fn_id, args: a } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: args(a),
        },
        IRExpr::PartialApply {
            fn_id,
            arity,
            args: a,
        } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: args(a),
        },
        IRExpr::ClosureApply { closure, args: a } => IRExpr::ClosureApply {
            closure: arg(closure),
            args: args(a),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: f(*var),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: f(*var),
            ty: ty.clone(),
        },
        IRExpr::IsShared(v) => IRExpr::IsShared(f(*v)),
        IRExpr::Reset(v) => IRExpr::Reset(f(*v)),
        IRExpr::Reuse { var, ctor, args: a } => IRExpr::Reuse {
            var: f(*var),
            ctor: ctor.clone(),
            args: args(a),
        },
        IRExpr::Lit(_) | IRExpr::String(_) => expr.clone(),
    }
}
