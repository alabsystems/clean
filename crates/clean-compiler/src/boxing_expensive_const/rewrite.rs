// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewrite pass for expensive constant boxing.
//!
//! Contains: max VarId computation and body rewriting using the hoist plan.

use super::HoistPlan;
use crate::ir::{IRAlt, IRArg, IRBody, IRExpr, IRType, VarId};

// ════════════════════════════════════════════════════════════════════════════
// Max VarId computation (for fresh ID generation)
// ════════════════════════════════════════════════════════════════════════════

pub(super) fn max_var_id(body: &IRBody, params: &[(VarId, IRType)]) -> u32 {
    let param_max = params.iter().map(|(v, _)| v.0).max().unwrap_or(0);
    param_max.max(max_var_in_body(body))
}

fn max_var_in_body(body: &IRBody) -> u32 {
    match body {
        IRBody::VDecl {
            var, rest, value, ..
        } => var.0.max(max_var_in_expr(value)).max(max_var_in_body(rest)),
        IRBody::JDecl {
            params, body, rest, ..
        } => {
            let p = params.iter().map(|(v, _)| v.0).max().unwrap_or(0);
            p.max(max_var_in_body(body)).max(max_var_in_body(rest))
        }
        IRBody::Inc { var, rest, .. } => var.0.max(max_var_in_body(rest)),
        IRBody::Dec { var, rest } => var.0.max(max_var_in_body(rest)),
        IRBody::Set {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_in_body(rest)),
        IRBody::SetTag { var, rest, .. } => var.0.max(max_var_in_body(rest)),
        IRBody::USet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_in_body(rest)),
        IRBody::SSet {
            var, value, rest, ..
        } => var.0.max(value.0).max(max_var_in_body(rest)),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let alt_max = alts
                .iter()
                .map(|a| max_var_in_body(&a.body))
                .max()
                .unwrap_or(0);
            let def_max = default.as_ref().map(|d| max_var_in_body(d)).unwrap_or(0);
            scrutinee.0.max(alt_max).max(def_max)
        }
        IRBody::Jmp { args, .. } => max_var_in_args(args),
        IRBody::Ret(arg) => max_var_in_arg(arg),
        IRBody::Unreachable => 0,
    }
}

fn max_var_in_expr(expr: &IRExpr) -> u32 {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => max_var_in_args(args),
        IRExpr::ClosureApply { closure, args } => {
            max_var_in_arg(closure).max(max_var_in_args(args))
        }
        IRExpr::Proj { arg, .. } | IRExpr::Box { arg, .. } | IRExpr::Unbox { arg, .. } => {
            max_var_in_arg(arg)
        }
        IRExpr::Tag(arg) => max_var_in_arg(arg),
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => var.0,
        IRExpr::Reuse { var, args, .. } => var.0.max(max_var_in_args(args)),
        IRExpr::Lit(_) | IRExpr::String(_) => 0,
    }
}

fn max_var_in_args(args: &[IRArg]) -> u32 {
    args.iter().map(max_var_in_arg).max().unwrap_or(0)
}

fn max_var_in_arg(arg: &IRArg) -> u32 {
    match arg {
        IRArg::Var(v) => v.0,
        IRArg::Erased => 0,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Pass 2: rewrite body using the hoist plan
// ════════════════════════════════════════════════════════════════════════════

pub(super) fn apply_plan(body: &IRBody, plan: &HoistPlan) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if plan.removed.contains_key(var) {
                apply_plan(rest, plan)
            } else {
                IRBody::VDecl {
                    var: subst_var(*var, plan),
                    ty: ty.clone(),
                    value: subst_expr(value, plan),
                    rest: Box::new(apply_plan(rest, plan)),
                }
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let new_params: Vec<_> = params
                .iter()
                .map(|(v, t)| (subst_var(*v, plan), t.clone()))
                .collect();
            IRBody::JDecl {
                jp: *jp,
                params: new_params,
                body: Box::new(apply_plan(jp_body, plan)),
                rest: Box::new(apply_plan(rest, plan)),
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: subst_var(*var, plan),
            n: *n,
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: subst_var(*var, plan),
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: subst_var(*var, plan),
            idx: *idx,
            value: subst_var(*value, plan),
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: subst_var(*var, plan),
            tag: *tag,
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: subst_var(*var, plan),
            idx: *idx,
            value: subst_var(*value, plan),
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: subst_var(*var, plan),
            n: *n,
            offset: *offset,
            value: subst_var(*value, plan),
            ty: ty.clone(),
            rest: Box::new(apply_plan(rest, plan)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(apply_plan(&a.body, plan)),
                })
                .collect();
            let new_default = default.as_ref().map(|d| Box::new(apply_plan(d, plan)));
            IRBody::Case {
                scrutinee: subst_var(*scrutinee, plan),
                alts: new_alts,
                default: new_default,
            }
        }
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: subst_args(args, plan),
        },
        IRBody::Ret(arg) => IRBody::Ret(subst_arg(arg, plan)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Substitution helpers
// ════════════════════════════════════════════════════════════════════════════

fn subst_var(var: VarId, plan: &HoistPlan) -> VarId {
    plan.subst.get(&var).copied().unwrap_or(var)
}

fn subst_arg(arg: &IRArg, plan: &HoistPlan) -> IRArg {
    match arg {
        IRArg::Var(v) => IRArg::Var(subst_var(*v, plan)),
        IRArg::Erased => IRArg::Erased,
    }
}

fn subst_args(args: &[IRArg], plan: &HoistPlan) -> Vec<IRArg> {
    args.iter().map(|a| subst_arg(a, plan)).collect()
}

fn subst_expr(expr: &IRExpr, plan: &HoistPlan) -> IRExpr {
    match expr {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: subst_args(args, plan),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: subst_arg(arg, plan),
        },
        IRExpr::Tag(arg) => IRExpr::Tag(subst_arg(arg, plan)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: subst_arg(arg, plan),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: subst_arg(arg, plan),
        },
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: subst_args(args, plan),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: subst_args(args, plan),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: subst_arg(closure, plan),
            args: subst_args(args, plan),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: subst_var(*var, plan),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: subst_var(*var, plan),
            ty: ty.clone(),
        },
        IRExpr::IsShared(var) => IRExpr::IsShared(subst_var(*var, plan)),
        IRExpr::Reset(var) => IRExpr::Reset(subst_var(*var, plan)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: subst_var(*var, plan),
            ctor: ctor.clone(),
            args: subst_args(args, plan),
        },
        IRExpr::Lit(_) | IRExpr::String(_) => expr.clone(),
    }
}
