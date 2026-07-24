// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Local dead code elimination for L5IR function bodies.
//!
//! Removes unused `VDecl` let-bindings and unreferenced `JDecl` join points
//! within a single function body. Uses a fixpoint iteration: collect all used
//! `VarId`/`JoinPointId` values, rebuild without dead nodes, repeat until
//! no more bindings are removed.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{IRAlt, IRArg, IRBody, IRExpr, JoinPointId, VarId};
use std::collections::HashSet;

// -----------------------------------------------------------------------
// Use-set collection
// -----------------------------------------------------------------------

/// Collect all `VarId`s and `JoinPointId`s that are *used* (as operands,
/// not at definition sites) anywhere in `body`.
pub(crate) fn collect_used(
    body: &IRBody,
    vars: &mut HashSet<VarId>,
    jps: &mut HashSet<JoinPointId>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_used_expr(value, vars);
            collect_used(rest, vars, jps);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_used(jp_body, vars, jps);
            collect_used(rest, vars, jps);
        }
        IRBody::Inc { var, rest, .. } => {
            vars.insert(*var);
            collect_used(rest, vars, jps);
        }
        IRBody::Dec { var, rest } => {
            vars.insert(*var);
            collect_used(rest, vars, jps);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            vars.insert(*var);
            vars.insert(*value);
            collect_used(rest, vars, jps);
        }
        IRBody::SetTag { var, rest, .. } => {
            vars.insert(*var);
            collect_used(rest, vars, jps);
        }
        IRBody::USet {
            var, value, rest, ..
        } => {
            vars.insert(*var);
            vars.insert(*value);
            collect_used(rest, vars, jps);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            vars.insert(*var);
            vars.insert(*value);
            collect_used(rest, vars, jps);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            vars.insert(*scrutinee);
            for alt in alts {
                collect_used(&alt.body, vars, jps);
            }
            if let Some(d) = default {
                collect_used(d, vars, jps);
            }
        }
        IRBody::Jmp { jp, args } => {
            jps.insert(*jp);
            collect_used_args(args, vars);
        }
        IRBody::Ret(arg) => {
            collect_used_arg(arg, vars);
        }
        IRBody::Unreachable => {}
    }
}

fn collect_used_arg(arg: &IRArg, vars: &mut HashSet<VarId>) {
    if let IRArg::Var(v) = arg {
        vars.insert(*v);
    }
}

fn collect_used_args(args: &[IRArg], vars: &mut HashSet<VarId>) {
    for a in args {
        collect_used_arg(a, vars);
    }
}

pub(crate) fn collect_used_expr(expr: &IRExpr, vars: &mut HashSet<VarId>) {
    match expr {
        IRExpr::Ctor { args, .. } => collect_used_args(args, vars),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            collect_used_arg(arg, vars);
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
        IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => {
            collect_used_args(args, vars);
        }
        IRExpr::ClosureApply { closure, args } => {
            collect_used_arg(closure, vars);
            collect_used_args(args, vars);
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            vars.insert(*var);
        }
        IRExpr::Reuse { var, args, .. } => {
            vars.insert(*var);
            collect_used_args(args, vars);
        }
    }
}

// -----------------------------------------------------------------------
// Rebuild-without-dead pass
// -----------------------------------------------------------------------

/// Eliminate dead `VDecl` bindings and dead `JDecl` join points.
///
/// Returns `(new_body, num_vdecls_removed)`.
pub(crate) fn eliminate_dead_locals(body: &IRBody) -> (IRBody, usize) {
    let mut current = body.clone();
    let mut total_removed = 0;

    loop {
        let mut used_vars = HashSet::new();
        let mut used_jps = HashSet::new();
        collect_used(&current, &mut used_vars, &mut used_jps);

        let (new_body, removed) = rebuild_without_dead(&current, &used_vars, &used_jps);
        total_removed += removed;
        if removed == 0 {
            return (new_body, total_removed);
        }
        current = new_body;
    }
}

fn rebuild_without_dead(
    body: &IRBody,
    used_vars: &HashSet<VarId>,
    used_jps: &HashSet<JoinPointId>,
) -> (IRBody, usize) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (new_rest, mut removed) = rebuild_without_dead(rest, used_vars, used_jps);
            if used_vars.contains(var) {
                (
                    IRBody::VDecl {
                        var: *var,
                        ty: ty.clone(),
                        value: value.clone(),
                        rest: Box::new(new_rest),
                    },
                    removed,
                )
            } else {
                removed += 1;
                (new_rest, removed)
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let (new_rest, mut removed) = rebuild_without_dead(rest, used_vars, used_jps);
            if used_jps.contains(jp) {
                let (new_jp_body, jp_removed) = rebuild_without_dead(jp_body, used_vars, used_jps);
                removed += jp_removed;
                (
                    IRBody::JDecl {
                        jp: *jp,
                        params: params.clone(),
                        body: Box::new(new_jp_body),
                        rest: Box::new(new_rest),
                    },
                    removed,
                )
            } else {
                removed += count_vdecls(jp_body);
                (new_rest, removed)
            }
        }
        IRBody::Inc { var, n, rest } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::Dec { var, rest } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::Set {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::SetTag { var, tag, rest } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::SetTag {
                    var: *var,
                    tag: *tag,
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::USet {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let (r, removed) = rebuild_without_dead(rest, used_vars, used_jps);
            (
                IRBody::SSet {
                    var: *var,
                    n: *n,
                    offset: *offset,
                    value: *value,
                    ty: ty.clone(),
                    rest: Box::new(r),
                },
                removed,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut removed = 0;
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| {
                    let (new_body, r) = rebuild_without_dead(&alt.body, used_vars, used_jps);
                    removed += r;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(new_body),
                    }
                })
                .collect();
            let new_default = default.as_ref().map(|d| {
                let (new_d, r) = rebuild_without_dead(d, used_vars, used_jps);
                removed += r;
                Box::new(new_d)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts: new_alts,
                    default: new_default,
                },
                removed,
            )
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (body.clone(), 0),
    }
}

/// Count VDecl nodes in a body subtree (for dead join-point accounting).
fn count_vdecls(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. } => 1 + count_vdecls(rest),
        IRBody::JDecl { body: b, rest, .. } => count_vdecls(b) + count_vdecls(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => count_vdecls(rest),
        IRBody::Case { alts, default, .. } => {
            let alt_count: usize = alts.iter().map(|a| count_vdecls(&a.body)).sum();
            let def_count = default.as_ref().map_or(0, |d| count_vdecls(d));
            alt_count + def_count
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}
