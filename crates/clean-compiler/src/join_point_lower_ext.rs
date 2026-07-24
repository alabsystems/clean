// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended join point optimization pass for L5IR.
//!
//! Performs detection, inlining, fusion, dead elimination, and validation
//! of join points within a single function body. Runs as a fixpoint loop.
//!
//! Part of #3083 - Extensibility epic.

use std::collections::{HashMap, HashSet};

use crate::dce_local::collect_used;
use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};

// ── Types ──────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub(crate) struct JpExtConfig {
    pub enabled: bool,
    pub inline_threshold: usize,
    pub fuse_enabled: bool,
    pub hoist_enabled: bool,
    pub max_iterations: usize,
}
impl Default for JpExtConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            inline_threshold: 5,
            fuse_enabled: true,
            hoist_enabled: true,
            max_iterations: 10,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct JpExtStats {
    pub join_points_detected: usize,
    pub join_points_inlined: usize,
    pub join_points_fused: usize,
    pub join_points_eliminated: usize,
    pub join_points_hoisted: usize,
    pub recursive_join_points: usize,
    pub iterations: usize,
}
impl JpExtStats {
    #[must_use]
    pub fn total(&self) -> usize {
        self.join_points_inlined
            + self.join_points_fused
            + self.join_points_eliminated
            + self.join_points_hoisted
    }
}

#[derive(Clone, Debug)]
pub(crate) struct JoinPointInfo {
    pub jp: JoinPointId,
    pub params: Vec<(VarId, IRType)>,
    pub body_size: usize,
    pub call_count: usize,
    pub is_recursive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum JpValidationError {
    UndefinedTarget {
        jp_id: u32,
    },
    ArityMismatch {
        jp_id: u32,
        expected: usize,
        actual: usize,
    },
}

// ── Helpers ────────────────────────────────────────────────────────────

fn body_size(body: &IRBody) -> usize {
    match body {
        IRBody::JDecl { body: b, rest, .. } => 1 + body_size(b) + body_size(rest),
        IRBody::Case { alts, default, .. } => {
            1 + alts.iter().map(|a| body_size(&a.body)).sum::<usize>()
                + default.as_ref().map_or(0, |d| body_size(d))
        }
        _ => 1 + rest_of(body).map_or(0, body_size),
    }
}

fn rest_of(body: &IRBody) -> Option<&IRBody> {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => Some(rest),
        _ => None,
    }
}

fn collect_jp_refs(body: &IRBody) -> HashMap<JoinPointId, usize> {
    let mut m = HashMap::new();
    walk_jmps(body, &mut m);
    m
}

fn walk_jmps(body: &IRBody, m: &mut HashMap<JoinPointId, usize>) {
    match body {
        IRBody::Jmp { jp, .. } => {
            *m.entry(*jp).or_insert(0) += 1;
        }
        IRBody::JDecl { body: b, rest, .. } => {
            walk_jmps(b, m);
            walk_jmps(rest, m);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                walk_jmps(&a.body, m);
            }
            if let Some(d) = default {
                walk_jmps(d, m);
            }
        }
        other => {
            if let Some(r) = rest_of(other) {
                walk_jmps(r, m);
            }
        }
    }
}

fn jp_is_self_recursive(target: JoinPointId, body: &IRBody) -> bool {
    match body {
        IRBody::Jmp { jp, .. } => *jp == target,
        IRBody::JDecl { body: b, rest, .. } => {
            jp_is_self_recursive(target, b) || jp_is_self_recursive(target, rest)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|a| jp_is_self_recursive(target, &a.body))
                || default
                    .as_ref()
                    .is_some_and(|d| jp_is_self_recursive(target, d))
        }
        other => rest_of(other).is_some_and(|r| jp_is_self_recursive(target, r)),
    }
}

// ── Substitution ───────────────────────────────────────────────────────

fn sv(v: VarId, m: &HashMap<VarId, IRArg>) -> VarId {
    if let Some(IRArg::Var(nv)) = m.get(&v) {
        *nv
    } else {
        v
    }
}
fn sa(arg: &IRArg, m: &HashMap<VarId, IRArg>) -> IRArg {
    match arg {
        IRArg::Var(v) => m.get(v).cloned().unwrap_or_else(|| arg.clone()),
        IRArg::Erased => IRArg::Erased,
    }
}

fn substitute_body(body: &IRBody, m: &HashMap<VarId, IRArg>) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: subst_expr(value, m),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: sv(*var, m),
            n: *n,
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: sv(*var, m),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: sv(*var, m),
            idx: *idx,
            value: sv(*value, m),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: sv(*var, m),
            tag: *tag,
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: sv(*var, m),
            idx: *idx,
            value: sv(*value, m),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: sv(*var, m),
            n: *n,
            offset: *offset,
            value: sv(*value, m),
            ty: ty.clone(),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(substitute_body(b, m)),
            rest: Box::new(substitute_body(rest, m)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: sv(*scrutinee, m),
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(substitute_body(&a.body, m)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(substitute_body(d, m))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRBody::Ret(arg) => IRBody::Ret(sa(arg, m)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

fn subst_expr(expr: &IRExpr, m: &HashMap<VarId, IRArg>) -> IRExpr {
    match expr {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: sa(arg, m),
        },
        IRExpr::Tag(arg) => IRExpr::Tag(sa(arg, m)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: sa(arg, m),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: sa(arg, m),
        },
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: sa(closure, m),
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: sv(*var, m),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: sv(*var, m),
            ty: ty.clone(),
        },
        IRExpr::IsShared(var) => IRExpr::IsShared(sv(*var, m)),
        IRExpr::Reset(var) => IRExpr::Reset(sv(*var, m)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: sv(*var, m),
            ctor: ctor.clone(),
            args: args.iter().map(|a| sa(a, m)).collect(),
        },
        IRExpr::Lit(_) | IRExpr::String(_) => expr.clone(),
    }
}

// ── Detection ──────────────────────────────────────────────────────────

#[must_use]
pub(crate) fn detect_join_points(body: &IRBody) -> Vec<JoinPointInfo> {
    let refs = collect_jp_refs(body);
    let mut out = Vec::new();
    detect_inner(body, &refs, &mut out);
    out
}
fn detect_inner(body: &IRBody, refs: &HashMap<JoinPointId, usize>, out: &mut Vec<JoinPointInfo>) {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            out.push(JoinPointInfo {
                jp: *jp,
                params: params.clone(),
                body_size: body_size(b),
                call_count: refs.get(jp).copied().unwrap_or(0),
                is_recursive: jp_is_self_recursive(*jp, b),
            });
            detect_inner(b, refs, out);
            detect_inner(rest, refs, out);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                detect_inner(&a.body, refs, out);
            }
            if let Some(d) = default {
                detect_inner(d, refs, out);
            }
        }
        other => {
            if let Some(r) = rest_of(other) {
                detect_inner(r, refs, out);
            }
        }
    }
}

// ── Parameter analysis ─────────────────────────────────────────────────

#[must_use]
pub(crate) fn analyze_jp_params(body: &IRBody) -> HashMap<JoinPointId, Vec<bool>> {
    let mut result = HashMap::new();
    ap_inner(body, &mut result);
    result
}
fn ap_inner(body: &IRBody, result: &mut HashMap<JoinPointId, Vec<bool>>) {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            let mut uv = HashSet::new();
            let mut uj = HashSet::new();
            collect_used(b, &mut uv, &mut uj);
            result.insert(*jp, params.iter().map(|(v, _)| uv.contains(v)).collect());
            ap_inner(b, result);
            ap_inner(rest, result);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                ap_inner(&a.body, result);
            }
            if let Some(d) = default {
                ap_inner(d, result);
            }
        }
        other => {
            if let Some(r) = rest_of(other) {
                ap_inner(r, result);
            }
        }
    }
}

// ── Inline small join points ───────────────────────────────────────────

#[must_use]
pub(crate) fn inline_small_join_points(body: &IRBody, threshold: usize) -> (IRBody, usize) {
    let refs = collect_jp_refs(body);
    let mut tgts: HashMap<JoinPointId, (Vec<(VarId, IRType)>, IRBody)> = HashMap::new();
    find_inlineable(body, &refs, threshold, &mut tgts);
    if tgts.is_empty() {
        return (body.clone(), 0);
    }
    let ids: HashSet<JoinPointId> = tgts.keys().copied().collect();
    let mut count = 0;
    let result = do_inline(body, &tgts, &ids, &mut count);
    (result, count)
}

fn find_inlineable(
    body: &IRBody,
    refs: &HashMap<JoinPointId, usize>,
    th: usize,
    out: &mut HashMap<JoinPointId, (Vec<(VarId, IRType)>, IRBody)>,
) {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            if body_size(b) <= th
                && refs.get(jp).copied().unwrap_or(0) == 1
                && !jp_is_self_recursive(*jp, b)
            {
                out.insert(*jp, (params.clone(), *b.clone()));
            }
            find_inlineable(b, refs, th, out);
            find_inlineable(rest, refs, th, out);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                find_inlineable(&a.body, refs, th, out);
            }
            if let Some(d) = default {
                find_inlineable(d, refs, th, out);
            }
        }
        other => {
            if let Some(r) = rest_of(other) {
                find_inlineable(r, refs, th, out);
            }
        }
    }
}

fn do_inline(
    body: &IRBody,
    tgts: &HashMap<JoinPointId, (Vec<(VarId, IRType)>, IRBody)>,
    ids: &HashSet<JoinPointId>,
    c: &mut usize,
) -> IRBody {
    let mut active = HashSet::new();
    do_inline_inner(body, tgts, ids, c, &mut active)
}

fn do_inline_inner(
    body: &IRBody,
    tgts: &HashMap<JoinPointId, (Vec<(VarId, IRType)>, IRBody)>,
    ids: &HashSet<JoinPointId>,
    c: &mut usize,
    active: &mut HashSet<JoinPointId>,
) -> IRBody {
    match body {
        IRBody::Jmp { jp, args } if ids.contains(jp) => {
            inline_target_jmp(*jp, args, tgts, ids, c, active).unwrap_or_else(|| body.clone())
        }
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } if ids.contains(jp) => do_inline_inner(rest, tgts, ids, c, active),
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(do_inline_inner(b, tgts, ids, c, active)),
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
        },
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
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
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
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
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
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
            rest: Box::new(do_inline_inner(rest, tgts, ids, c, active)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: *scrutinee,
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(do_inline_inner(&a.body, tgts, ids, c, active)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(do_inline_inner(d, tgts, ids, c, active))),
        },
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

fn inline_target_jmp(
    jp: JoinPointId,
    args: &[IRArg],
    tgts: &HashMap<JoinPointId, (Vec<(VarId, IRType)>, IRBody)>,
    ids: &HashSet<JoinPointId>,
    c: &mut usize,
    active: &mut HashSet<JoinPointId>,
) -> Option<IRBody> {
    if !active.insert(jp) {
        return None;
    }
    let result = tgts.get(&jp).and_then(|(params, jb)| {
        if params.len() != args.len() {
            return None;
        }
        let m: HashMap<VarId, IRArg> = params
            .iter()
            .zip(args)
            .map(|((v, _), a)| (*v, a.clone()))
            .collect();
        *c += 1;
        let substituted = substitute_body(jb, &m);
        Some(do_inline_inner(&substituted, tgts, ids, c, active))
    });
    active.remove(&jp);
    result
}

// ── Fuse join points ───────────────────────────────────────────────────

#[derive(Clone, Debug)]
struct ForwardingJoinPoint {
    params: Vec<(VarId, IRType)>,
    target: JoinPointId,
    args: Vec<IRArg>,
}

#[must_use]
pub(crate) fn fuse_join_points(body: &IRBody) -> (IRBody, usize) {
    let mut fwd: HashMap<JoinPointId, ForwardingJoinPoint> = HashMap::new();
    find_fwd(body, &mut fwd);
    if fwd.is_empty() {
        return (body.clone(), 0);
    }
    let mut count = 0;
    let result = do_fuse(body, &fwd, &mut count);
    (result, count)
}

fn find_fwd(body: &IRBody, fwd: &mut HashMap<JoinPointId, ForwardingJoinPoint>) {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            if let IRBody::Jmp { jp: t, args } = b.as_ref() {
                if *t != *jp {
                    fwd.insert(
                        *jp,
                        ForwardingJoinPoint {
                            params: params.clone(),
                            target: *t,
                            args: args.clone(),
                        },
                    );
                }
            }
            find_fwd(b, fwd);
            find_fwd(rest, fwd);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                find_fwd(&a.body, fwd);
            }
            if let Some(d) = default {
                find_fwd(d, fwd);
            }
        }
        other => {
            if let Some(r) = rest_of(other) {
                find_fwd(r, fwd);
            }
        }
    }
}

fn do_fuse(
    body: &IRBody,
    fwd: &HashMap<JoinPointId, ForwardingJoinPoint>,
    c: &mut usize,
) -> IRBody {
    match body {
        IRBody::JDecl { jp, rest, .. } if is_safe_forward(*jp, fwd) => {
            *c += 1;
            do_fuse(rest, fwd, c)
        }
        IRBody::Jmp { jp, args } => {
            if fwd.contains_key(jp) {
                let mut active = HashSet::new();
                if let Some((target, resolved_args)) =
                    resolve_forward_call(*jp, args, fwd, &mut active)
                {
                    if target != *jp || resolved_args.as_slice() != args.as_slice() {
                        return IRBody::Jmp {
                            jp: target,
                            args: resolved_args,
                        };
                    }
                }
            }
            body.clone()
        }
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(do_fuse(b, fwd, c)),
            rest: Box::new(do_fuse(rest, fwd, c)),
        },
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(do_fuse(rest, fwd, c)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(do_fuse(rest, fwd, c)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(do_fuse(rest, fwd, c)),
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
            rest: Box::new(do_fuse(rest, fwd, c)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(do_fuse(rest, fwd, c)),
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
            rest: Box::new(do_fuse(rest, fwd, c)),
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
            rest: Box::new(do_fuse(rest, fwd, c)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: *scrutinee,
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(do_fuse(&a.body, fwd, c)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(do_fuse(d, fwd, c))),
        },
        IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

fn is_safe_forward(jp: JoinPointId, fwd: &HashMap<JoinPointId, ForwardingJoinPoint>) -> bool {
    let Some(info) = fwd.get(&jp) else {
        return false;
    };
    let identity_args: Vec<IRArg> = info
        .params
        .iter()
        .map(|(var, _)| IRArg::Var(*var))
        .collect();
    let mut active = HashSet::new();
    resolve_forward_call(jp, &identity_args, fwd, &mut active)
        .is_some_and(|(target, _)| target != jp)
}

fn resolve_forward_call(
    jp: JoinPointId,
    args: &[IRArg],
    fwd: &HashMap<JoinPointId, ForwardingJoinPoint>,
    active: &mut HashSet<JoinPointId>,
) -> Option<(JoinPointId, Vec<IRArg>)> {
    if !active.insert(jp) {
        return None;
    }
    let result = if let Some(info) = fwd.get(&jp) {
        if info.params.len() != args.len() {
            None
        } else {
            let subst: HashMap<VarId, IRArg> = info
                .params
                .iter()
                .zip(args)
                .map(|((var, _), arg)| (*var, arg.clone()))
                .collect();
            let forwarded_args: Vec<IRArg> = info.args.iter().map(|arg| sa(arg, &subst)).collect();
            resolve_forward_call(info.target, &forwarded_args, fwd, active)
        }
    } else {
        Some((jp, args.to_vec()))
    };
    active.remove(&jp);
    result
}

// ── Dead join point elimination ────────────────────────────────────────

#[must_use]
pub(crate) fn eliminate_dead_join_points(body: &IRBody) -> (IRBody, usize) {
    let refs = collect_jp_refs(body);
    let mut count = 0;
    let result = do_elim(body, &refs, &mut count);
    (result, count)
}

fn do_elim(body: &IRBody, refs: &HashMap<JoinPointId, usize>, c: &mut usize) -> IRBody {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            let nr = do_elim(rest, refs, c);
            if refs.get(jp).copied().unwrap_or(0) == 0 {
                *c += 1;
                nr
            } else {
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(do_elim(b, refs, c)),
                    rest: Box::new(nr),
                }
            }
        }
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(do_elim(rest, refs, c)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(do_elim(rest, refs, c)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(do_elim(rest, refs, c)),
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
            rest: Box::new(do_elim(rest, refs, c)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(do_elim(rest, refs, c)),
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
            rest: Box::new(do_elim(rest, refs, c)),
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
            rest: Box::new(do_elim(rest, refs, c)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: *scrutinee,
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(do_elim(&a.body, refs, c)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(do_elim(d, refs, c))),
        },
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

// ── Validation ─────────────────────────────────────────────────────────

pub(crate) fn validate_join_points(body: &IRBody) -> Result<(), JpValidationError> {
    let mut scope: HashMap<JoinPointId, usize> = HashMap::new();
    val(body, &mut scope)
}
fn val(body: &IRBody, scope: &mut HashMap<JoinPointId, usize>) -> Result<(), JpValidationError> {
    match body {
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => {
            scope.insert(*jp, params.len());
            val(b, scope)?;
            val(rest, scope)?;
            scope.remove(jp);
            Ok(())
        }
        IRBody::Jmp { jp, args } => {
            let exp = scope
                .get(jp)
                .ok_or(JpValidationError::UndefinedTarget { jp_id: jp.0 })?;
            if args.len() != *exp {
                return Err(JpValidationError::ArityMismatch {
                    jp_id: jp.0,
                    expected: *exp,
                    actual: args.len(),
                });
            }
            Ok(())
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                val(&a.body, scope)?;
            }
            if let Some(d) = default {
                val(d, scope)?;
            }
            Ok(())
        }
        other => {
            if let Some(r) = rest_of(other) {
                val(r, scope)
            } else {
                Ok(())
            }
        }
    }
}

// ── Orchestration ──────────────────────────────────────────────────────

#[must_use]
pub(crate) fn run_join_point_ext(body: &IRBody, config: &JpExtConfig) -> (IRBody, JpExtStats) {
    let mut stats = JpExtStats::default();
    if !config.enabled {
        return (body.clone(), stats);
    }
    let info = detect_join_points(body);
    stats.join_points_detected = info.len();
    stats.recursive_join_points = info.iter().filter(|i| i.is_recursive).count();
    let mut cur = body.clone();
    for _ in 0..config.max_iterations {
        stats.iterations += 1;
        let mut changed = false;
        if config.fuse_enabled {
            let (next, n) = fuse_join_points(&cur);
            if n > 0 {
                stats.join_points_fused += n;
                changed = true;
                cur = next;
            }
        }
        let (next, n) = inline_small_join_points(&cur, config.inline_threshold);
        if n > 0 {
            stats.join_points_inlined += n;
            changed = true;
            cur = next;
        }
        let (next, n) = eliminate_dead_join_points(&cur);
        if n > 0 {
            stats.join_points_eliminated += n;
            changed = true;
            cur = next;
        }
        if !changed {
            break;
        }
    }
    (cur, stats)
}

#[must_use]
pub(crate) fn run_join_point_ext_default(body: &IRBody) -> (IRBody, JpExtStats) {
    run_join_point_ext(body, &JpExtConfig::default())
}

#[must_use]
pub(crate) fn run_join_point_ext_decl(decl: &IRDecl, config: &JpExtConfig) -> (IRDecl, JpExtStats) {
    let (new_body, stats) = run_join_point_ext(&decl.body, config);
    (
        IRDecl {
            name: decl.name.clone(),
            params: decl.params.clone(),
            return_type: decl.return_type.clone(),
            body: new_body,
        },
        stats,
    )
}
