// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IR analysis: node statistics, def-use chains, structural comparison,
//! well-formedness validation, subexpression extraction, and pretty summary.
//! Complements `probing_ext` (body size, var usage, call graph, RC ops).

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, JoinPointId, VarId};
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

// ── Error ──────────────────────────────────────────────────────────────────

/// Errors from IR well-formedness validation.
#[derive(Debug, Clone, Error)]
pub(crate) enum IrValidationError {
    #[error("variable {0:?} used but never defined")]
    UndefinedVar(VarId),
    #[error("variable {0:?} defined more than once")]
    DuplicateDef(VarId),
    #[error("join point {0:?} jumped to but never declared")]
    UndefinedJoinPoint(JoinPointId),
    #[error("join point {0:?} declared more than once")]
    DuplicateJoinPoint(JoinPointId),
    #[error("join point {jp:?} called with {actual} args, expected {expected}")]
    JoinPointArityMismatch {
        jp: JoinPointId,
        expected: usize,
        actual: usize,
    },
}

// ── Node-kind statistics ───────────────────────────────────────────────────

/// Counts of each IR body node kind.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NodeKindCounts {
    pub(crate) vdecl: usize,
    pub(crate) jdecl: usize,
    pub(crate) inc: usize,
    pub(crate) dec: usize,
    pub(crate) set: usize,
    pub(crate) set_tag: usize,
    pub(crate) uset: usize,
    pub(crate) sset: usize,
    pub(crate) case: usize,
    pub(crate) jmp: usize,
    pub(crate) ret: usize,
    pub(crate) unreachable: usize,
}

impl NodeKindCounts {
    /// Total number of nodes across all kinds.
    #[must_use]
    pub(crate) fn total(&self) -> usize {
        self.vdecl
            + self.jdecl
            + self.inc
            + self.dec
            + self.set
            + self.set_tag
            + self.uset
            + self.sset
            + self.case
            + self.jmp
            + self.ret
            + self.unreachable
    }
}

/// Count each IR body node kind in `body`.
#[must_use]
pub(crate) fn node_kind_counts(body: &IRBody) -> NodeKindCounts {
    let mut c = NodeKindCounts::default();
    count_kinds(body, &mut c);
    c
}

fn count_kinds(body: &IRBody, c: &mut NodeKindCounts) {
    match body {
        IRBody::VDecl { rest, .. } => {
            c.vdecl += 1;
            count_kinds(rest, c);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            c.jdecl += 1;
            count_kinds(jp, c);
            count_kinds(rest, c);
        }
        IRBody::Inc { rest, .. } => {
            c.inc += 1;
            count_kinds(rest, c);
        }
        IRBody::Dec { rest, .. } => {
            c.dec += 1;
            count_kinds(rest, c);
        }
        IRBody::Set { rest, .. } => {
            c.set += 1;
            count_kinds(rest, c);
        }
        IRBody::SetTag { rest, .. } => {
            c.set_tag += 1;
            count_kinds(rest, c);
        }
        IRBody::USet { rest, .. } => {
            c.uset += 1;
            count_kinds(rest, c);
        }
        IRBody::SSet { rest, .. } => {
            c.sset += 1;
            count_kinds(rest, c);
        }
        IRBody::Case { alts, default, .. } => {
            c.case += 1;
            for alt in alts {
                count_kinds(&alt.body, c);
            }
            if let Some(d) = default {
                count_kinds(d, c);
            }
        }
        IRBody::Jmp { .. } => c.jmp += 1,
        IRBody::Ret(_) => c.ret += 1,
        IRBody::Unreachable => c.unreachable += 1,
    }
}

// ── Nesting depth ──────────────────────────────────────────────────────────

/// Maximum nesting depth of the entire IR body (not just cases).
#[must_use]
pub(crate) fn nesting_depth(body: &IRBody) -> usize {
    depth_impl(body, 0)
}

fn depth_impl(body: &IRBody, d: usize) -> usize {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => depth_impl(rest, d + 1),
        IRBody::JDecl { body: jp, rest, .. } => depth_impl(jp, d + 1).max(depth_impl(rest, d + 1)),
        IRBody::Case { alts, default, .. } => {
            let mut mx = d + 1;
            for alt in alts {
                mx = mx.max(depth_impl(&alt.body, d + 1));
            }
            if let Some(df) = default {
                mx = mx.max(depth_impl(df, d + 1));
            }
            mx
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => d,
    }
}

// ── Def-use chains ─────────────────────────────────────────────────────────

/// Where a variable is defined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DefSite {
    VDecl,
    JDeclParam { jp: JoinPointId },
    FuncParam,
}

/// Def-use chain: maps VarId to definition site and use count.
#[derive(Debug, Clone)]
pub(crate) struct DefUseChain {
    pub(crate) defs: HashMap<VarId, DefSite>,
    pub(crate) uses: HashMap<VarId, usize>,
}

/// Build def-use chains for a declaration.
#[must_use]
pub(crate) fn def_use_chain(decl: &IRDecl) -> DefUseChain {
    let mut defs = HashMap::new();
    let mut uses = HashMap::new();
    for (var, _) in &decl.params {
        defs.insert(*var, DefSite::FuncParam);
    }
    du_body(&decl.body, &mut defs, &mut uses);
    DefUseChain { defs, uses }
}

fn du_bump(uses: &mut HashMap<VarId, usize>, v: VarId) {
    *uses.entry(v).or_insert(0) += 1;
}

fn du_arg(a: &IRArg, uses: &mut HashMap<VarId, usize>) {
    if let IRArg::Var(v) = a {
        du_bump(uses, *v);
    }
}

fn du_expr(expr: &IRExpr, uses: &mut HashMap<VarId, usize>) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => args.iter().for_each(|a| du_arg(a, uses)),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => du_arg(arg, uses),
        IRExpr::ClosureApply { closure, args } => {
            du_arg(closure, uses);
            args.iter().for_each(|a| du_arg(a, uses));
        }
        IRExpr::UProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var)
        | IRExpr::SProj { var, .. } => du_bump(uses, *var),
        IRExpr::Reuse { var, args, .. } => {
            du_bump(uses, *var);
            args.iter().for_each(|a| du_arg(a, uses));
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}

fn du_body(body: &IRBody, defs: &mut HashMap<VarId, DefSite>, uses: &mut HashMap<VarId, usize>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            defs.insert(*var, DefSite::VDecl);
            du_expr(value, uses);
            du_body(rest, defs, uses);
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            for (v, _) in params {
                defs.insert(*v, DefSite::JDeclParam { jp: *jp });
            }
            du_body(jp_body, defs, uses);
            du_body(rest, defs, uses);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            du_bump(uses, *var);
            du_body(rest, defs, uses);
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            du_bump(uses, *var);
            du_bump(uses, *value);
            du_body(rest, defs, uses);
        }
        IRBody::SetTag { var, rest, .. } => {
            du_bump(uses, *var);
            du_body(rest, defs, uses);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            du_bump(uses, *scrutinee);
            for alt in alts {
                du_body(&alt.body, defs, uses);
            }
            if let Some(d) = default {
                du_body(d, defs, uses);
            }
        }
        IRBody::Jmp { args, .. } => args.iter().for_each(|a| du_arg(a, uses)),
        IRBody::Ret(arg) => du_arg(arg, uses),
        IRBody::Unreachable => {}
    }
}

/// Variables defined but never used.
#[must_use]
pub(crate) fn dead_vars(chain: &DefUseChain) -> Vec<VarId> {
    let mut d: Vec<VarId> = chain
        .defs
        .keys()
        .filter(|v| chain.uses.get(v).copied().unwrap_or(0) == 0)
        .copied()
        .collect();
    d.sort_by_key(|v| v.0);
    d
}

// ── Structural comparison (alpha-equivalence) ──────────────────────────────

type VMap = HashMap<VarId, VarId>;

/// Compare two IR bodies for structural equality ignoring VarId values.
#[must_use]
pub(crate) fn structurally_equal(a: &IRBody, b: &IRBody) -> bool {
    seq_body(a, b, &mut VMap::new(), &mut VMap::new())
}

fn sv(va: VarId, vb: VarId, ab: &mut VMap, ba: &mut VMap) -> bool {
    match (ab.get(&va), ba.get(&vb)) {
        (Some(&mb), Some(&ma)) => mb == vb && ma == va,
        (None, None) => {
            ab.insert(va, vb);
            ba.insert(vb, va);
            true
        }
        _ => false,
    }
}
fn sa(a: &IRArg, b: &IRArg, ab: &mut VMap, ba: &mut VMap) -> bool {
    match (a, b) {
        (IRArg::Var(va), IRArg::Var(vb)) => sv(*va, *vb, ab, ba),
        (IRArg::Erased, IRArg::Erased) => true,
        _ => false,
    }
}
fn sas(a: &[IRArg], b: &[IRArg], ab: &mut VMap, ba: &mut VMap) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| sa(x, y, ab, ba))
}
fn se(a: &IRExpr, b: &IRExpr, ab: &mut VMap, ba: &mut VMap) -> bool {
    match (a, b) {
        (IRExpr::Ctor { args: aa, .. }, IRExpr::Ctor { args: ab2, .. }) => sas(aa, ab2, ab, ba),
        (
            IRExpr::Proj {
                idx: i1,
                ty: t1,
                arg: a1,
            },
            IRExpr::Proj {
                idx: i2,
                ty: t2,
                arg: a2,
            },
        ) => i1 == i2 && t1 == t2 && sa(a1, a2, ab, ba),
        (IRExpr::Tag(a1), IRExpr::Tag(a2)) => sa(a1, a2, ab, ba),
        (IRExpr::Box { ty: t1, arg: a1 }, IRExpr::Box { ty: t2, arg: a2 })
        | (IRExpr::Unbox { ty: t1, arg: a1 }, IRExpr::Unbox { ty: t2, arg: a2 }) => {
            t1 == t2 && sa(a1, a2, ab, ba)
        }
        (IRExpr::Lit(l1), IRExpr::Lit(l2)) => format!("{l1:?}") == format!("{l2:?}"),
        (IRExpr::String(s1), IRExpr::String(s2)) => s1 == s2,
        (
            IRExpr::Apply {
                fn_id: f1,
                args: a1,
            },
            IRExpr::Apply {
                fn_id: f2,
                args: a2,
            },
        ) => f1 == f2 && sas(a1, a2, ab, ba),
        (
            IRExpr::PartialApply {
                fn_id: f1,
                arity: r1,
                args: a1,
            },
            IRExpr::PartialApply {
                fn_id: f2,
                arity: r2,
                args: a2,
            },
        ) => f1 == f2 && r1 == r2 && sas(a1, a2, ab, ba),
        (
            IRExpr::ClosureApply {
                closure: c1,
                args: a1,
            },
            IRExpr::ClosureApply {
                closure: c2,
                args: a2,
            },
        ) => sa(c1, c2, ab, ba) && sas(a1, a2, ab, ba),
        (IRExpr::UProj { idx: i1, var: v1 }, IRExpr::UProj { idx: i2, var: v2 }) => {
            i1 == i2 && sv(*v1, *v2, ab, ba)
        }
        (
            IRExpr::SProj {
                n: n1,
                offset: o1,
                var: v1,
                ty: t1,
            },
            IRExpr::SProj {
                n: n2,
                offset: o2,
                var: v2,
                ty: t2,
            },
        ) => n1 == n2 && o1 == o2 && t1 == t2 && sv(*v1, *v2, ab, ba),
        (IRExpr::IsShared(v1), IRExpr::IsShared(v2)) | (IRExpr::Reset(v1), IRExpr::Reset(v2)) => {
            sv(*v1, *v2, ab, ba)
        }
        (
            IRExpr::Reuse {
                var: v1, args: a1, ..
            },
            IRExpr::Reuse {
                var: v2, args: a2, ..
            },
        ) => sv(*v1, *v2, ab, ba) && sas(a1, a2, ab, ba),
        _ => false,
    }
}
fn seq_body(a: &IRBody, b: &IRBody, ab: &mut VMap, ba: &mut VMap) -> bool {
    match (a, b) {
        (
            IRBody::VDecl {
                var: v1,
                ty: t1,
                value: e1,
                rest: r1,
            },
            IRBody::VDecl {
                var: v2,
                ty: t2,
                value: e2,
                rest: r2,
            },
        ) => sv(*v1, *v2, ab, ba) && t1 == t2 && se(e1, e2, ab, ba) && seq_body(r1, r2, ab, ba),
        (
            IRBody::JDecl {
                jp: j1,
                params: p1,
                body: b1,
                rest: r1,
            },
            IRBody::JDecl {
                jp: j2,
                params: p2,
                body: b2,
                rest: r2,
            },
        ) => {
            j1 == j2
                && p1.len() == p2.len()
                && p1
                    .iter()
                    .zip(p2)
                    .all(|((v1, t1), (v2, t2))| sv(*v1, *v2, ab, ba) && t1 == t2)
                && seq_body(b1, b2, ab, ba)
                && seq_body(r1, r2, ab, ba)
        }
        (
            IRBody::Inc {
                var: v1,
                n: n1,
                rest: r1,
            },
            IRBody::Inc {
                var: v2,
                n: n2,
                rest: r2,
            },
        ) => n1 == n2 && sv(*v1, *v2, ab, ba) && seq_body(r1, r2, ab, ba),
        (IRBody::Dec { var: v1, rest: r1 }, IRBody::Dec { var: v2, rest: r2 }) => {
            sv(*v1, *v2, ab, ba) && seq_body(r1, r2, ab, ba)
        }
        (
            IRBody::Set {
                var: v1,
                idx: i1,
                value: u1,
                rest: r1,
            },
            IRBody::Set {
                var: v2,
                idx: i2,
                value: u2,
                rest: r2,
            },
        ) => i1 == i2 && sv(*v1, *v2, ab, ba) && sv(*u1, *u2, ab, ba) && seq_body(r1, r2, ab, ba),
        (
            IRBody::SetTag {
                var: v1,
                tag: t1,
                rest: r1,
            },
            IRBody::SetTag {
                var: v2,
                tag: t2,
                rest: r2,
            },
        ) => t1 == t2 && sv(*v1, *v2, ab, ba) && seq_body(r1, r2, ab, ba),
        (
            IRBody::USet {
                var: v1,
                idx: i1,
                value: u1,
                rest: r1,
            },
            IRBody::USet {
                var: v2,
                idx: i2,
                value: u2,
                rest: r2,
            },
        ) => i1 == i2 && sv(*v1, *v2, ab, ba) && sv(*u1, *u2, ab, ba) && seq_body(r1, r2, ab, ba),
        (
            IRBody::SSet {
                var: v1,
                n: n1,
                offset: o1,
                value: u1,
                ty: t1,
                rest: r1,
            },
            IRBody::SSet {
                var: v2,
                n: n2,
                offset: o2,
                value: u2,
                ty: t2,
                rest: r2,
            },
        ) => {
            n1 == n2
                && o1 == o2
                && t1 == t2
                && sv(*v1, *v2, ab, ba)
                && sv(*u1, *u2, ab, ba)
                && seq_body(r1, r2, ab, ba)
        }
        (
            IRBody::Case {
                scrutinee: s1,
                alts: a1,
                default: d1,
            },
            IRBody::Case {
                scrutinee: s2,
                alts: a2,
                default: d2,
            },
        ) => {
            sv(*s1, *s2, ab, ba)
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2)
                    .all(|(x, y)| seq_body(&x.body, &y.body, ab, ba))
                && match (d1, d2) {
                    (Some(x), Some(y)) => seq_body(x, y, ab, ba),
                    (None, None) => true,
                    _ => false,
                }
        }
        (IRBody::Jmp { jp: j1, args: a1 }, IRBody::Jmp { jp: j2, args: a2 }) => {
            j1 == j2 && sas(a1, a2, ab, ba)
        }
        (IRBody::Ret(a1), IRBody::Ret(a2)) => sa(a1, a2, ab, ba),
        (IRBody::Unreachable, IRBody::Unreachable) => true,
        _ => false,
    }
}

// ── IR validation ──────────────────────────────────────────────────────────

/// Validate well-formedness of an IR declaration.
pub(crate) fn validate_decl(decl: &IRDecl) -> Result<(), Vec<IrValidationError>> {
    let mut errs = Vec::new();
    let mut defs: HashSet<VarId> = HashSet::new();
    let mut jp_ar: HashMap<JoinPointId, usize> = HashMap::new();
    let mut jp_def: HashSet<JoinPointId> = HashSet::new();
    for (v, _) in &decl.params {
        if !defs.insert(*v) {
            errs.push(IrValidationError::DuplicateDef(*v));
        }
    }
    vld_body(&decl.body, &mut defs, &mut jp_ar, &mut jp_def, &mut errs);
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

fn vld_arg(a: &IRArg, defs: &HashSet<VarId>, errs: &mut Vec<IrValidationError>) {
    if let IRArg::Var(v) = a {
        if !defs.contains(v) {
            errs.push(IrValidationError::UndefinedVar(*v));
        }
    }
}
fn vld_var(v: VarId, defs: &HashSet<VarId>, errs: &mut Vec<IrValidationError>) {
    if !defs.contains(&v) {
        errs.push(IrValidationError::UndefinedVar(v));
    }
}
fn vld_expr(expr: &IRExpr, defs: &HashSet<VarId>, errs: &mut Vec<IrValidationError>) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => args.iter().for_each(|a| vld_arg(a, defs, errs)),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => vld_arg(arg, defs, errs),
        IRExpr::ClosureApply { closure, args } => {
            vld_arg(closure, defs, errs);
            args.iter().for_each(|a| vld_arg(a, defs, errs));
        }
        IRExpr::UProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var)
        | IRExpr::SProj { var, .. } => vld_var(*var, defs, errs),
        IRExpr::Reuse { var, args, .. } => {
            vld_var(*var, defs, errs);
            args.iter().for_each(|a| vld_arg(a, defs, errs));
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}
fn vld_body(
    body: &IRBody,
    defs: &mut HashSet<VarId>,
    jp_ar: &mut HashMap<JoinPointId, usize>,
    jp_def: &mut HashSet<JoinPointId>,
    errs: &mut Vec<IrValidationError>,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            vld_expr(value, defs, errs);
            if !defs.insert(*var) {
                errs.push(IrValidationError::DuplicateDef(*var));
            }
            vld_body(rest, defs, jp_ar, jp_def, errs);
        }
        IRBody::JDecl {
            jp,
            params,
            body: jpb,
            rest,
        } => {
            if !jp_def.insert(*jp) {
                errs.push(IrValidationError::DuplicateJoinPoint(*jp));
            }
            jp_ar.insert(*jp, params.len());
            let mut scope = defs.clone();
            for (v, _) in params {
                if !scope.insert(*v) {
                    errs.push(IrValidationError::DuplicateDef(*v));
                }
            }
            vld_body(jpb, &mut scope, jp_ar, jp_def, errs);
            vld_body(rest, defs, jp_ar, jp_def, errs);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            vld_var(*var, defs, errs);
            vld_body(rest, defs, jp_ar, jp_def, errs);
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            vld_var(*var, defs, errs);
            vld_var(*value, defs, errs);
            vld_body(rest, defs, jp_ar, jp_def, errs);
        }
        IRBody::SetTag { var, rest, .. } => {
            vld_var(*var, defs, errs);
            vld_body(rest, defs, jp_ar, jp_def, errs);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            vld_var(*scrutinee, defs, errs);
            for alt in alts {
                vld_body(&alt.body, defs, jp_ar, jp_def, errs);
            }
            if let Some(d) = default {
                vld_body(d, defs, jp_ar, jp_def, errs);
            }
        }
        IRBody::Jmp { jp, args } => {
            if !jp_def.contains(jp) {
                errs.push(IrValidationError::UndefinedJoinPoint(*jp));
            }
            if let Some(&exp) = jp_ar.get(jp) {
                if args.len() != exp {
                    errs.push(IrValidationError::JoinPointArityMismatch {
                        jp: *jp,
                        expected: exp,
                        actual: args.len(),
                    });
                }
            }
            args.iter().for_each(|a| vld_arg(a, defs, errs));
        }
        IRBody::Ret(arg) => vld_arg(arg, defs, errs),
        IRBody::Unreachable => {}
    }
}

// ── Subexpression extraction ───────────────────────────────────────────────

/// An extracted function call site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub(crate) fn_id: FnId,
    pub(crate) num_args: usize,
    pub(crate) is_partial: bool,
}

/// Extract all function call sites from an IR body.
#[must_use]
pub(crate) fn extract_call_sites(body: &IRBody) -> Vec<CallSite> {
    let mut s = Vec::new();
    xc_body(body, &mut s);
    s
}

fn xc_body(body: &IRBody, s: &mut Vec<CallSite>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, args } = value {
                s.push(CallSite {
                    fn_id: fn_id.clone(),
                    num_args: args.len(),
                    is_partial: false,
                });
            } else if let IRExpr::PartialApply { fn_id, args, .. } = value {
                s.push(CallSite {
                    fn_id: fn_id.clone(),
                    num_args: args.len(),
                    is_partial: true,
                });
            }
            xc_body(rest, s);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            xc_body(jp, s);
            xc_body(rest, s);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => xc_body(rest, s),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                xc_body(&alt.body, s);
            }
            if let Some(d) = default {
                xc_body(d, s);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Extract all case scrutinee VarIds from an IR body.
#[must_use]
pub(crate) fn extract_case_scrutinees(body: &IRBody) -> Vec<VarId> {
    let mut r = Vec::new();
    xs_body(body, &mut r);
    r
}

fn xs_body(body: &IRBody, r: &mut Vec<VarId>) {
    match body {
        IRBody::Case {
            scrutinee,
            alts,
            default,
            ..
        } => {
            r.push(*scrutinee);
            for alt in alts {
                xs_body(&alt.body, r);
            }
            if let Some(d) = default {
                xs_body(d, r);
            }
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => xs_body(rest, r),
        IRBody::JDecl { body: jp, rest, .. } => {
            xs_body(jp, r);
            xs_body(rest, r);
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ── Pretty summary ─────────────────────────────────────────────────────────

/// Concise summary of an IR declaration.
#[derive(Debug, Clone)]
pub(crate) struct DeclSummary {
    pub(crate) name: String,
    pub(crate) num_params: usize,
    pub(crate) return_type: String,
    pub(crate) node_counts: NodeKindCounts,
    pub(crate) depth: usize,
}

impl fmt::Display for DeclSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "fn {}({} params) -> {} [nodes={}, depth={}, lets={}, cases={}, rc=+{}-{}]",
            self.name,
            self.num_params,
            self.return_type,
            self.node_counts.total(),
            self.depth,
            self.node_counts.vdecl,
            self.node_counts.case,
            self.node_counts.inc,
            self.node_counts.dec
        )
    }
}

/// Generate a concise summary of an IR declaration.
#[must_use]
pub(crate) fn decl_summary(decl: &IRDecl) -> DeclSummary {
    DeclSummary {
        name: decl.name.to_string(),
        num_params: decl.params.len(),
        return_type: format!("{:?}", decl.return_type),
        node_counts: node_kind_counts(&decl.body),
        depth: nesting_depth(&decl.body),
    }
}

/// Multi-line pretty summary for a slice of declarations.
#[must_use]
pub(crate) fn module_pretty_summary(decls: &[IRDecl]) -> String {
    let mut out = format!("IR Module: {} declaration(s)\n", decls.len());
    for decl in decls {
        out.push_str(&format!("  {}\n", decl_summary(decl)));
    }
    out
}
