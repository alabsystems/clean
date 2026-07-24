// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Borrow Inference Phase 2: field-sensitive borrowing, uniqueness,
//! last-use detection, conflict analysis, join point propagation, and
//! inter-procedural borrow summaries with conservative fallback.
//!
//! Part of #3083 - Extensibility epic.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use std::collections::{HashMap, HashSet};

/// Borrow classification for a function parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) enum BorrowClass {
    Borrowed,
    Owned,
    #[default]
    Unknown,
}

/// Why a value escapes its function scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum EscapeKind {
    ReturnValue,
    StoredInCtor,
    PassedToExtern,
    CapturedByClosure,
    MutablyModified,
}

/// A field-level borrow: which field of which variable is accessed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FieldBorrow {
    pub(crate) var: VarId,
    pub(crate) field_idx: u32,
}

/// A detected borrow conflict: mutable use of a variable that is also borrowed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BorrowConflict {
    pub(crate) var: VarId,
    pub(crate) mutable_use: &'static str,
}

/// Per-function borrow summary for inter-procedural analysis.
#[derive(Clone, Debug)]
pub(crate) struct BorrowSummary {
    pub(crate) fn_id: FnId,
    pub(crate) param_classes: Vec<BorrowClass>,
    pub(crate) escapes: Vec<(VarId, EscapeKind)>,
    pub(crate) conflicts: Vec<BorrowConflict>,
}

/// Statistics from the extended borrow analysis.
#[derive(Clone, Debug, Default)]
pub(crate) struct BorrowExtStats {
    pub(crate) params_classified: usize,
    pub(crate) escapes_detected: usize,
    pub(crate) last_uses_found: usize,
    pub(crate) conflicts_found: usize,
    pub(crate) fields_tracked: usize,
    pub(crate) join_points_analyzed: usize,
}

/// Configuration for extended borrow analysis.
#[derive(Clone, Debug)]
pub(crate) struct BorrowExt2Config {
    pub(crate) max_iterations: usize,
    pub(crate) enable_field_sensitive: bool,
    pub(crate) enable_uniqueness: bool,
    pub(crate) enable_last_use: bool,
    pub(crate) enable_conflict_detection: bool,
    pub(crate) conservative_extern: bool,
}

impl Default for BorrowExt2Config {
    fn default() -> Self {
        Self {
            max_iterations: 20,
            enable_field_sensitive: true,
            enable_uniqueness: true,
            enable_last_use: true,
            enable_conflict_detection: true,
            conservative_extern: true,
        }
    }
}

/// Result of the extended borrow analysis.
#[derive(Clone, Debug)]
pub(crate) struct BorrowExt2Result {
    pub(crate) summaries: HashMap<FnId, BorrowSummary>,
    pub(crate) last_uses: HashMap<FnId, HashMap<VarId, u32>>,
    pub(crate) unique_vars: HashMap<FnId, HashSet<VarId>>,
    pub(crate) field_borrows: HashMap<FnId, HashSet<FieldBorrow>>,
    pub(crate) stats: BorrowExtStats,
}

/// Run extended borrow analysis on a set of IR declarations.
pub(crate) fn analyze_borrows_ext2(
    decls: &[IRDecl],
    config: &BorrowExt2Config,
) -> BorrowExt2Result {
    let mut stats = BorrowExtStats::default();
    let mut summaries: HashMap<FnId, BorrowSummary> = HashMap::new();
    let mut last_uses: HashMap<FnId, HashMap<VarId, u32>> = HashMap::new();
    let mut unique_vars: HashMap<FnId, HashSet<VarId>> = HashMap::new();
    let mut field_borrows: HashMap<FnId, HashSet<FieldBorrow>> = HashMap::new();

    for decl in decls {
        let fn_id = FnId(decl.name.clone());
        let params: Vec<VarId> = decl.params.iter().map(|(v, _)| *v).collect();
        let escapes = collect_escapes_ext2(&decl.body, &params);
        stats.escapes_detected += escapes.len();
        if config.enable_last_use {
            let lu = detect_last_uses(&decl.body);
            stats.last_uses_found += lu.len();
            last_uses.insert(fn_id.clone(), lu);
        }
        if config.enable_uniqueness {
            unique_vars.insert(fn_id.clone(), analyze_uniqueness(&decl.body, &params));
        }
        if config.enable_field_sensitive {
            let fb = collect_field_borrows(&decl.body);
            stats.fields_tracked += fb.len();
            field_borrows.insert(fn_id.clone(), fb);
        }
        stats.join_points_analyzed += count_join_points(&decl.body);
        let conflicts = if config.enable_conflict_detection {
            let c = detect_conflicts(&decl.body, &params);
            stats.conflicts_found += c.len();
            c
        } else {
            Vec::new()
        };
        let param_classes = classify_params(decl, &escapes);
        stats.params_classified += param_classes.len();
        summaries.insert(
            fn_id.clone(),
            BorrowSummary {
                fn_id,
                param_classes,
                escapes,
                conflicts,
            },
        );
    }

    // Inter-procedural fixpoint propagation
    for iteration in 0..config.max_iterations {
        if !propagate_inter_procedural(decls, &mut summaries, config.conservative_extern) {
            break;
        }
        if iteration + 1 >= config.max_iterations {
            break;
        }
    }

    // Resolve Unknown -> conservative fallback (Owned)
    for summary in summaries.values_mut() {
        for class in &mut summary.param_classes {
            if *class == BorrowClass::Unknown {
                *class = BorrowClass::Owned;
            }
        }
    }
    BorrowExt2Result {
        summaries,
        last_uses,
        unique_vars,
        field_borrows,
        stats,
    }
}

/// Convenience: analyze with default config.
pub(crate) fn analyze_borrows_ext2_default(decls: &[IRDecl]) -> BorrowExt2Result {
    analyze_borrows_ext2(decls, &BorrowExt2Config::default())
}

// -- Escape analysis --

fn collect_escapes_ext2(body: &IRBody, params: &[VarId]) -> Vec<(VarId, EscapeKind)> {
    let mut out = Vec::new();
    walk_escapes(body, params, &mut out);
    out
}

fn push_esc(v: VarId, k: EscapeKind, params: &[VarId], o: &mut Vec<(VarId, EscapeKind)>) {
    if params.contains(&v) {
        o.push((v, k));
    }
}

fn push_esc_args(args: &[IRArg], k: EscapeKind, p: &[VarId], o: &mut Vec<(VarId, EscapeKind)>) {
    for a in args {
        if let IRArg::Var(v) = a {
            push_esc(*v, k.clone(), p, o);
        }
    }
}

fn walk_escapes(body: &IRBody, p: &[VarId], o: &mut Vec<(VarId, EscapeKind)>) {
    match body {
        IRBody::Ret(IRArg::Var(v)) => push_esc(*v, EscapeKind::ReturnValue, p, o),
        IRBody::Ret(IRArg::Erased) | IRBody::Unreachable => {}
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { args, .. } | IRExpr::Reuse { args, .. } => {
                    push_esc_args(args, EscapeKind::StoredInCtor, p, o)
                }
                IRExpr::PartialApply { args, .. } => {
                    push_esc_args(args, EscapeKind::CapturedByClosure, p, o)
                }
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        push_esc(*v, EscapeKind::PassedToExtern, p, o);
                    }
                    push_esc_args(args, EscapeKind::PassedToExtern, p, o);
                }
                IRExpr::Apply { args, .. } => push_esc_args(args, EscapeKind::PassedToExtern, p, o),
                IRExpr::Box {
                    arg: IRArg::Var(v), ..
                } => {
                    push_esc(*v, EscapeKind::StoredInCtor, p, o);
                }
                IRExpr::Reset(v) => push_esc(*v, EscapeKind::MutablyModified, p, o),
                _ => {}
            }
            walk_escapes(rest, p, o);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            push_esc(*var, EscapeKind::MutablyModified, p, o);
            push_esc(*value, EscapeKind::StoredInCtor, p, o);
            walk_escapes(rest, p, o);
        }
        IRBody::SetTag { var, rest, .. } => {
            push_esc(*var, EscapeKind::MutablyModified, p, o);
            walk_escapes(rest, p, o);
        }
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            push_esc(*var, EscapeKind::MutablyModified, p, o);
            push_esc(*value, EscapeKind::StoredInCtor, p, o);
            walk_escapes(rest, p, o);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => walk_escapes(rest, p, o),
        IRBody::JDecl { body: jb, rest, .. } => {
            walk_escapes(jb, p, o);
            walk_escapes(rest, p, o);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                walk_escapes(&alt.body, p, o);
            }
            if let Some(def) = default {
                walk_escapes(def, p, o);
            }
        }
        IRBody::Jmp { args, .. } => push_esc_args(args, EscapeKind::PassedToExtern, p, o),
    }
}

// -- Last-use detection --

/// Detect the last use position (depth) of each VarId in a body.
pub(crate) fn detect_last_uses(body: &IRBody) -> HashMap<VarId, u32> {
    let mut uses = HashMap::new();
    walk_last_uses(body, 0, &mut uses);
    uses
}

fn rec_use(v: VarId, d: u32, u: &mut HashMap<VarId, u32>) {
    let e = u.entry(v).or_insert(0);
    if d > *e {
        *e = d;
    }
}

fn rec_args(args: &[IRArg], d: u32, u: &mut HashMap<VarId, u32>) {
    for a in args {
        if let IRArg::Var(v) = a {
            rec_use(*v, d, u);
        }
    }
}

fn walk_last_uses(body: &IRBody, d: u32, u: &mut HashMap<VarId, u32>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { args, .. }
                | IRExpr::Reuse { args, .. }
                | IRExpr::Apply { args, .. }
                | IRExpr::PartialApply { args, .. } => rec_args(args, d, u),
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        rec_use(*v, d, u);
                    }
                    rec_args(args, d, u);
                }
                IRExpr::Proj { arg, .. }
                | IRExpr::Box { arg, .. }
                | IRExpr::Tag(arg)
                | IRExpr::Unbox { arg, .. } => {
                    if let IRArg::Var(v) = arg {
                        rec_use(*v, d, u);
                    }
                }
                IRExpr::UProj { var, .. }
                | IRExpr::SProj { var, .. }
                | IRExpr::IsShared(var)
                | IRExpr::Reset(var) => rec_use(*var, d, u),
                IRExpr::Lit(_) | IRExpr::String(_) => {}
            }
            walk_last_uses(rest, d + 1, u);
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
            rec_use(*var, d, u);
            rec_use(*value, d, u);
            walk_last_uses(rest, d + 1, u);
        }
        IRBody::SetTag { var, rest, .. } => {
            rec_use(*var, d, u);
            walk_last_uses(rest, d + 1, u);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            rec_use(*var, d, u);
            walk_last_uses(rest, d + 1, u);
        }
        IRBody::JDecl { body: jb, rest, .. } => {
            walk_last_uses(jb, d + 1, u);
            walk_last_uses(rest, d + 1, u);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            rec_use(*scrutinee, d, u);
            for alt in alts {
                walk_last_uses(&alt.body, d + 1, u);
            }
            if let Some(def) = default {
                walk_last_uses(def, d + 1, u);
            }
        }
        IRBody::Jmp { args, .. } => rec_args(args, d, u),
        IRBody::Ret(arg) => {
            if let IRArg::Var(v) = arg {
                rec_use(*v, d, u);
            }
        }
        IRBody::Unreachable => {}
    }
}

// -- Uniqueness analysis --

/// Identify parameters guaranteed unique (never passed to IsShared).
pub(crate) fn analyze_uniqueness(body: &IRBody, params: &[VarId]) -> HashSet<VarId> {
    let mut shared = HashSet::new();
    collect_shared_checks(body, &mut shared);
    params
        .iter()
        .filter(|v| !shared.contains(v))
        .copied()
        .collect()
}

fn collect_shared_checks(body: &IRBody, s: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::IsShared(v) = value {
                s.insert(*v);
            }
            collect_shared_checks(rest, s);
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => collect_shared_checks(rest, s),
        IRBody::JDecl { body: jb, rest, .. } => {
            collect_shared_checks(jb, s);
            collect_shared_checks(rest, s);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_shared_checks(&alt.body, s);
            }
            if let Some(def) = default {
                collect_shared_checks(def, s);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// -- Field-sensitive borrowing --

/// Collect field-level borrows: projections that access individual fields.
pub(crate) fn collect_field_borrows(body: &IRBody) -> HashSet<FieldBorrow> {
    let mut out = HashSet::new();
    walk_field_borrows(body, &mut out);
    out
}

fn walk_field_borrows(body: &IRBody, out: &mut HashSet<FieldBorrow>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Proj {
                idx,
                arg: IRArg::Var(v),
                ..
            } = value
            {
                out.insert(FieldBorrow {
                    var: *v,
                    field_idx: *idx,
                });
            }
            walk_field_borrows(rest, out);
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => walk_field_borrows(rest, out),
        IRBody::JDecl { body: jb, rest, .. } => {
            walk_field_borrows(jb, out);
            walk_field_borrows(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                walk_field_borrows(&alt.body, out);
            }
            if let Some(def) = default {
                walk_field_borrows(def, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// -- Join point counting --

fn count_join_points(body: &IRBody) -> usize {
    match body {
        IRBody::JDecl { body: jb, rest, .. } => 1 + count_join_points(jb) + count_join_points(rest),
        IRBody::VDecl { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => count_join_points(rest),
        IRBody::Case { alts, default, .. } => {
            alts.iter()
                .map(|a| count_join_points(&a.body))
                .sum::<usize>()
                + default.as_ref().map_or(0, |d| count_join_points(d))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 0,
    }
}

// -- Conflict detection --

/// Detect borrow conflicts: a param mutably used (Set/USet/SSet/Reset).
pub(crate) fn detect_conflicts(body: &IRBody, params: &[VarId]) -> Vec<BorrowConflict> {
    let mut mutated = HashSet::new();
    collect_mutated(body, &mut mutated);
    let param_set: HashSet<VarId> = params.iter().copied().collect();
    mutated
        .intersection(&param_set)
        .map(|v| BorrowConflict {
            var: *v,
            mutable_use: "Set/USet/SSet/Reset",
        })
        .collect()
}

fn collect_mutated(body: &IRBody, m: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Reset(v) = value {
                m.insert(*v);
            }
            collect_mutated(rest, m);
        }
        IRBody::Set { var, rest, .. }
        | IRBody::SetTag { var, rest, .. }
        | IRBody::USet { var, rest, .. }
        | IRBody::SSet { var, rest, .. } => {
            m.insert(*var);
            collect_mutated(rest, m);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => collect_mutated(rest, m),
        IRBody::JDecl { body: jb, rest, .. } => {
            collect_mutated(jb, m);
            collect_mutated(rest, m);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_mutated(&alt.body, m);
            }
            if let Some(def) = default {
                collect_mutated(def, m);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// -- Parameter classification --

fn classify_params(decl: &IRDecl, escapes: &[(VarId, EscapeKind)]) -> Vec<BorrowClass> {
    let escaped: HashSet<VarId> = escapes.iter().map(|(v, _)| *v).collect();
    decl.params
        .iter()
        .map(|(var, ty)| {
            if ty.is_scalar()
                || ty.is_void()
                || matches!(ty, IRType::Erased)
                || escaped.contains(var)
            {
                BorrowClass::Owned
            } else {
                BorrowClass::Unknown
            }
        })
        .collect()
}

// -- Inter-procedural propagation --

fn propagate_inter_procedural(
    decls: &[IRDecl],
    summaries: &mut HashMap<FnId, BorrowSummary>,
    conservative_extern: bool,
) -> bool {
    let mut changed = false;
    let param_maps: Vec<(FnId, HashMap<VarId, usize>)> = decls
        .iter()
        .map(|d| {
            let map: HashMap<VarId, usize> = d
                .params
                .iter()
                .enumerate()
                .map(|(i, (v, _))| (*v, i))
                .collect();
            (FnId(d.name.clone()), map)
        })
        .collect();
    for (idx, decl) in decls.iter().enumerate() {
        let (ref cfn, ref pm) = param_maps[idx];
        prop_body(
            &decl.body,
            cfn,
            pm,
            summaries,
            conservative_extern,
            &mut changed,
        );
    }
    changed
}

fn prop_body(
    body: &IRBody,
    cfn: &FnId,
    pm: &HashMap<VarId, usize>,
    sm: &mut HashMap<FnId, BorrowSummary>,
    ce: bool,
    ch: &mut bool,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply {
                fn_id: callee,
                args,
            } = value
            {
                let cc: Option<Vec<BorrowClass>> = sm.get(callee).map(|s| s.param_classes.clone());
                if let Some(classes) = cc {
                    for (i, a) in args.iter().enumerate() {
                        if let IRArg::Var(v) = a {
                            if i < classes.len() && classes[i] == BorrowClass::Owned {
                                if let Some(pi) = pm.get(v) {
                                    mark_own(sm, cfn, *pi, ch);
                                }
                            }
                        }
                    }
                } else if ce {
                    for a in args {
                        if let IRArg::Var(v) = a {
                            if let Some(pi) = pm.get(v) {
                                mark_own(sm, cfn, *pi, ch);
                            }
                        }
                    }
                }
            }
            prop_body(rest, cfn, pm, sm, ce, ch);
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => prop_body(rest, cfn, pm, sm, ce, ch),
        IRBody::JDecl { body: jb, rest, .. } => {
            prop_body(jb, cfn, pm, sm, ce, ch);
            prop_body(rest, cfn, pm, sm, ce, ch);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                prop_body(&alt.body, cfn, pm, sm, ce, ch);
            }
            if let Some(def) = default {
                prop_body(def, cfn, pm, sm, ce, ch);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn mark_own(sm: &mut HashMap<FnId, BorrowSummary>, fid: &FnId, i: usize, ch: &mut bool) {
    if let Some(s) = sm.get_mut(fid) {
        if i < s.param_classes.len() && s.param_classes[i] != BorrowClass::Owned {
            s.param_classes[i] = BorrowClass::Owned;
            *ch = true;
        }
    }
}

#[cfg(test)]
#[path = "borrow_infer_ext2_tests.rs"]
mod tests;
