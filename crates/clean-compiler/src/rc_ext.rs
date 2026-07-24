// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Reference Counting Optimization for L5IR
//!
//! Post-insertion optimizations: elision, borrowed-param, last-use, sinking,
//! combining, and immutable bean counting (Ullrich/de Moura IFL 2020).
//! Runs after `rc::insert` places conservative inc/dec, before codegen.
//!
//! Part of #3083 - Compiler extensibility.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, VarId};
use std::collections::{HashMap, HashSet};

/// Configuration for extended RC optimization.
#[derive(Clone, Debug)]
pub(crate) struct RcExtConfig {
    pub(crate) elision: bool,
    pub(crate) borrowed_opt: bool,
    pub(crate) last_use: bool,
    pub(crate) sinking: bool,
    pub(crate) combining: bool,
    pub(crate) immutable_beans: bool,
}

impl Default for RcExtConfig {
    fn default() -> Self {
        Self {
            elision: true,
            borrowed_opt: true,
            last_use: true,
            sinking: true,
            combining: true,
            immutable_beans: true,
        }
    }
}

/// Statistics from an RC optimization pass.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RcExtStats {
    pub(crate) incs_eliminated: usize,
    pub(crate) decs_eliminated: usize,
    pub(crate) incs_remaining: usize,
    pub(crate) decs_remaining: usize,
    pub(crate) incs_combined: usize,
    pub(crate) decs_sunk: usize,
    pub(crate) borrowed_skipped: usize,
    pub(crate) last_use_skipped: usize,
    pub(crate) bean_elisions: usize,
}

/// Run extended RC optimization on a single declaration.
#[must_use]
pub(crate) fn optimize_rc_ext(decl: &IRDecl, config: &RcExtConfig) -> (IRDecl, RcExtStats) {
    let mut stats = RcExtStats::default();
    let borrowed = if config.borrowed_opt {
        find_borrowed_params(decl)
    } else {
        HashSet::new()
    };
    let last_uses = if config.last_use {
        find_last_uses(&decl.body)
    } else {
        HashMap::new()
    };
    let unique = if config.immutable_beans {
        find_unique_owned(&decl.body)
    } else {
        HashSet::new()
    };

    let body = opt_body(
        &decl.body, config, &borrowed, &last_uses, &unique, &mut stats,
    );
    count_rc_ops(&body, &mut stats);

    let optimized = IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body,
    };
    (optimized, stats)
}

/// Run extended RC optimization with default config.
#[must_use]
pub(crate) fn optimize_rc_ext_default(decl: &IRDecl) -> (IRDecl, RcExtStats) {
    optimize_rc_ext(decl, &RcExtConfig::default())
}

/// Net RC delta per variable. Positive = net inc, negative = net dec.
#[must_use]
pub(crate) fn validate_rc_balance(body: &IRBody) -> HashMap<VarId, i64> {
    let mut balance: HashMap<VarId, i64> = HashMap::new();
    walk_rc_balance(body, &mut balance);
    balance
}

/// True if no variable has negative RC balance (more decs than incs).
#[must_use]
pub(crate) fn is_rc_balanced(body: &IRBody) -> bool {
    validate_rc_balance(body).values().all(|&d| d >= 0)
}

// ---- Borrowed-parameter analysis ----

fn find_borrowed_params(decl: &IRDecl) -> HashSet<VarId> {
    let params: HashSet<VarId> = decl
        .params
        .iter()
        .filter(|(_, ty)| ty.is_object())
        .map(|(v, _)| *v)
        .collect();
    let mut consumed = HashSet::new();
    walk_consumed(&decl.body, &mut consumed);
    params.difference(&consumed).copied().collect()
}

fn walk_consumed(body: &IRBody, out: &mut HashSet<VarId>) {
    match body {
        IRBody::Ret(IRArg::Var(v)) => {
            out.insert(*v);
        }
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Ctor { args, .. }
                | IRExpr::Reuse { args, .. }
                | IRExpr::Apply { args, .. }
                | IRExpr::PartialApply { args, .. } => push_vars(args, out),
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        out.insert(*v);
                    }
                    push_vars(args, out);
                }
                IRExpr::Box {
                    arg: IRArg::Var(v), ..
                } => {
                    out.insert(*v);
                }
                IRExpr::Reset(v) => {
                    out.insert(*v);
                }
                _ => {}
            }
            walk_consumed(rest, out);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            out.insert(*var);
            out.insert(*value);
            walk_consumed(rest, out);
        }
        IRBody::SetTag { var, rest, .. } => {
            out.insert(*var);
            walk_consumed(rest, out);
        }
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            out.insert(*var);
            out.insert(*value);
            walk_consumed(rest, out);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => walk_consumed(rest, out),
        IRBody::JDecl { body, rest, .. } => {
            walk_consumed(body, out);
            walk_consumed(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                walk_consumed(&a.body, out);
            }
            if let Some(d) = default {
                walk_consumed(d, out);
            }
        }
        IRBody::Jmp { args, .. } => push_vars(args, out),
        _ => {}
    }
}

fn push_vars(args: &[IRArg], set: &mut HashSet<VarId>) {
    for a in args {
        if let IRArg::Var(v) = a {
            set.insert(*v);
        }
    }
}

// ---- Last-use analysis ----

fn find_last_uses(body: &IRBody) -> HashMap<VarId, bool> {
    let mut uses = HashMap::new();
    walk_last_uses(body, &mut uses);
    uses
}

fn walk_last_uses(body: &IRBody, uses: &mut HashMap<VarId, bool>) {
    match body {
        IRBody::Ret(IRArg::Var(v)) => {
            uses.entry(*v).or_insert(true);
        }
        IRBody::VDecl { value, rest, .. } => {
            walk_last_uses(rest, uses);
            match value {
                IRExpr::Ctor { args, .. }
                | IRExpr::Reuse { args, .. }
                | IRExpr::Apply { args, .. } => {
                    for a in args {
                        if let IRArg::Var(v) = a {
                            uses.entry(*v).or_insert(true);
                        }
                    }
                }
                IRExpr::Proj {
                    arg: IRArg::Var(v), ..
                } => {
                    uses.entry(*v).or_insert(false);
                }
                IRExpr::Tag(IRArg::Var(v)) | IRExpr::IsShared(v) => {
                    uses.entry(*v).or_insert(false);
                }
                _ => {}
            }
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            walk_last_uses(rest, uses);
            uses.entry(*var).or_insert(true);
            uses.entry(*value).or_insert(true);
        }
        IRBody::SetTag { var, rest, .. } => {
            walk_last_uses(rest, uses);
            uses.entry(*var).or_insert(true);
        }
        IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            walk_last_uses(rest, uses);
            uses.entry(*var).or_insert(true);
            uses.entry(*value).or_insert(true);
        }
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => walk_last_uses(rest, uses),
        IRBody::JDecl { body, rest, .. } => {
            walk_last_uses(rest, uses);
            walk_last_uses(body, uses);
        }
        IRBody::Case { alts, default, .. } => {
            if let Some(d) = default {
                walk_last_uses(d, uses);
            }
            for a in alts {
                walk_last_uses(&a.body, uses);
            }
        }
        IRBody::Jmp { args, .. } => {
            for a in args {
                if let IRArg::Var(v) = a {
                    uses.entry(*v).or_insert(true);
                }
            }
        }
        _ => {}
    }
}

// ---- Unique-ownership (immutable bean counting) ----

fn find_unique_owned(body: &IRBody) -> HashSet<VarId> {
    let mut unique = HashSet::new();
    let mut shared = HashSet::new();
    walk_unique(body, &mut unique, &mut shared);
    unique.difference(&shared).copied().collect()
}

fn walk_unique(body: &IRBody, unique: &mut HashSet<VarId>, shared: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            match value {
                IRExpr::Ctor { .. } | IRExpr::Lit(_) | IRExpr::String(_) => {
                    unique.insert(*var);
                }
                IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => {
                    for a in args {
                        if let IRArg::Var(v) = a {
                            shared.insert(*v);
                        }
                    }
                }
                IRExpr::ClosureApply { closure, args } => {
                    if let IRArg::Var(v) = closure {
                        shared.insert(*v);
                    }
                    for a in args {
                        if let IRArg::Var(v) = a {
                            shared.insert(*v);
                        }
                    }
                }
                _ => {}
            }
            walk_unique(rest, unique, shared);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            shared.insert(*var);
            shared.insert(*value);
            walk_unique(rest, unique, shared);
        }
        IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. } => walk_unique(rest, unique, shared),
        IRBody::JDecl { body, rest, .. } => {
            walk_unique(body, unique, shared);
            walk_unique(rest, unique, shared);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                walk_unique(&a.body, unique, shared);
            }
            if let Some(d) = default {
                walk_unique(d, unique, shared);
            }
        }
        IRBody::Ret(IRArg::Var(v)) => {
            shared.insert(*v);
        }
        IRBody::Jmp { args, .. } => {
            for a in args {
                if let IRArg::Var(v) = a {
                    shared.insert(*v);
                }
            }
        }
        _ => {}
    }
}

// ---- Core optimization ----

fn opt_body(
    body: &IRBody,
    cfg: &RcExtConfig,
    borrowed: &HashSet<VarId>,
    last_uses: &HashMap<VarId, bool>,
    unique: &HashSet<VarId>,
    stats: &mut RcExtStats,
) -> IRBody {
    let recurse = |b: &IRBody, s: &mut RcExtStats| opt_body(b, cfg, borrowed, last_uses, unique, s);
    match body {
        IRBody::Inc { var, n, rest } => {
            if cfg.elision {
                if let IRBody::Dec { var: dv, rest: dr } = rest.as_ref() {
                    if *dv == *var && *n == 1 {
                        stats.incs_eliminated += 1;
                        stats.decs_eliminated += 1;
                        return recurse(dr, stats);
                    }
                }
            }
            let rest_opt = recurse(rest, stats);
            if cfg.combining {
                if let IRBody::Inc {
                    var: v2,
                    n: n2,
                    rest: r2,
                } = &rest_opt
                {
                    if *v2 == *var {
                        stats.incs_combined += 1;
                        return IRBody::Inc {
                            var: *var,
                            n: n + n2,
                            rest: r2.clone(),
                        };
                    }
                }
            }
            if cfg.borrowed_opt && borrowed.contains(var) {
                stats.borrowed_skipped += 1;
                stats.incs_eliminated += 1;
                return rest_opt;
            }
            if cfg.immutable_beans && unique.contains(var) {
                stats.bean_elisions += 1;
                stats.incs_eliminated += 1;
                return rest_opt;
            }
            IRBody::Inc {
                var: *var,
                n: *n,
                rest: Box::new(rest_opt),
            }
        }
        IRBody::Dec { var, rest } => {
            let rest_opt = recurse(rest, stats);
            if cfg.borrowed_opt && borrowed.contains(var) {
                stats.borrowed_skipped += 1;
                stats.decs_eliminated += 1;
                return rest_opt;
            }
            if cfg.last_use {
                if let Some(true) = last_uses.get(var) {
                    stats.last_use_skipped += 1;
                    stats.decs_eliminated += 1;
                    return rest_opt;
                }
            }
            if cfg.immutable_beans && unique.contains(var) {
                stats.bean_elisions += 1;
                stats.decs_eliminated += 1;
                return rest_opt;
            }
            if cfg.sinking && !uses_var_next(&rest_opt, *var) {
                stats.decs_sunk += 1;
            }
            IRBody::Dec {
                var: *var,
                rest: Box::new(rest_opt),
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
            rest: Box::new(recurse(rest, stats)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: jb,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(recurse(jb, stats)),
            rest: Box::new(recurse(rest, stats)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let ao: Vec<_> = alts
                .iter()
                .map(|a| crate::ir::IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(recurse(&a.body, stats)),
                })
                .collect();
            let d = default.as_ref().map(|d| Box::new(recurse(d, stats)));
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: ao,
                default: d,
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
            rest: Box::new(recurse(rest, stats)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(recurse(rest, stats)),
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
            rest: Box::new(recurse(rest, stats)),
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
            rest: Box::new(recurse(rest, stats)),
        },
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => body.clone(),
    }
}

fn uses_var_next(body: &IRBody, target: VarId) -> bool {
    match body {
        IRBody::VDecl { value, .. } => expr_uses(value, target),
        IRBody::Ret(IRArg::Var(v)) => *v == target,
        IRBody::Inc { var, .. } | IRBody::Dec { var, .. } => *var == target,
        IRBody::Set { var, value, .. } => *var == target || *value == target,
        IRBody::Case { scrutinee, .. } => *scrutinee == target,
        _ => false,
    }
}

fn expr_uses(expr: &IRExpr, t: VarId) -> bool {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. }
        | IRExpr::Reuse { args, .. } => args.iter().any(|a| matches!(a, IRArg::Var(v) if *v == t)),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => matches!(arg, IRArg::Var(v) if *v == t),
        IRExpr::ClosureApply { closure, args } => {
            matches!(closure, IRArg::Var(v) if *v == t)
                || args.iter().any(|a| matches!(a, IRArg::Var(v) if *v == t))
        }
        IRExpr::IsShared(v)
        | IRExpr::Reset(v)
        | IRExpr::UProj { var: v, .. }
        | IRExpr::SProj { var: v, .. } => *v == t,
        IRExpr::Lit(_) | IRExpr::String(_) => false,
    }
}

// ---- RC counting and validation ----

fn count_rc_ops(body: &IRBody, stats: &mut RcExtStats) {
    match body {
        IRBody::Inc { rest, .. } => {
            stats.incs_remaining += 1;
            count_rc_ops(rest, stats);
        }
        IRBody::Dec { rest, .. } => {
            stats.decs_remaining += 1;
            count_rc_ops(rest, stats);
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => count_rc_ops(rest, stats),
        IRBody::JDecl { body, rest, .. } => {
            count_rc_ops(body, stats);
            count_rc_ops(rest, stats);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                count_rc_ops(&a.body, stats);
            }
            if let Some(d) = default {
                count_rc_ops(d, stats);
            }
        }
        _ => {}
    }
}

fn walk_rc_balance(body: &IRBody, bal: &mut HashMap<VarId, i64>) {
    match body {
        IRBody::Inc { var, n, rest } => {
            *bal.entry(*var).or_insert(0) += i64::from(*n);
            walk_rc_balance(rest, bal);
        }
        IRBody::Dec { var, rest } => {
            *bal.entry(*var).or_insert(0) -= 1;
            walk_rc_balance(rest, bal);
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => walk_rc_balance(rest, bal),
        IRBody::JDecl { body, rest, .. } => {
            walk_rc_balance(body, bal);
            walk_rc_balance(rest, bal);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                walk_rc_balance(&a.body, bal);
            }
            if let Some(d) = default {
                walk_rc_balance(d, bal);
            }
        }
        _ => {}
    }
}
