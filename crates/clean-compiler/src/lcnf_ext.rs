// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended LCNF analysis: statistics, depth, size, free variables,
//! pretty summary, and complexity measurement.
//!
//! Substitution, alpha-equivalence, and validation live in `lcnf_ext2`.
//!
//! Part of #3082 — LCNF extensibility.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, LetValue};
use clean_kernel::FVarId;
use std::collections::BTreeSet;

// ════════════════════════════════════════════════════════════════════════════
// Statistics
// ════════════════════════════════════════════════════════════════════════════

/// Counts of each LCNF code construct.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LcnfStats {
    pub(crate) let_bindings: usize,
    pub(crate) fun_decls: usize,
    pub(crate) join_points: usize,
    pub(crate) cases: usize,
    pub(crate) alts: usize,
    pub(crate) jmps: usize,
    pub(crate) returns: usize,
    pub(crate) unreachables: usize,
}

impl LcnfStats {
    /// Total number of AST nodes.
    #[must_use]
    pub(crate) fn total_nodes(&self) -> usize {
        self.let_bindings
            + self.fun_decls
            + self.join_points
            + self.cases
            + self.jmps
            + self.returns
            + self.unreachables
    }
}

/// Collect statistics from a `Code` tree.
#[must_use]
pub(crate) fn code_stats(code: &Code) -> LcnfStats {
    let mut stats = LcnfStats::default();
    collect_stats(code, &mut stats);
    stats
}

fn collect_stats(code: &Code, stats: &mut LcnfStats) {
    match code {
        Code::Let(_, body) => {
            stats.let_bindings += 1;
            collect_stats(body, stats);
        }
        Code::Fun(decl, body) => {
            stats.fun_decls += 1;
            collect_stats(&decl.body, stats);
            collect_stats(body, stats);
        }
        Code::JoinPoint(decl, body) => {
            stats.join_points += 1;
            collect_stats(&decl.body, stats);
            collect_stats(body, stats);
        }
        Code::Cases(cases) => {
            stats.cases += 1;
            for alt in &cases.alts {
                stats.alts += 1;
                collect_stats(alt.body(), stats);
            }
        }
        Code::Jmp { .. } => stats.jmps += 1,
        Code::Return(_) => stats.returns += 1,
        Code::Unreachable(_) => stats.unreachables += 1,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Nesting depth and size
// ════════════════════════════════════════════════════════════════════════════

/// Maximum nesting depth of a `Code` tree.
///
/// Terminals (Return, Jmp, Unreachable) have depth 1. Each wrapper adds 1.
#[must_use]
pub(crate) fn code_depth(code: &Code) -> usize {
    match code {
        Code::Let(_, body) => 1 + code_depth(body),
        Code::Fun(decl, body) => 1 + code_depth(&decl.body).max(code_depth(body)),
        Code::JoinPoint(decl, body) => 1 + code_depth(&decl.body).max(code_depth(body)),
        Code::Cases(cases) => {
            let inner = cases
                .alts
                .iter()
                .map(|a| code_depth(a.body()))
                .max()
                .unwrap_or(0);
            1 + inner
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 1,
    }
}

/// Total number of nodes in the `Code` tree (including all sub-trees).
#[must_use]
pub(crate) fn code_size(code: &Code) -> usize {
    match code {
        Code::Let(_, body) => 1 + code_size(body),
        Code::Fun(decl, body) => 1 + code_size(&decl.body) + code_size(body),
        Code::JoinPoint(decl, body) => 1 + code_size(&decl.body) + code_size(body),
        Code::Cases(cases) => {
            1 + cases
                .alts
                .iter()
                .map(|a| code_size(a.body()))
                .sum::<usize>()
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => 1,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Free variable collection
// ════════════════════════════════════════════════════════════════════════════

/// Collect all free variables referenced in a `Code` tree.
///
/// A variable is "free" if it appears in a use position (Arg::FVar, Return,
/// scrutinee, projection, etc.) but is not bound by a Let, Fun, JoinPoint,
/// or case-alt parameter within this tree.
#[must_use]
pub(crate) fn free_vars(code: &Code) -> BTreeSet<FVarId> {
    let mut free = BTreeSet::new();
    let mut bound = BTreeSet::new();
    collect_free_vars(code, &mut bound, &mut free);
    free
}

fn collect_free_vars(code: &Code, bound: &mut BTreeSet<FVarId>, free: &mut BTreeSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            collect_let_value_free(&decl.value, bound, free);
            bound.insert(decl.fvar_id);
            collect_free_vars(body, bound, free);
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            let mut inner_bound = bound.clone();
            inner_bound.insert(decl.fvar_id);
            for p in &decl.params {
                inner_bound.insert(p.fvar_id);
            }
            collect_free_vars(&decl.body, &mut inner_bound, free);
            bound.insert(decl.fvar_id);
            collect_free_vars(body, bound, free);
        }
        Code::Cases(cases) => {
            if !bound.contains(&cases.scrutinee) {
                free.insert(cases.scrutinee);
            }
            for alt in &cases.alts {
                let mut alt_bound = bound.clone();
                if let Alt::Ctor { params, .. } = alt {
                    for p in params {
                        alt_bound.insert(p.fvar_id);
                    }
                }
                collect_free_vars(alt.body(), &mut alt_bound, free);
            }
        }
        Code::Jmp { jp, args } => {
            if !bound.contains(jp) {
                free.insert(*jp);
            }
            for arg in args {
                collect_arg_free(arg, bound, free);
            }
        }
        Code::Return(fvar) => {
            if !bound.contains(fvar) {
                free.insert(*fvar);
            }
        }
        Code::Unreachable(_) => {}
    }
}

fn collect_let_value_free(val: &LetValue, bound: &BTreeSet<FVarId>, free: &mut BTreeSet<FVarId>) {
    match val {
        LetValue::Proj { structure, .. } => {
            if !bound.contains(structure) {
                free.insert(*structure);
            }
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                collect_arg_free(arg, bound, free);
            }
        }
        LetValue::FVar { fvar, args } => {
            if !bound.contains(fvar) {
                free.insert(*fvar);
            }
            for arg in args {
                collect_arg_free(arg, bound, free);
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            if !bound.contains(slot) {
                free.insert(*slot);
            }
            for arg in args {
                collect_arg_free(arg, bound, free);
            }
        }
        LetValue::Lit(_) | LetValue::Erased => {}
    }
}

fn collect_arg_free(arg: &Arg, bound: &BTreeSet<FVarId>, free: &mut BTreeSet<FVarId>) {
    if let Arg::FVar(id) = arg {
        if !bound.contains(id) {
            free.insert(*id);
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Pretty summary
// ════════════════════════════════════════════════════════════════════════════

/// Return a concise one-line summary of a `Code` tree for debugging.
///
/// Format: `"<kind>(<details>) depth=N size=M fvars=K"`
#[must_use]
pub(crate) fn code_summary(code: &Code) -> String {
    let stats = code_stats(code);
    let depth = code_depth(code);
    let size = code_size(code);
    let fv = free_vars(code);
    let kind = match code {
        Code::Let(..) => "Let",
        Code::Fun(..) => "Fun",
        Code::JoinPoint(..) => "JoinPoint",
        Code::Cases(..) => "Cases",
        Code::Jmp { .. } => "Jmp",
        Code::Return(_) => "Return",
        Code::Unreachable(_) => "Unreachable",
    };
    format!(
        "{kind}(lets={} funs={} jps={} cases={}) depth={depth} size={size} free_vars={}",
        stats.let_bindings,
        stats.fun_decls,
        stats.join_points,
        stats.cases,
        fv.len()
    )
}

/// Return a concise summary of a `Decl` for debugging.
#[must_use]
pub(crate) fn decl_summary(decl: &Decl) -> String {
    match &decl.body {
        DeclValue::Extern(attr) => {
            let backends: Vec<&str> = attr.entries.iter().map(|e| e.backend.as_str()).collect();
            format!(
                "extern {} params={} backends=[{}]",
                decl.name,
                decl.params.len(),
                backends.join(", ")
            )
        }
        DeclValue::Code(code) => {
            let stats = code_stats(code);
            let depth = code_depth(code);
            format!(
                "{} params={} recursive={} nodes={} depth={depth}",
                decl.name,
                decl.params.len(),
                decl.recursive,
                stats.total_nodes()
            )
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Complexity analysis
// ════════════════════════════════════════════════════════════════════════════

/// Complexity metrics for an LCNF code block.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Complexity {
    /// Maximum depth of nested let-bindings.
    pub(crate) max_let_depth: usize,
    /// Maximum depth of nested case expressions.
    pub(crate) max_case_depth: usize,
    /// Total number of case alternatives across all cases.
    pub(crate) total_case_alts: usize,
    /// Number of function/join-point call sites (Const, FVar calls, Jmp).
    pub(crate) call_sites: usize,
    /// Number of join point definitions.
    pub(crate) join_point_count: usize,
}

/// Compute complexity metrics for a `Code` tree.
#[must_use]
pub(crate) fn complexity(code: &Code) -> Complexity {
    let mut cx = Complexity::default();
    compute_complexity(code, 0, 0, &mut cx);
    cx
}

fn compute_complexity(code: &Code, let_depth: usize, case_depth: usize, cx: &mut Complexity) {
    match code {
        Code::Let(decl, body) => {
            let new_depth = let_depth + 1;
            if new_depth > cx.max_let_depth {
                cx.max_let_depth = new_depth;
            }
            count_let_value_calls(&decl.value, cx);
            compute_complexity(body, new_depth, case_depth, cx);
        }
        Code::Fun(decl, body) => {
            compute_complexity(&decl.body, 0, 0, cx);
            compute_complexity(body, let_depth, case_depth, cx);
        }
        Code::JoinPoint(decl, body) => {
            cx.join_point_count += 1;
            compute_complexity(&decl.body, 0, 0, cx);
            compute_complexity(body, let_depth, case_depth, cx);
        }
        Code::Cases(cases) => {
            let new_depth = case_depth + 1;
            if new_depth > cx.max_case_depth {
                cx.max_case_depth = new_depth;
            }
            cx.total_case_alts += cases.alts.len();
            for alt in &cases.alts {
                compute_complexity(alt.body(), 0, new_depth, cx);
            }
        }
        Code::Jmp { .. } => {
            cx.call_sites += 1;
        }
        Code::Return(_) | Code::Unreachable(_) => {}
    }
}

fn count_let_value_calls(val: &LetValue, cx: &mut Complexity) {
    match val {
        LetValue::Const { .. } | LetValue::FVar { .. } => {
            cx.call_sites += 1;
        }
        LetValue::Lit(_)
        | LetValue::Erased
        | LetValue::Proj { .. }
        | LetValue::Ctor { .. }
        | LetValue::Reuse { .. } => {}
    }
}
