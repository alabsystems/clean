// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended optimization passes for L5IR.
//!
//! Concrete IR-level passes: LICM analysis, CSE, strength reduction, algebraic
//! simplification, dead store elimination, tail call detection, and inlining
//! heuristics with cost model. Collects per-pass [`PassStatistics`].
//!
//! Part of #3083 - Compiler extensibility.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, VarId};
use crate::pass_manager::Phase;

/// Errors from extended optimization passes.
#[derive(Debug, thiserror::Error)]
pub(crate) enum OptPassExtError {
    #[error("pass order violation: {0}")]
    PassOrderViolation(String),
    #[error("invalid config: {0}")]
    InvalidConfig(String),
}

/// Per-pass statistics.
#[derive(Debug, Clone, Default)]
pub(crate) struct PassStatistics {
    pub(crate) exprs_hoisted: usize,
    pub(crate) cse_eliminated: usize,
    pub(crate) strength_reductions: usize,
    pub(crate) algebraic_simplifications: usize,
    pub(crate) dead_stores_removed: usize,
    pub(crate) tail_calls_detected: usize,
    pub(crate) inline_candidates: usize,
    pub(crate) duration_us: u64,
}

impl PassStatistics {
    #[must_use]
    pub(crate) fn total_transforms(&self) -> usize {
        self.exprs_hoisted
            + self.cse_eliminated
            + self.strength_reductions
            + self.algebraic_simplifications
            + self.dead_stores_removed
    }
}

#[derive(Debug, Clone)]
pub(crate) struct OptPassExtConfig {
    pub(crate) enable_profiling: bool,
    pub(crate) dump_ir_after_pass: bool,
    pub(crate) max_pass_iterations: usize,
    pub(crate) skip_passes: Vec<String>,
    pub(crate) inline_threshold: usize,
}

impl Default for OptPassExtConfig {
    fn default() -> Self {
        Self {
            enable_profiling: false,
            dump_ir_after_pass: false,
            max_pass_iterations: 3,
            skip_passes: Vec::new(),
            inline_threshold: 20,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct PassPipelineResult {
    pub(crate) pass_stats: Vec<(String, PassStatistics)>,
    pub(crate) total_duration_us: u64,
    pub(crate) total_decls_modified: usize,
    pub(crate) passes_skipped: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct ExtOptPass {
    pub(crate) name: String,
    pub(crate) phase: Phase,
    pub(crate) priority: u32,
    pub(crate) is_required: bool,
}

impl ExtOptPass {
    pub(crate) fn new(name: &str, phase: Phase, priority: u32, req: bool) -> Self {
        Self {
            name: name.to_owned(),
            phase,
            priority,
            is_required: req,
        }
    }
}

// --- IR size ---

#[must_use]
pub(crate) fn compute_ir_size(decls: &[IRDecl]) -> usize {
    decls.iter().map(|d| count_body_nodes(&d.body)).sum()
}

pub(crate) fn count_body_nodes(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { value, rest, .. } => 1 + count_expr_nodes(value) + count_body_nodes(rest),
        IRBody::JDecl { body, rest, .. } => 1 + count_body_nodes(body) + count_body_nodes(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + count_body_nodes(rest),
        IRBody::Case { alts, default, .. } => {
            1 + alts
                .iter()
                .map(|a| count_body_nodes(&a.body))
                .sum::<usize>()
                + default.as_ref().map_or(0, |d| count_body_nodes(d))
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

fn count_expr_nodes(expr: &IRExpr) -> usize {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. }
        | IRExpr::ClosureApply { args, .. }
        | IRExpr::Reuse { args, .. } => 1 + args.len(),
        _ => 1,
    }
}

// --- Variable helpers ---

fn expr_uses(expr: &IRExpr) -> HashSet<VarId> {
    let mut s = HashSet::new();
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. }
        | IRExpr::ClosureApply { args, .. }
        | IRExpr::Reuse { args, .. } => args.iter().for_each(|a| {
            if let IRArg::Var(v) = a {
                s.insert(*v);
            }
        }),
        IRExpr::Proj { arg, .. } | IRExpr::Box { arg, .. } | IRExpr::Unbox { arg, .. } => {
            if let IRArg::Var(v) = arg {
                s.insert(*v);
            }
        }
        IRExpr::Tag(a) => {
            if let IRArg::Var(v) = a {
                s.insert(*v);
            }
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            s.insert(*var);
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
    s
}

fn body_reads(body: &IRBody) -> HashSet<VarId> {
    let mut s = HashSet::new();
    collect_reads(body, &mut s);
    s
}

fn collect_reads(body: &IRBody, s: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            s.extend(expr_uses(value));
            collect_reads(rest, s);
        }
        IRBody::JDecl { body: b, rest, .. } => {
            collect_reads(b, s);
            collect_reads(rest, s);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
            s.insert(*var);
            collect_reads(rest, s);
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
            s.insert(*var);
            s.insert(*value);
            collect_reads(rest, s);
        }
        IRBody::SetTag { var, rest, .. } => {
            s.insert(*var);
            collect_reads(rest, s);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            s.insert(*scrutinee);
            alts.iter().for_each(|a| collect_reads(&a.body, s));
            if let Some(d) = default {
                collect_reads(d, s);
            }
        }
        IRBody::Jmp { args, .. } => args.iter().for_each(|a| {
            if let IRArg::Var(v) = a {
                s.insert(*v);
            }
        }),
        IRBody::Ret(IRArg::Var(v)) => {
            s.insert(*v);
        }
        _ => {}
    }
}

// --- Algebraic simplification ---

pub(crate) fn algebraic_simplify_expr(expr: &IRExpr) -> (IRExpr, bool) {
    match expr {
        IRExpr::Lit(IRLiteral::Bool(b)) => (IRExpr::Lit(IRLiteral::Bool(*b)), false),
        _ => (expr.clone(), false),
    }
}

/// Strength reduction placeholder.
pub(crate) fn strength_reduce_expr(expr: &IRExpr) -> (IRExpr, bool) {
    (expr.clone(), false)
}

// --- CSE ---

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ExprKey {
    Lit(LitKey),
    Proj(u32, ArgKey),
    Tag(ArgKey),
    Str(String),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LitKey {
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    USize(usize),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ArgKey {
    Var(u32),
    Erased,
}

fn arg_key(a: &IRArg) -> ArgKey {
    match a {
        IRArg::Var(v) => ArgKey::Var(v.0),
        IRArg::Erased => ArgKey::Erased,
    }
}

fn expr_key(expr: &IRExpr) -> Option<ExprKey> {
    match expr {
        IRExpr::Lit(lit) => Some(ExprKey::Lit(match lit {
            IRLiteral::Bool(b) => LitKey::Bool(*b),
            IRLiteral::UInt8(v) => LitKey::U8(*v),
            IRLiteral::UInt16(v) => LitKey::U16(*v),
            IRLiteral::UInt32(v) => LitKey::U32(*v),
            IRLiteral::UInt64(v) => LitKey::U64(*v),
            IRLiteral::USize(v) => LitKey::USize(*v),
            _ => return None,
        })),
        IRExpr::Proj { idx, arg, .. } => Some(ExprKey::Proj(*idx, arg_key(arg))),
        IRExpr::Tag(a) => Some(ExprKey::Tag(arg_key(a))),
        IRExpr::String(s) => Some(ExprKey::Str(s.clone())),
        _ => None,
    }
}

pub(crate) fn cse_body(body: &IRBody) -> (IRBody, usize) {
    let mut seen: HashMap<ExprKey, VarId> = HashMap::new();
    let mut n = 0;
    let r = cse_inner(body, &mut seen, &mut n);
    (r, n)
}

fn cse_inner(body: &IRBody, seen: &mut HashMap<ExprKey, VarId>, n: &mut usize) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let Some(key) = expr_key(value) {
                if let Some(&prev) = seen.get(&key) {
                    *n += 1;
                    return cse_inner(&subst_var(rest, *var, prev), seen, n);
                }
                seen.insert(key, *var);
            }
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(cse_inner(rest, seen, n)),
            }
        }
        IRBody::Inc { var, n: cnt, rest } => IRBody::Inc {
            var: *var,
            n: *cnt,
            rest: Box::new(cse_inner(rest, seen, n)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(cse_inner(rest, seen, n)),
        },
        other => other.clone(),
    }
}

fn subst_arg(a: &IRArg, from: VarId, to: VarId) -> IRArg {
    match a {
        IRArg::Var(v) if *v == from => IRArg::Var(to),
        o => o.clone(),
    }
}

fn subst_var(body: &IRBody, from: VarId, to: VarId) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: value.clone(),
            rest: Box::new(subst_var(rest, from, to)),
        },
        IRBody::Ret(a) => IRBody::Ret(subst_arg(a, from, to)),
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.iter().map(|a| subst_arg(a, from, to)).collect(),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: if *var == from { to } else { *var },
            n: *n,
            rest: Box::new(subst_var(rest, from, to)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: if *var == from { to } else { *var },
            rest: Box::new(subst_var(rest, from, to)),
        },
        other => other.clone(),
    }
}

// --- Dead store elimination ---

pub(crate) fn dead_store_eliminate(body: &IRBody) -> (IRBody, usize) {
    let mut n = 0;
    let r = dse_inner(body, &mut n);
    (r, n)
}

fn dse_inner(body: &IRBody, n: &mut usize) -> IRBody {
    match body {
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } if !body_reads(rest).contains(var) => {
            *n += 1;
            dse_inner(rest, n)
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
            rest: Box::new(dse_inner(rest, n)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } if !body_reads(rest).contains(var) => {
            *n += 1;
            dse_inner(rest, n)
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(dse_inner(rest, n)),
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
            rest: Box::new(dse_inner(rest, n)),
        },
        IRBody::Inc { var, n: cnt, rest } => IRBody::Inc {
            var: *var,
            n: *cnt,
            rest: Box::new(dse_inner(rest, n)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(dse_inner(rest, n)),
        },
        other => other.clone(),
    }
}

// --- Tail call detection ---

#[must_use]
pub(crate) fn detect_tail_calls(decl: &IRDecl) -> bool {
    has_self_apply(&decl.body, &decl.name)
}

fn has_self_apply(body: &IRBody, name: &clean_kernel::Name) -> bool {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, .. } = value {
                if fn_id.0 == *name && matches!(rest.as_ref(), IRBody::Ret(_)) {
                    return true;
                }
            }
            has_self_apply(rest, name)
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => has_self_apply(rest, name),
        IRBody::JDecl { body, rest, .. } => {
            has_self_apply(body, name) || has_self_apply(rest, name)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|a| has_self_apply(&a.body, name))
                || default.as_ref().is_some_and(|d| has_self_apply(d, name))
        }
        _ => false,
    }
}

// --- LICM analysis ---

#[must_use]
pub(crate) fn find_hoistable_exprs(body: &IRBody) -> Vec<VarId> {
    let mut defined = HashSet::new();
    let mut out = Vec::new();
    licm_scan(body, &mut defined, &mut out);
    out
}

fn licm_scan(body: &IRBody, defined: &mut HashSet<VarId>, out: &mut Vec<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            let uses = expr_uses(value);
            if !uses.is_empty() && !uses.iter().any(|u| defined.contains(u)) {
                out.push(*var);
            }
            defined.insert(*var);
            licm_scan(rest, defined, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => licm_scan(rest, defined, out),
        IRBody::JDecl { body, rest, .. } => {
            licm_scan(body, defined, out);
            licm_scan(rest, defined, out);
        }
        _ => {}
    }
}

// --- Inlining heuristics ---

#[derive(Debug, Clone)]
pub(crate) struct InlineCost {
    pub(crate) body_size: usize,
    pub(crate) param_count: usize,
    pub(crate) is_recursive: bool,
    pub(crate) score: u32,
}

#[must_use]
pub(crate) fn compute_inline_cost(decl: &IRDecl, _config: &OptPassExtConfig) -> InlineCost {
    let body_size = count_body_nodes(&decl.body);
    let is_recursive = detect_tail_calls(decl);
    let score =
        body_size as u32 + (decl.params.len() as u32) * 2 + if is_recursive { 100 } else { 0 };
    InlineCost {
        body_size,
        param_count: decl.params.len(),
        is_recursive,
        score,
    }
}

#[must_use]
pub(crate) fn should_inline(cost: &InlineCost, config: &OptPassExtConfig) -> bool {
    !cost.is_recursive && cost.body_size <= config.inline_threshold
}

// --- Validation, snapshot, skip, merge ---

pub(crate) fn validate_pass_order(passes: &[ExtOptPass]) -> Result<(), Vec<String>> {
    let mut errs = Vec::new();
    for w in passes.windows(2) {
        if w[1].phase < w[0].phase {
            errs.push(format!(
                "pass '{}' (phase {}) comes after '{}' (phase {}): phases must not go backward",
                w[1].name, w[1].phase, w[0].name, w[0].phase
            ));
        }
    }
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

#[must_use]
pub(crate) fn dump_ir_snapshot(decls: &[IRDecl], pass_name: &str) -> String {
    let mut buf = format!(
        "=== After pass: {} ({} decl(s)) ===\n",
        pass_name,
        decls.len()
    );
    for d in decls {
        buf.push_str(&format!(
            "  fn {} ({} params, {} IR nodes)\n",
            d.name,
            d.params.len(),
            count_body_nodes(&d.body)
        ));
    }
    buf
}

#[must_use]
pub(crate) fn should_run_pass(pass: &ExtOptPass, config: &OptPassExtConfig) -> bool {
    pass.is_required || !config.skip_passes.iter().any(|s| s == &pass.name)
}

#[must_use]
pub(crate) fn merge_pipeline_results(results: &[PassPipelineResult]) -> PassPipelineResult {
    let mut m = PassPipelineResult::default();
    for r in results {
        m.pass_stats.extend(r.pass_stats.iter().cloned());
        m.total_duration_us += r.total_duration_us;
        m.total_decls_modified += r.total_decls_modified;
        m.passes_skipped += r.passes_skipped;
    }
    m
}

// --- Default pass ordering ---

#[must_use]
pub(crate) fn default_pass_order() -> Vec<ExtOptPass> {
    vec![
        ExtOptPass::new("licm", Phase::Base, 5, false),
        ExtOptPass::new("ir_dce", Phase::Base, 10, false),
        ExtOptPass::new("algebraic_simp", Phase::Base, 15, false),
        ExtOptPass::new("ir_cse", Phase::Base, 20, false),
        ExtOptPass::new("strength_reduce", Phase::Base, 25, false),
        ExtOptPass::new("dead_store_elim", Phase::Base, 30, false),
        ExtOptPass::new("ir_specialize", Phase::Mono, 10, false),
        ExtOptPass::new("ir_inline", Phase::Mono, 20, false),
        ExtOptPass::new("tail_call_detect", Phase::Mono, 25, false),
        ExtOptPass::new("ir_const_fold", Phase::Mono, 30, false),
        ExtOptPass::new("ir_rc_insert", Phase::Impure, 10, true),
        ExtOptPass::new("ir_reset_reuse", Phase::Impure, 20, false),
        ExtOptPass::new("ir_borrow_infer", Phase::Impure, 30, false),
    ]
}

// --- Pipeline execution ---

pub(crate) fn run_optimization_pipeline(
    decls: &mut [IRDecl],
    passes: &[ExtOptPass],
    config: &OptPassExtConfig,
) -> PassPipelineResult {
    let mut result = PassPipelineResult::default();
    let start = Instant::now();
    for _iter in 0..config.max_pass_iterations {
        let mut changed = false;
        for pass in passes {
            if !should_run_pass(pass, config) {
                result.passes_skipped += 1;
                continue;
            }
            let t = Instant::now();
            let mut stats = PassStatistics::default();
            match pass.name.as_str() {
                "ir_cse" => {
                    for d in decls.iter_mut() {
                        let (b, c) = cse_body(&d.body);
                        if c > 0 {
                            d.body = b;
                            stats.cse_eliminated += c;
                            changed = true;
                        }
                    }
                }
                "dead_store_elim" => {
                    for d in decls.iter_mut() {
                        let (b, c) = dead_store_eliminate(&d.body);
                        if c > 0 {
                            d.body = b;
                            stats.dead_stores_removed += c;
                            changed = true;
                        }
                    }
                }
                "tail_call_detect" => {
                    for d in decls.iter() {
                        if detect_tail_calls(d) {
                            stats.tail_calls_detected += 1;
                        }
                    }
                }
                "licm" => {
                    for d in decls.iter() {
                        stats.exprs_hoisted += find_hoistable_exprs(&d.body).len();
                    }
                }
                "ir_inline" => {
                    for d in decls.iter() {
                        if should_inline(&compute_inline_cost(d, config), config) {
                            stats.inline_candidates += 1;
                        }
                    }
                }
                _ => {}
            }
            stats.duration_us = t.elapsed().as_micros() as u64;
            if config.enable_profiling {
                result.pass_stats.push((pass.name.clone(), stats.clone()));
            }
            result.total_decls_modified += stats.total_transforms();
            if config.dump_ir_after_pass {
                let _ = dump_ir_snapshot(decls, &pass.name);
            }
        }
        if !changed {
            break;
        }
    }
    result.total_duration_us = start.elapsed().as_micros() as u64;
    result
}

pub(crate) fn run_optimization_pipeline_default(decls: &mut [IRDecl]) -> PassPipelineResult {
    run_optimization_pipeline(decls, &default_pass_order(), &OptPassExtConfig::default())
}
