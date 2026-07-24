// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended inlining pass for L5IR.
//!
//! Builds on `inline_pass` with cost model, call-site analysis, recursive
//! inlining limits, partial inlining, annotation support, cross-module
//! summaries, depth tracking, post-inline cleanup, and extended statistics.
//!
//! Part of #3083 - Extensibility.

use crate::inline_pass::{body_references_name, estimate_size, InlineAttr};
use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

/// Extended inlining pass configuration.
#[derive(Clone, Debug)]
pub(crate) struct ExtInlineConfig {
    pub(crate) max_inline_size: usize,
    pub(crate) max_inline_depth: usize,
    pub(crate) max_recursive_unroll: usize,
    pub(crate) benefit_cost_ratio: f64,
    pub(crate) enable_partial_inline: bool,
    pub(crate) enable_cleanup: bool,
    pub(crate) max_growth_factor: f64,
}

impl Default for ExtInlineConfig {
    fn default() -> Self {
        Self {
            max_inline_size: 20,
            max_inline_depth: 4,
            max_recursive_unroll: 2,
            benefit_cost_ratio: 1.5,
            enable_partial_inline: true,
            enable_cleanup: true,
            max_growth_factor: 3.0,
        }
    }
}

/// Cost model for inlining decisions.
#[derive(Clone, Debug)]
pub(crate) struct InlineCostModel {
    pub(crate) call_overhead: usize,
    pub(crate) node_cost: usize,
}

impl Default for InlineCostModel {
    fn default() -> Self {
        Self {
            call_overhead: 5,
            node_cost: 1,
        }
    }
}

impl InlineCostModel {
    /// Benefit of inlining: call overhead saved + param optimization bonus.
    #[must_use]
    pub(crate) fn estimate_benefit(&self, callee: &IRDecl, call_count: usize) -> usize {
        let base = self.call_overhead + callee.params.len();
        if call_count == 1 {
            base + estimate_size(&callee.body)
        } else {
            base
        }
    }
    /// Code-size cost of inlining a callee.
    #[must_use]
    pub(crate) fn estimate_cost(&self, callee: &IRDecl, call_count: usize) -> usize {
        if call_count == 1 {
            0
        } else {
            estimate_size(&callee.body)
                .saturating_mul(self.node_cost)
                .saturating_mul(call_count.saturating_sub(1))
        }
    }
}

/// Information about a call site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallSiteInfo {
    pub(crate) callee: Name,
    pub(crate) call_count: usize,
    pub(crate) in_case_branch: bool,
    pub(crate) nesting_depth: usize,
}

/// Analyze all call sites across declarations.
#[must_use]
pub(crate) fn analyze_call_sites(decls: &[IRDecl]) -> Vec<CallSiteInfo> {
    let mut counts: HashMap<Name, usize> = HashMap::new();
    for d in decls {
        count_calls(&d.body, &mut counts);
    }
    let mut sites = Vec::new();
    for d in decls {
        collect_sites(&d.body, &counts, false, 0, &mut sites);
    }
    sites
}

fn count_calls(body: &IRBody, counts: &mut HashMap<Name, usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = value {
                *counts.entry(fn_id.0.clone()).or_insert(0) += 1;
            }
            count_calls(rest, counts);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            count_calls(jp, counts);
            count_calls(rest, counts);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => count_calls(rest, counts),
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                count_calls(&a.body, counts);
            }
            if let Some(d) = default {
                count_calls(d, counts);
            }
        }
        _ => {}
    }
}

fn collect_sites(
    body: &IRBody,
    counts: &HashMap<Name, usize>,
    in_case: bool,
    depth: usize,
    out: &mut Vec<CallSiteInfo>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, .. } = value {
                out.push(CallSiteInfo {
                    callee: fn_id.0.clone(),
                    call_count: counts.get(&fn_id.0).copied().unwrap_or(0),
                    in_case_branch: in_case,
                    nesting_depth: depth,
                });
            }
            collect_sites(rest, counts, in_case, depth, out);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_sites(jp, counts, in_case, depth + 1, out);
            collect_sites(rest, counts, in_case, depth, out);
        }
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                collect_sites(&a.body, counts, true, depth + 1, out);
            }
            if let Some(d) = default {
                collect_sites(d, counts, true, depth + 1, out);
            }
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_sites(rest, counts, in_case, depth, out),
        _ => {}
    }
}

/// Tracks per-function recursive inlining depth.
#[derive(Clone, Debug, Default)]
pub(crate) struct RecursiveInlineTracker {
    depths: HashMap<Name, usize>,
}

impl RecursiveInlineTracker {
    #[must_use]
    pub(crate) fn can_unroll(&self, name: &Name, max: usize) -> bool {
        self.depths.get(name).copied().unwrap_or(0) < max
    }
    pub(crate) fn record_unroll(&mut self, name: &Name) {
        *self.depths.entry(name.clone()).or_insert(0) += 1;
    }
    #[must_use]
    pub(crate) fn depth_of(&self, name: &Name) -> usize {
        self.depths.get(name).copied().unwrap_or(0)
    }
}

/// Tracks nested inlining depth for code explosion prevention.
#[derive(Clone, Debug, Default)]
pub(crate) struct InlineDepthTracker {
    current: usize,
    max_seen: usize,
    distribution: HashMap<usize, usize>,
}

impl InlineDepthTracker {
    #[must_use]
    pub(crate) fn check_depth(&self, max_depth: usize) -> bool {
        self.current < max_depth
    }
    pub(crate) fn record_inline(&mut self) {
        self.current += 1;
        if self.current > self.max_seen {
            self.max_seen = self.current;
        }
        *self.distribution.entry(self.current).or_insert(0) += 1;
    }
    pub(crate) fn pop(&mut self) {
        self.current = self.current.saturating_sub(1);
    }
    #[must_use]
    pub(crate) fn max_depth_seen(&self) -> usize {
        self.max_seen
    }
    #[must_use]
    pub(crate) fn depth_distribution(&self) -> &HashMap<usize, usize> {
        &self.distribution
    }
}

/// Candidate for partial inlining: function with a Case body having a small fast path.
#[derive(Clone, Debug)]
pub(crate) struct PartialInlineCandidate {
    pub(crate) name: Name,
    pub(crate) fast_alt_idx: usize,
    pub(crate) fast_path_size: usize,
    pub(crate) total_size: usize,
}

/// Find functions suitable for partial inlining.
#[must_use]
pub(crate) fn find_partial_inline_candidates(
    decls: &[IRDecl],
    threshold: usize,
) -> Vec<PartialInlineCandidate> {
    let mut out = Vec::new();
    for decl in decls {
        if let IRBody::Case { alts, .. } = &decl.body {
            let total = estimate_size(&decl.body);
            if total <= threshold {
                continue;
            }
            for (idx, alt) in alts.iter().enumerate() {
                let sz = estimate_size(&alt.body);
                if sz <= threshold {
                    out.push(PartialInlineCandidate {
                        name: decl.name.clone(),
                        fast_alt_idx: idx,
                        fast_path_size: sz,
                        total_size: total,
                    });
                    break;
                }
            }
        }
    }
    out
}

/// Extract the fast-path from a Case-based body with fallback to original call.
#[must_use]
pub(crate) fn apply_partial_inline(
    decl: &IRDecl,
    fast_alt_idx: usize,
    result_var: VarId,
) -> Option<IRBody> {
    if let IRBody::Case {
        scrutinee, alts, ..
    } = &decl.body
    {
        let fast = alts.get(fast_alt_idx)?;
        let fallback = IRBody::VDecl {
            var: result_var,
            ty: decl.return_type.clone(),
            value: IRExpr::Apply {
                fn_id: FnId(decl.name.clone()),
                args: decl.params.iter().map(|(v, _)| IRArg::Var(*v)).collect(),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(result_var))),
        };
        Some(IRBody::Case {
            scrutinee: *scrutinee,
            alts: vec![IRAlt {
                ctor: fast.ctor.clone(),
                body: fast.body.clone(),
            }],
            default: Some(Box::new(fallback)),
        })
    } else {
        None
    }
}

/// Summary of a function's inlining characteristics for cross-module use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InliningSummary {
    pub(crate) name: Name,
    pub(crate) size: usize,
    pub(crate) attr: InlineAttr,
    pub(crate) is_recursive: bool,
    pub(crate) param_count: usize,
    pub(crate) is_case_dispatch: bool,
}

/// Compute inlining summaries for cross-module use.
#[must_use]
pub(crate) fn compute_inlining_summaries(
    decls: &[IRDecl],
    attrs: &HashMap<Name, InlineAttr>,
) -> Vec<InliningSummary> {
    decls
        .iter()
        .map(|d| InliningSummary {
            name: d.name.clone(),
            size: estimate_size(&d.body),
            attr: attrs.get(&d.name).cloned().unwrap_or(InlineAttr::None),
            is_recursive: body_references_name(&d.body, &d.name),
            param_count: d.params.len(),
            is_case_dispatch: matches!(d.body, IRBody::Case { .. }),
        })
        .collect()
}

/// Propagate trivial copies: `let v := _identity(w)` => replace v with w.
#[must_use]
pub(crate) fn propagate_copies(body: &IRBody) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Apply { fn_id, args } = value {
                if fn_id.0 == Name::from_string("_identity") && args.len() == 1 {
                    if let Some(IRArg::Var(src)) = args.first() {
                        return propagate_copies(&subst_var_body(rest, *var, *src));
                    }
                }
            }
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(propagate_copies(rest)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(propagate_copies(jp_body)),
            rest: Box::new(propagate_copies(rest)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(propagate_copies(rest)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(propagate_copies(rest)),
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
                    body: Box::new(propagate_copies(&a.body)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(propagate_copies(d))),
        },
        other => other.clone(),
    }
}

fn subst_var_body(body: &IRBody, old: VarId, new: VarId) -> IRBody {
    let sv = |v: VarId| if v == old { new } else { v };
    let sa = |a: &IRArg| match a {
        IRArg::Var(v) => IRArg::Var(sv(*v)),
        IRArg::Erased => IRArg::Erased,
    };
    let se = |e: &IRExpr| subst_var_expr(e, old, new);
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: se(value),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(subst_var_body(jp_body, old, new)),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: sv(*var),
            n: *n,
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: sv(*var),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: sv(*var),
            idx: *idx,
            value: sv(*value),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: sv(*var),
            tag: *tag,
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: sv(*var),
            idx: *idx,
            value: sv(*value),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: sv(*var),
            n: *n,
            offset: *offset,
            value: sv(*value),
            ty: ty.clone(),
            rest: Box::new(subst_var_body(rest, old, new)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: sv(*scrutinee),
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(subst_var_body(&a.body, old, new)),
                })
                .collect(),
            default: default
                .as_ref()
                .map(|d| Box::new(subst_var_body(d, old, new))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.iter().map(&sa).collect(),
        },
        IRBody::Ret(arg) => IRBody::Ret(sa(arg)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

fn subst_var_expr(expr: &IRExpr, old: VarId, new: VarId) -> IRExpr {
    let sv = |v: VarId| if v == old { new } else { v };
    let sa = |a: &IRArg| match a {
        IRArg::Var(v) => IRArg::Var(sv(*v)),
        IRArg::Erased => IRArg::Erased,
    };
    let sargs = |args: &[IRArg]| args.iter().map(&sa).collect();
    match expr {
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: sargs(args),
        },
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: sargs(args),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: sargs(args),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: sa(closure),
            args: sargs(args),
        },
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: sv(*var),
            ctor: ctor.clone(),
            args: sargs(args),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: sa(arg),
        },
        IRExpr::Tag(a) => IRExpr::Tag(sa(a)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: sa(arg),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: sa(arg),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: sv(*var),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: sv(*var),
            ty: ty.clone(),
        },
        IRExpr::IsShared(v) => IRExpr::IsShared(sv(*v)),
        IRExpr::Reset(v) => IRExpr::Reset(sv(*v)),
        IRExpr::Lit(l) => IRExpr::Lit(l.clone()),
        IRExpr::String(s) => IRExpr::String(s.clone()),
    }
}

/// Eliminate dead VDecls with pure values where the var is unused in rest.
#[must_use]
pub(crate) fn eliminate_dead_vars(body: &IRBody) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let r = eliminate_dead_vars(rest);
            if is_pure(value) && !uses_var(&r, *var) {
                r
            } else {
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(r),
                }
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: j,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(eliminate_dead_vars(j)),
            rest: Box::new(eliminate_dead_vars(rest)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(eliminate_dead_vars(rest)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(eliminate_dead_vars(rest)),
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
                    body: Box::new(eliminate_dead_vars(&a.body)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(eliminate_dead_vars(d))),
        },
        other => other.clone(),
    }
}

fn is_pure(e: &IRExpr) -> bool {
    matches!(
        e,
        IRExpr::Lit(_)
            | IRExpr::String(_)
            | IRExpr::Proj { .. }
            | IRExpr::Tag(_)
            | IRExpr::Box { .. }
            | IRExpr::Unbox { .. }
            | IRExpr::UProj { .. }
            | IRExpr::SProj { .. }
            | IRExpr::IsShared(_)
    )
}

fn uses_var(body: &IRBody, t: VarId) -> bool {
    let av = |a: &IRArg| matches!(a, IRArg::Var(v) if *v == t);
    match body {
        IRBody::VDecl { value, rest, .. } => uses_var_expr(value, t) || uses_var(rest, t),
        IRBody::JDecl { body: j, rest, .. } => uses_var(j, t) || uses_var(rest, t),
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => *var == t || uses_var(rest, t),
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => *var == t || *value == t || uses_var(rest, t),
        IRBody::SetTag { var, rest, .. } => *var == t || uses_var(rest, t),
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            *scrutinee == t
                || alts.iter().any(|a| uses_var(&a.body, t))
                || default.as_ref().is_some_and(|d| uses_var(d, t))
        }
        IRBody::Jmp { args, .. } => args.iter().any(av),
        IRBody::Ret(a) => av(a),
        IRBody::Unreachable => false,
    }
}

fn uses_var_expr(e: &IRExpr, t: VarId) -> bool {
    let av = |a: &IRArg| matches!(a, IRArg::Var(v) if *v == t);
    match e {
        IRExpr::Apply { args, .. }
        | IRExpr::Ctor { args, .. }
        | IRExpr::PartialApply { args, .. } => args.iter().any(av),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => av(arg),
        IRExpr::ClosureApply { closure, args } => av(closure) || args.iter().any(av),
        IRExpr::Reuse { var, args, .. } => *var == t || args.iter().any(av),
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => *var == t,
        IRExpr::Lit(_) | IRExpr::String(_) => false,
    }
}

/// Extended statistics from the inlining pass.
#[derive(Clone, Debug, Default)]
pub(crate) struct ExtendedInlineStats {
    pub(crate) inlined_calls: usize,
    pub(crate) code_size_before: usize,
    pub(crate) code_size_after: usize,
    pub(crate) depth_distribution: HashMap<usize, usize>,
    pub(crate) partial_inlines: usize,
    pub(crate) skipped_by_cost: usize,
    pub(crate) skipped_noinline: usize,
    pub(crate) skipped_recursive: usize,
    pub(crate) skipped_depth: usize,
}

/// Run the extended inlining pass on a set of IR declarations.
#[must_use]
pub(crate) fn run_extended_inline_pass(
    decls: &[IRDecl],
    attrs: &HashMap<Name, InlineAttr>,
    config: &ExtInlineConfig,
) -> (Vec<IRDecl>, ExtendedInlineStats) {
    let cm = InlineCostModel::default();
    let mut stats = ExtendedInlineStats::default();
    let mut dt = InlineDepthTracker::default();
    stats.code_size_before = decls.iter().map(|d| estimate_size(&d.body)).sum();
    let env: HashMap<Name, IRDecl> = decls.iter().map(|d| (d.name.clone(), d.clone())).collect();
    let sites = analyze_call_sites(decls);
    let mut cc: HashMap<Name, usize> = HashMap::new();
    for s in &sites {
        *cc.entry(s.callee.clone()).or_insert(0) += 1;
    }
    let rec: HashSet<Name> = decls
        .iter()
        .filter(|d| body_references_name(&d.body, &d.name))
        .map(|d| d.name.clone())
        .collect();
    let result: Vec<IRDecl> = decls
        .iter()
        .map(|decl| {
            let nb = do_inline(
                &decl.body, &env, attrs, &cc, &rec, &cm, config, &mut dt, &mut stats, 0,
            );
            let cleaned = if config.enable_cleanup {
                eliminate_dead_vars(&propagate_copies(&nb))
            } else {
                nb
            };
            IRDecl {
                name: decl.name.clone(),
                params: decl.params.clone(),
                return_type: decl.return_type.clone(),
                body: cleaned,
            }
        })
        .collect();
    stats.code_size_after = result.iter().map(|d| estimate_size(&d.body)).sum();
    stats.depth_distribution = dt.depth_distribution().clone();
    (result, stats)
}

fn do_inline(
    body: &IRBody,
    env: &HashMap<Name, IRDecl>,
    attrs: &HashMap<Name, InlineAttr>,
    cc: &HashMap<Name, usize>,
    rec: &HashSet<Name>,
    cm: &InlineCostModel,
    cfg: &ExtInlineConfig,
    dt: &mut InlineDepthTracker,
    stats: &mut ExtendedInlineStats,
    depth: usize,
) -> IRBody {
    if depth > cfg.max_inline_depth {
        stats.skipped_depth += 1;
        return body.clone();
    }
    let recurse = |b: &IRBody, dt: &mut InlineDepthTracker, st: &mut ExtendedInlineStats| {
        do_inline(b, env, attrs, cc, rec, cm, cfg, dt, st, depth)
    };
    match body {
        IRBody::VDecl {
            var,
            ty,
            value: IRExpr::Apply { fn_id, args },
            rest,
        } => {
            let cn = &fn_id.0;
            let attr = attrs.get(cn).unwrap_or(&InlineAttr::None);
            let skip = |stats: &mut ExtendedInlineStats, dt: &mut InlineDepthTracker| {
                let nr = do_inline(rest, env, attrs, cc, rec, cm, cfg, dt, stats, depth);
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args: args.to_vec(),
                    },
                    rest: Box::new(nr),
                }
            };
            if *attr == InlineAttr::NoInline {
                stats.skipped_noinline += 1;
                return skip(stats, dt);
            }
            if rec.contains(cn) {
                stats.skipped_recursive += 1;
                return skip(stats, dt);
            }
            let Some(callee) = env.get(cn) else {
                return skip(stats, dt);
            };
            if !dt.check_depth(cfg.max_inline_depth) {
                stats.skipped_depth += 1;
                return skip(stats, dt);
            }
            let should = *attr == InlineAttr::Always || *attr == InlineAttr::Inline || {
                let cnt = cc.get(cn).copied().unwrap_or(0);
                let b = cm.estimate_benefit(callee, cnt);
                let c = cm.estimate_cost(callee, cnt);
                estimate_size(&callee.body) <= cfg.max_inline_size
                    || c == 0
                    || (b as f64 >= c as f64 * cfg.benefit_cost_ratio)
            };
            if !should {
                stats.skipped_by_cost += 1;
                return skip(stats, dt);
            }
            dt.record_inline();
            stats.inlined_calls += 1;
            let offset = crate::inline_pass::max_var_id(body)
                + crate::inline_pass::max_var_id(&callee.body)
                + 1;
            let inlined =
                crate::inline_pass::substitute_args(&callee.body, &callee.params, args, offset);
            let spliced = crate::inline_pass::splice_inlined(inlined, *var, ty.clone(), rest);
            let r = do_inline(&spliced, env, attrs, cc, rec, cm, cfg, dt, stats, depth + 1);
            dt.pop();
            r
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
            rest: Box::new(recurse(rest, dt, stats)),
        },
        IRBody::JDecl {
            jp,
            params,
            body: j,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(recurse(j, dt, stats)),
            rest: Box::new(recurse(rest, dt, stats)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(recurse(rest, dt, stats)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(recurse(rest, dt, stats)),
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
                    body: Box::new(recurse(&a.body, dt, stats)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(recurse(d, dt, stats))),
        },
        other => other.clone(),
    }
}
