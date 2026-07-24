// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended expensive constant boxing: cost estimation, hoisting analysis,
//! sharing detection, and impact reporting.
//!
//! Part of #3082 - Extended expensive constant boxing.

use std::collections::HashMap;
use std::fmt;

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, VarId};

// -- Error type ---------------------------------------------------------------

#[derive(Debug, Clone, thiserror::Error)]
pub(crate) enum ExpensiveConstExtError {
    #[error("cost threshold must be positive, got {0}")]
    InvalidThreshold(u64),
    #[error("declaration has no body to analyze: {name}")]
    EmptyDeclaration { name: String },
}

// -- Constant classification --------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ConstantClass {
    Literal,
    NullaryCtor,
    CompoundCtor { arg_count: usize },
    StringLit,
    Recursive { depth: u32 },
    FunctionApp,
}

impl fmt::Display for ConstantClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal => write!(f, "literal"),
            Self::NullaryCtor => write!(f, "nullary_ctor"),
            Self::CompoundCtor { arg_count } => write!(f, "compound_ctor({})", arg_count),
            Self::StringLit => write!(f, "string"),
            Self::Recursive { depth } => write!(f, "recursive(depth={})", depth),
            Self::FunctionApp => write!(f, "function_app"),
        }
    }
}

#[must_use]
pub(crate) fn classify_constant(expr: &IRExpr) -> ConstantClass {
    match expr {
        IRExpr::Lit(_) => ConstantClass::Literal,
        IRExpr::String(_) => ConstantClass::StringLit,
        IRExpr::Ctor { args, .. } if args.is_empty() => ConstantClass::NullaryCtor,
        IRExpr::Ctor { args, .. } => ConstantClass::CompoundCtor {
            arg_count: args.len(),
        },
        IRExpr::Apply { .. } | IRExpr::PartialApply { .. } | IRExpr::ClosureApply { .. } => {
            ConstantClass::FunctionApp
        }
        _ => ConstantClass::Literal,
    }
}

// -- Cost estimation ----------------------------------------------------------

/// Configurable thresholds for cost analysis.
#[derive(Clone, Debug)]
pub(crate) struct CostThresholds {
    pub(crate) expensive_threshold: u64,
    pub(crate) hoist_threshold: u64,
    pub(crate) alloc_cost: u64,
    pub(crate) per_arg_cost: u64,
    pub(crate) string_cost: u64,
    pub(crate) function_app_cost: u64,
}

impl Default for CostThresholds {
    fn default() -> Self {
        Self {
            expensive_threshold: 4,
            hoist_threshold: 8,
            alloc_cost: 4,
            per_arg_cost: 1,
            string_cost: 6,
            function_app_cost: 10,
        }
    }
}

impl CostThresholds {
    pub(crate) fn validate(&self) -> Result<(), ExpensiveConstExtError> {
        if self.expensive_threshold == 0 {
            return Err(ExpensiveConstExtError::InvalidThreshold(0));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CostEstimate {
    pub(crate) cost: u64,
    pub(crate) class: ConstantClass,
    pub(crate) is_expensive: bool,
    pub(crate) is_hoistable: bool,
}

#[must_use]
pub(crate) fn estimate_expr_cost(expr: &IRExpr, thresholds: &CostThresholds) -> CostEstimate {
    let class = classify_constant(expr);
    let cost = compute_raw_cost(expr, thresholds);
    CostEstimate {
        cost,
        class,
        is_expensive: cost >= thresholds.expensive_threshold,
        is_hoistable: cost >= thresholds.hoist_threshold,
    }
}

fn compute_raw_cost(expr: &IRExpr, t: &CostThresholds) -> u64 {
    match expr {
        IRExpr::Lit(lit) => literal_cost(lit),
        IRExpr::String(_) => t.string_cost,
        IRExpr::Ctor { args, .. } if args.is_empty() => 1,
        IRExpr::Ctor { args, .. } => t.alloc_cost + args.len() as u64 * t.per_arg_cost,
        IRExpr::Apply { args, .. } => t.function_app_cost + args.len() as u64,
        IRExpr::PartialApply { args, .. } => {
            t.alloc_cost + t.function_app_cost / 2 + args.len() as u64
        }
        IRExpr::ClosureApply { args, .. } => t.function_app_cost + args.len() as u64,
        IRExpr::Box { .. } => 2,
        IRExpr::Unbox { .. }
        | IRExpr::Proj { .. }
        | IRExpr::Tag(_)
        | IRExpr::UProj { .. }
        | IRExpr::SProj { .. }
        | IRExpr::IsShared(_) => 1,
        IRExpr::Reset(_) => 2,
        IRExpr::Reuse { args, .. } => t.alloc_cost + args.len() as u64,
    }
}

fn literal_cost(lit: &IRLiteral) -> u64 {
    match lit {
        IRLiteral::Bool(_) | IRLiteral::UInt8(_) | IRLiteral::UInt16(_) | IRLiteral::UInt32(_) => 0,
        _ => 1,
    }
}

// -- Hoisting analysis --------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HoistCandidate {
    pub(crate) var: VarId,
    pub(crate) cost: u64,
    pub(crate) class: ConstantClass,
    pub(crate) occurrence_count: u32,
}

#[must_use]
pub(crate) fn find_hoist_candidates(
    decl: &IRDecl,
    thresholds: &CostThresholds,
) -> Vec<HoistCandidate> {
    let mut expr_counts: HashMap<ExprFingerprint, (VarId, u64, ConstantClass, u32)> =
        HashMap::new();
    collect_hoistable_exprs(&decl.body, thresholds, &mut expr_counts);
    let mut candidates: Vec<_> = expr_counts
        .into_values()
        .filter(|(_, cost, _, _)| *cost >= thresholds.hoist_threshold)
        .map(|(var, cost, class, count)| HoistCandidate {
            var,
            cost,
            class,
            occurrence_count: count,
        })
        .collect();
    candidates.sort_by_key(|b| std::cmp::Reverse(b.cost));
    candidates
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ExprFingerprint {
    Ctor {
        name_hash: u64,
        tag: u32,
        arg_count: usize,
    },
    StringLit(String),
    LitBool(bool),
    LitU8(u8),
    LitU16(u16),
    LitU32(u32),
    LitU64(u64),
    LitUSize(u64),
    LitF64(u64),
    LitF32(u32),
    Apply {
        name_hash: u64,
        arg_count: usize,
    },
}

fn fingerprint_expr(expr: &IRExpr) -> Option<ExprFingerprint> {
    match expr {
        IRExpr::Ctor { info, args } => Some(ExprFingerprint::Ctor {
            name_hash: hash_name(&info.name.to_string()),
            tag: info.tag,
            arg_count: args.len(),
        }),
        IRExpr::String(s) => Some(ExprFingerprint::StringLit(s.clone())),
        IRExpr::Lit(IRLiteral::Bool(v)) => Some(ExprFingerprint::LitBool(*v)),
        IRExpr::Lit(IRLiteral::UInt8(v)) => Some(ExprFingerprint::LitU8(*v)),
        IRExpr::Lit(IRLiteral::UInt16(v)) => Some(ExprFingerprint::LitU16(*v)),
        IRExpr::Lit(IRLiteral::UInt32(v)) => Some(ExprFingerprint::LitU32(*v)),
        IRExpr::Lit(IRLiteral::UInt64(v)) => Some(ExprFingerprint::LitU64(*v)),
        IRExpr::Lit(IRLiteral::USize(v)) => Some(ExprFingerprint::LitUSize(*v as u64)),
        IRExpr::Lit(IRLiteral::Float64(v)) => Some(ExprFingerprint::LitF64(v.to_bits())),
        IRExpr::Lit(IRLiteral::Float32(v)) => Some(ExprFingerprint::LitF32(v.to_bits())),
        IRExpr::Apply { fn_id, args } => Some(ExprFingerprint::Apply {
            name_hash: hash_name(&fn_id.0.to_string()),
            arg_count: args.len(),
        }),
        _ => None,
    }
}

fn hash_name(s: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    s.hash(&mut h);
    h.finish()
}

fn collect_hoistable_exprs(
    body: &IRBody,
    thresholds: &CostThresholds,
    map: &mut HashMap<ExprFingerprint, (VarId, u64, ConstantClass, u32)>,
) {
    if let IRBody::VDecl { var, value, .. } = body {
        if let Some(fp) = fingerprint_expr(value) {
            let est = estimate_expr_cost(value, thresholds);
            map.entry(fp)
                .and_modify(|(_, _, _, c)| *c += 1)
                .or_insert((*var, est.cost, est.class, 1));
        }
    }
    for_each_child(body, |child| {
        collect_hoistable_exprs(child, thresholds, map)
    });
}

// -- Sharing detection --------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SharingOpportunity {
    pub(crate) canonical_var: VarId,
    pub(crate) duplicate_vars: Vec<VarId>,
    pub(crate) savings: u64,
    pub(crate) class: ConstantClass,
}

#[must_use]
pub(crate) fn find_sharing_opportunities(
    decl: &IRDecl,
    thresholds: &CostThresholds,
) -> Vec<SharingOpportunity> {
    let mut fps: HashMap<ExprFingerprint, Vec<(VarId, u64, ConstantClass)>> = HashMap::new();
    collect_shareable(&decl.body, thresholds, &mut fps);
    fps.into_values()
        .filter(|v| v.len() > 1)
        .map(|vars| {
            let (canonical_var, cost, class) = vars[0].clone();
            let duplicate_vars: Vec<VarId> = vars[1..].iter().map(|(v, _, _)| *v).collect();
            let savings = cost * duplicate_vars.len() as u64;
            SharingOpportunity {
                canonical_var,
                duplicate_vars,
                savings,
                class,
            }
        })
        .collect()
}

fn collect_shareable(
    body: &IRBody,
    thresholds: &CostThresholds,
    map: &mut HashMap<ExprFingerprint, Vec<(VarId, u64, ConstantClass)>>,
) {
    if let IRBody::VDecl { var, value, .. } = body {
        if let Some(fp) = fingerprint_expr(value) {
            let est = estimate_expr_cost(value, thresholds);
            if est.is_expensive {
                map.entry(fp).or_default().push((*var, est.cost, est.class));
            }
        }
    }
    for_each_child(body, |child| collect_shareable(child, thresholds, map));
}

// -- Boxing statistics --------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ExpensiveConstStats {
    pub(crate) total_constants: u32,
    pub(crate) expensive_count: u32,
    pub(crate) hoistable_count: u32,
    pub(crate) sharing_opportunities: u32,
    pub(crate) total_savings: u64,
    pub(crate) literals: u32,
    pub(crate) nullary_ctors: u32,
    pub(crate) compound_ctors: u32,
    pub(crate) string_lits: u32,
    pub(crate) function_apps: u32,
    pub(crate) recursive_exprs: u32,
}

impl ExpensiveConstStats {
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        format!(
            "total={} expensive={} hoistable={} sharing={} savings={} \
             lit={} nullary={} compound={} str={} app={} rec={}",
            self.total_constants,
            self.expensive_count,
            self.hoistable_count,
            self.sharing_opportunities,
            self.total_savings,
            self.literals,
            self.nullary_ctors,
            self.compound_ctors,
            self.string_lits,
            self.function_apps,
            self.recursive_exprs,
        )
    }
}

#[must_use]
pub(crate) fn collect_expensive_const_stats(
    decls: &[IRDecl],
    thresholds: &CostThresholds,
) -> ExpensiveConstStats {
    let mut stats = ExpensiveConstStats::default();
    for decl in decls {
        collect_stats_body(&decl.body, thresholds, &mut stats);
        let sharing = find_sharing_opportunities(decl, thresholds);
        stats.sharing_opportunities += sharing.len() as u32;
        stats.total_savings += sharing.iter().map(|s| s.savings).sum::<u64>();
    }
    stats
}

fn collect_stats_body(body: &IRBody, thresholds: &CostThresholds, stats: &mut ExpensiveConstStats) {
    if let IRBody::VDecl { value, .. } = body {
        let est = estimate_expr_cost(value, thresholds);
        stats.total_constants += 1;
        if est.is_expensive {
            stats.expensive_count += 1;
        }
        if est.is_hoistable {
            stats.hoistable_count += 1;
        }
        match &est.class {
            ConstantClass::Literal => stats.literals += 1,
            ConstantClass::NullaryCtor => stats.nullary_ctors += 1,
            ConstantClass::CompoundCtor { .. } => stats.compound_ctors += 1,
            ConstantClass::StringLit => stats.string_lits += 1,
            ConstantClass::FunctionApp => stats.function_apps += 1,
            ConstantClass::Recursive { .. } => stats.recursive_exprs += 1,
        }
    }
    for_each_child(body, |child| collect_stats_body(child, thresholds, stats));
}

// -- Impact report ------------------------------------------------------------

#[derive(Clone, Debug)]
pub(crate) struct ImpactEntry {
    pub(crate) var: VarId,
    pub(crate) class: ConstantClass,
    pub(crate) cost: u64,
    pub(crate) occurrences: u32,
    pub(crate) decision: BoxingDecisionKind,
    pub(crate) justification: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BoxingDecisionKind {
    LeaveInPlace,
    BoxAndCache,
    HoistAndShare,
}

#[derive(Clone, Debug)]
pub(crate) struct ImpactReport {
    pub(crate) fn_name: String,
    pub(crate) entries: Vec<ImpactEntry>,
    pub(crate) total_cost_before: u64,
    pub(crate) total_cost_after: u64,
}

impl ImpactReport {
    #[must_use]
    pub(crate) fn cost_reduction(&self) -> u64 {
        self.total_cost_before.saturating_sub(self.total_cost_after)
    }
}

#[must_use]
pub(crate) fn generate_impact_report(decl: &IRDecl, thresholds: &CostThresholds) -> ImpactReport {
    let mut expr_info: HashMap<ExprFingerprint, (VarId, u64, ConstantClass, u32)> = HashMap::new();
    collect_hoistable_exprs(&decl.body, thresholds, &mut expr_info);
    let mut total_before = 0u64;
    let mut total_after = 0u64;
    let mut entries = Vec::new();
    for (var, cost, class, count) in expr_info.values() {
        let full = *cost * (*count as u64);
        total_before += full;
        let (decision, after, justification) = if *cost < thresholds.expensive_threshold {
            (
                BoxingDecisionKind::LeaveInPlace,
                full,
                format!(
                    "cost {} below threshold {}",
                    cost, thresholds.expensive_threshold
                ),
            )
        } else if *count > 1 && *cost >= thresholds.hoist_threshold {
            (
                BoxingDecisionKind::HoistAndShare,
                *cost,
                format!(
                    "cost {} x {} = {}; hoist saves {}",
                    cost,
                    count,
                    full,
                    full.saturating_sub(*cost)
                ),
            )
        } else {
            (
                BoxingDecisionKind::BoxAndCache,
                *cost,
                format!(
                    "cost {} exceeds threshold {}; box once",
                    cost, thresholds.expensive_threshold
                ),
            )
        };
        total_after += after;
        entries.push(ImpactEntry {
            var: *var,
            class: class.clone(),
            cost: *cost,
            occurrences: *count,
            decision,
            justification,
        });
    }
    entries.sort_by_key(|b| std::cmp::Reverse(b.cost));
    ImpactReport {
        fn_name: decl.name.to_string(),
        entries,
        total_cost_before: total_before,
        total_cost_after: total_after,
    }
}

// -- Recursive depth estimation -----------------------------------------------

/// Estimate nesting depth of constructor arguments in a function body.
#[must_use]
pub(crate) fn estimate_recursive_depth(body: &IRBody) -> u32 {
    let mut ctor_vars: HashMap<VarId, u32> = HashMap::new();
    compute_depth(body, &mut ctor_vars);
    ctor_vars.values().copied().max().unwrap_or(0)
}

fn compute_depth(body: &IRBody, ctor_vars: &mut HashMap<VarId, u32>) {
    if let IRBody::VDecl {
        var,
        value: IRExpr::Ctor { args, .. },
        ..
    } = body
    {
        let d = args
            .iter()
            .filter_map(|a| match a {
                IRArg::Var(v) => ctor_vars.get(v).copied(),
                IRArg::Erased => None,
            })
            .max()
            .unwrap_or(0);
        ctor_vars.insert(*var, d + 1);
    }
    for_each_child(body, |child| compute_depth(child, ctor_vars));
}

// -- Utility ------------------------------------------------------------------

fn for_each_child(body: &IRBody, mut f: impl FnMut(&IRBody)) {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => f(rest),
        IRBody::JDecl { body, rest, .. } => {
            f(body);
            f(rest);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                f(&alt.body);
            }
            if let Some(d) = default {
                f(d);
            }
        }
        IRBody::Ret(_) | IRBody::Jmp { .. } | IRBody::Unreachable => {}
    }
}
