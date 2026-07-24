// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended boxing analysis for L5IR.
//!
//! Provides cross-function boxing propagation, polymorphic boxing analysis,
//! cost estimation, redundant box/unbox elimination, and shared boxing
//! optimization on top of the core boxing pass.
//!
//! Part of #3083 - Compiler extensibility infrastructure.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};

/// Apply `f` to every child `IRBody` of `body` (non-recursive).
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

// ---------------------------------------------------------------------------
// Boxing insertion analysis
// ---------------------------------------------------------------------------

/// Describes where a box or unbox operation is needed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BoxingSite {
    BoxScalar { var: VarId, ty: IRType },
    UnboxObject { var: VarId, target_ty: IRType },
}

/// Scan a function body for sites requiring box/unbox insertion.
#[must_use]
pub(crate) fn analyze_boxing_sites(decl: &IRDecl) -> Vec<BoxingSite> {
    let mut sites = Vec::new();
    collect_sites(&decl.body, &mut sites);
    sites
}

fn collect_sites(body: &IRBody, sites: &mut Vec<BoxingSite>) {
    if let IRBody::VDecl { var, value, .. } = body {
        match value {
            IRExpr::Box { ty: scalar_ty, .. } => sites.push(BoxingSite::BoxScalar {
                var: *var,
                ty: scalar_ty.clone(),
            }),
            IRExpr::Unbox { ty: target_ty, .. } => sites.push(BoxingSite::UnboxObject {
                var: *var,
                target_ty: target_ty.clone(),
            }),
            _ => {}
        }
    }
    for_each_child(body, |child| collect_sites(child, sites));
}

// ---------------------------------------------------------------------------
// Cross-function boxing propagation
// ---------------------------------------------------------------------------

/// Per-function boxing summary used for inter-procedural propagation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FunctionBoxingSummary {
    pub(crate) fn_id: FnId,
    pub(crate) boxed_params: Vec<bool>,
    pub(crate) returns_boxed: bool,
}

/// Build per-function boxing summaries for a set of declarations.
#[must_use]
pub(crate) fn build_boxing_summaries(decls: &[IRDecl]) -> Vec<FunctionBoxingSummary> {
    decls
        .iter()
        .map(|d| FunctionBoxingSummary {
            fn_id: FnId(d.name.clone()),
            boxed_params: d.params.iter().map(|(_, ty)| ty.is_object()).collect(),
            returns_boxed: d.return_type.is_object(),
        })
        .collect()
}

/// Propagate boxing requirements across call edges.
#[must_use]
pub(crate) fn propagate_boxing(
    decls: &[IRDecl],
    summaries: &[FunctionBoxingSummary],
) -> Vec<FunctionBoxingSummary> {
    let index: HashMap<&Name, &FunctionBoxingSummary> =
        summaries.iter().map(|s| (&s.fn_id.0, s)).collect();
    decls
        .iter()
        .map(|d| {
            let mut bp: Vec<bool> = d.params.iter().map(|(_, ty)| ty.is_object()).collect();
            propagate_body(&d.body, &d.params, &index, &mut bp);
            FunctionBoxingSummary {
                fn_id: FnId(d.name.clone()),
                boxed_params: bp,
                returns_boxed: d.return_type.is_object(),
            }
        })
        .collect()
}

fn propagate_body(
    body: &IRBody,
    params: &[(VarId, IRType)],
    index: &HashMap<&Name, &FunctionBoxingSummary>,
    bp: &mut [bool],
) {
    if let IRBody::VDecl {
        value: IRExpr::Apply { fn_id, args },
        ..
    } = body
    {
        if let Some(callee) = index.get(&fn_id.0) {
            for (i, arg) in args.iter().enumerate() {
                if i < callee.boxed_params.len() && callee.boxed_params[i] {
                    if let IRArg::Var(v) = arg {
                        if let Some(pi) = params.iter().position(|(pv, _)| pv == v) {
                            bp[pi] = true;
                        }
                    }
                }
            }
        }
    }
    for_each_child(body, |child| propagate_body(child, params, index, bp));
}

// ---------------------------------------------------------------------------
// Polymorphic boxing
// ---------------------------------------------------------------------------

/// Determine the boxing strategy for a polymorphic/erased type.
#[must_use]
pub(crate) fn polymorphic_boxing_type(ty: &IRType) -> IRType {
    match ty {
        IRType::Erased => IRType::Object,
        IRType::Void => IRType::Void,
        other if other.is_scalar() => other.boxed(),
        other => other.clone(),
    }
}

/// Check whether a function has polymorphic parameters requiring boxing.
#[must_use]
pub(crate) fn has_polymorphic_params(decl: &IRDecl) -> bool {
    decl.params
        .iter()
        .any(|(_, ty)| matches!(ty, IRType::Erased))
}

// ---------------------------------------------------------------------------
// Boxing cost analysis
// ---------------------------------------------------------------------------

/// Estimated cost of boxing operations in a function.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BoxingCost {
    pub(crate) box_count: u32,
    pub(crate) unbox_count: u32,
    pub(crate) redundant_pairs: u32,
}

impl BoxingCost {
    /// Total estimated instruction overhead (box costs 2, unbox costs 1).
    #[must_use]
    pub(crate) fn total_overhead(&self) -> u32 {
        self.box_count * 2 + self.unbox_count
    }

    /// Overhead after redundant pair elimination.
    #[must_use]
    pub(crate) fn net_overhead(&self) -> u32 {
        self.total_overhead()
            .saturating_sub(self.redundant_pairs * 3)
    }
}

/// Estimate boxing cost for a declaration.
#[must_use]
pub(crate) fn estimate_boxing_cost(decl: &IRDecl) -> BoxingCost {
    let mut cost = BoxingCost::default();
    count_boxing_ops(&decl.body, &mut cost);
    cost.redundant_pairs = count_redundant_pairs(&decl.body);
    cost
}

fn count_boxing_ops(body: &IRBody, cost: &mut BoxingCost) {
    if let IRBody::VDecl { value, .. } = body {
        match value {
            IRExpr::Box { .. } => cost.box_count += 1,
            IRExpr::Unbox { .. } => cost.unbox_count += 1,
            _ => {}
        }
    }
    for_each_child(body, |child| count_boxing_ops(child, cost));
}

// ---------------------------------------------------------------------------
// Boxing elimination — remove redundant box-then-unbox pairs
// ---------------------------------------------------------------------------

fn count_redundant_pairs(body: &IRBody) -> u32 {
    let mut boxed: HashMap<VarId, (IRType, IRArg)> = HashMap::new();
    let mut count = 0u32;
    count_pairs_inner(body, &mut boxed, &mut count);
    count
}

fn count_pairs_inner(body: &IRBody, boxed: &mut HashMap<VarId, (IRType, IRArg)>, count: &mut u32) {
    if let IRBody::VDecl { var, value, .. } = body {
        if let IRExpr::Box { ty, arg } = value {
            boxed.insert(*var, (ty.clone(), arg.clone()));
        }
        if let IRExpr::Unbox {
            ty,
            arg: IRArg::Var(src),
        } = value
        {
            if let Some((box_ty, _)) = boxed.get(src) {
                if box_ty == ty {
                    *count += 1;
                }
            }
        }
    }
    for_each_child(body, |child| count_pairs_inner(child, boxed, count));
}

/// Eliminate redundant box-then-unbox pairs in an IR body.
///
/// Rewrites `let v1 = box(ty, x); ... let v2 = unbox(ty, v1)` so that
/// the unbox reads directly from the original source variable.
#[must_use]
pub(crate) fn eliminate_redundant_boxing(body: &IRBody) -> IRBody {
    let mut boxed: HashMap<VarId, (IRType, IRArg)> = HashMap::new();
    elim_inner(body, &mut boxed)
}

fn elim_inner(body: &IRBody, boxed: &mut HashMap<VarId, (IRType, IRArg)>) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Box { ty: bt, arg: ba } = value {
                boxed.insert(*var, (bt.clone(), ba.clone()));
            }
            let new_value = match value {
                IRExpr::Unbox {
                    ty: ut,
                    arg: IRArg::Var(src),
                } => boxed.get(src).cloned().and_then(|(bt, orig)| {
                    if &bt == ut {
                        match orig {
                            IRArg::Var(ov) => Some(IRExpr::Unbox {
                                ty: ut.clone(),
                                arg: IRArg::Var(ov),
                            }),
                            IRArg::Erased => None,
                        }
                    } else {
                        None
                    }
                }),
                _ => None,
            };
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: new_value.unwrap_or_else(|| value.clone()),
                rest: Box::new(elim_inner(rest, boxed)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: b,
            rest,
        } => IRBody::JDecl {
            jp: *jp,
            params: params.clone(),
            body: Box::new(elim_inner(b, boxed)),
            rest: Box::new(elim_inner(rest, boxed)),
        },
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(elim_inner(rest, boxed)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(elim_inner(rest, boxed)),
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
                    body: Box::new(elim_inner(&a.body, boxed)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(elim_inner(d, boxed))),
        },
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Shared boxing optimisation
// ---------------------------------------------------------------------------

/// Identify variables boxed from the same source that could share a single
/// boxed representation.
#[must_use]
pub(crate) fn find_shared_boxing_opportunities(body: &IRBody) -> Vec<(VarId, VarId)> {
    let mut srcs: HashMap<(IRType, VarId), Vec<VarId>> = HashMap::new();
    collect_box_sources(body, &mut srcs);
    srcs.values()
        .filter(|vs| vs.len() > 1)
        .flat_map(|vs| vs[1..].iter().map(move |v| (vs[0], *v)))
        .collect()
}

fn collect_box_sources(body: &IRBody, map: &mut HashMap<(IRType, VarId), Vec<VarId>>) {
    if let IRBody::VDecl {
        var,
        value: IRExpr::Box {
            ty,
            arg: IRArg::Var(src),
        },
        ..
    } = body
    {
        map.entry((ty.clone(), *src)).or_default().push(*var);
    }
    for_each_child(body, |child| collect_box_sources(child, map));
}

// ---------------------------------------------------------------------------
// Boxing statistics
// ---------------------------------------------------------------------------

/// Aggregate boxing statistics for a module.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct BoxingStats {
    pub(crate) total_functions: u32,
    pub(crate) functions_with_boxing: u32,
    pub(crate) total_box_ops: u32,
    pub(crate) total_unbox_ops: u32,
    pub(crate) total_redundant_pairs: u32,
    pub(crate) total_shared_opportunities: u32,
    pub(crate) polymorphic_functions: u32,
}

impl BoxingStats {
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        format!(
            "funcs={}/{} box={} unbox={} redundant={} shared={} poly={}",
            self.functions_with_boxing,
            self.total_functions,
            self.total_box_ops,
            self.total_unbox_ops,
            self.total_redundant_pairs,
            self.total_shared_opportunities,
            self.polymorphic_functions,
        )
    }
}

/// Collect boxing statistics across a set of declarations.
#[must_use]
pub(crate) fn collect_boxing_stats(decls: &[IRDecl]) -> BoxingStats {
    let mut stats = BoxingStats {
        total_functions: decls.len() as u32,
        ..Default::default()
    };
    for decl in decls {
        let cost = estimate_boxing_cost(decl);
        if cost.box_count > 0 || cost.unbox_count > 0 {
            stats.functions_with_boxing += 1;
        }
        stats.total_box_ops += cost.box_count;
        stats.total_unbox_ops += cost.unbox_count;
        stats.total_redundant_pairs += cost.redundant_pairs;
        stats.total_shared_opportunities +=
            find_shared_boxing_opportunities(&decl.body).len() as u32;
        if has_polymorphic_params(decl) {
            stats.polymorphic_functions += 1;
        }
    }
    stats
}

// ---------------------------------------------------------------------------
// RC compatibility check
// ---------------------------------------------------------------------------

/// Verify that boxing decisions are compatible with reference counting.
///
/// Returns `(function_name, issue)` pairs where RC ops target scalar vars.
#[must_use]
pub(crate) fn check_rc_compatibility(decls: &[IRDecl]) -> Vec<(Name, String)> {
    let mut issues = Vec::new();
    for decl in decls {
        let mut vt: HashMap<VarId, IRType> = decl.params.iter().cloned().collect();
        check_rc_body(&decl.body, &mut vt, &decl.name, &mut issues);
    }
    issues
}

fn check_rc_body(
    body: &IRBody,
    vt: &mut HashMap<VarId, IRType>,
    name: &Name,
    issues: &mut Vec<(Name, String)>,
) {
    match body {
        IRBody::VDecl { var, ty, .. } => {
            vt.insert(*var, ty.clone());
        }
        IRBody::JDecl { params, .. } => {
            for (v, ty) in params {
                vt.insert(*v, ty.clone());
            }
        }
        IRBody::Inc { var, .. } | IRBody::Dec { var, .. } => {
            if let Some(ty) = vt.get(var) {
                if ty.is_scalar() {
                    let op = if matches!(body, IRBody::Inc { .. }) {
                        "inc"
                    } else {
                        "dec"
                    };
                    issues.push((
                        name.clone(),
                        format!("{} on scalar {:?} ({:?})", op, var, ty),
                    ));
                }
            }
        }
        _ => {}
    }
    for_each_child(body, |child| check_rc_body(child, vt, name, issues));
}

// ---------------------------------------------------------------------------
// Extended boxing config
// ---------------------------------------------------------------------------

/// Configuration for extended boxing analysis.
#[derive(Clone, Debug)]
pub(crate) struct BoxingExtConfig {
    pub(crate) propagate_across_calls: bool,
    pub(crate) eliminate_redundant: bool,
    pub(crate) shared_boxing: bool,
    pub(crate) max_propagation_iters: u32,
}

impl Default for BoxingExtConfig {
    fn default() -> Self {
        Self {
            propagate_across_calls: true,
            eliminate_redundant: true,
            shared_boxing: true,
            max_propagation_iters: 10,
        }
    }
}
