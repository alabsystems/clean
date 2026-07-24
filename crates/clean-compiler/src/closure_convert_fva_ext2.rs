// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Free Variable Analysis for L5IR — Part 2
//!
//! Higher-level analyses built on `closure_convert_fva_ext`:
//! - Lifetime estimation (short-lived vs long-lived)
//! - Hierarchical capture tracking (nested capture chains)
//! - Aggregate FVA statistics
//!
//! Part of #3084 - Runtime closure support.

use crate::closure_convert_fva::{bound_from_params, free_vars_body};
use crate::closure_convert_fva_ext::{
    classify_captures, find_redundant_captures, find_sharing_points, total_capture_cost,
    CaptureUsage, FvaExtError,
};
use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use std::collections::{HashMap, HashSet};

// ════════════════════════════════════════════════════════════════════════════
// Lifetime Analysis
// ════════════════════════════════════════════════════════════════════════════

/// Estimated capture lifetime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CaptureLifetime {
    /// Used only within a single branch or before the first control split.
    ShortLived,
    /// Used across branches or returned/escaped.
    LongLived,
}

/// Estimate the lifetime of each captured variable in `body`.
///
/// A capture is `LongLived` if it escapes or is used across case branches.
/// Otherwise it is `ShortLived`.
#[must_use]
pub(crate) fn estimate_capture_lifetimes(
    body: &IRBody,
    free_vars: &HashSet<VarId>,
) -> Vec<(VarId, CaptureLifetime)> {
    let classifications = classify_captures(body, free_vars);
    let case_vars = vars_used_across_branches(body, free_vars);
    let mut result: Vec<(VarId, CaptureLifetime)> = classifications
        .iter()
        .map(|c| {
            let lt = if c.usages.contains(&CaptureUsage::Escapes) || case_vars.contains(&c.var) {
                CaptureLifetime::LongLived
            } else {
                CaptureLifetime::ShortLived
            };
            (c.var, lt)
        })
        .collect();
    result.sort_by_key(|(v, _)| v.0);
    result
}

/// Collect free vars that appear in more than one case branch.
fn vars_used_across_branches(body: &IRBody, free_vars: &HashSet<VarId>) -> HashSet<VarId> {
    let mut multi_branch = HashSet::new();
    collect_multi_branch_vars(body, free_vars, &mut multi_branch);
    multi_branch
}

fn collect_multi_branch_vars(body: &IRBody, free_vars: &HashSet<VarId>, out: &mut HashSet<VarId>) {
    match body {
        IRBody::Case { alts, default, .. } => {
            let mut branch_var_sets: Vec<HashSet<VarId>> = Vec::new();
            for alt in alts {
                let bound_empty = HashSet::new();
                let fv = free_vars_body(&alt.body, &bound_empty);
                let intersection: HashSet<VarId> = fv.intersection(free_vars).copied().collect();
                branch_var_sets.push(intersection);
                collect_multi_branch_vars(&alt.body, free_vars, out);
            }
            if let Some(def) = default {
                let bound_empty = HashSet::new();
                let fv = free_vars_body(def, &bound_empty);
                let intersection: HashSet<VarId> = fv.intersection(free_vars).copied().collect();
                branch_var_sets.push(intersection);
                collect_multi_branch_vars(def, free_vars, out);
            }
            let mut seen = HashSet::new();
            for set in &branch_var_sets {
                for v in set {
                    if !seen.insert(*v) {
                        out.insert(*v);
                    }
                }
            }
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_multi_branch_vars(rest, free_vars, out);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_multi_branch_vars(jp_body, free_vars, out);
            collect_multi_branch_vars(rest, free_vars, out);
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Hierarchical Capture Tracking
// ════════════════════════════════════════════════════════════════════════════

/// A chain of nested captures: `source_fn -> closure_a -> closure_b -> var`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CaptureChain {
    /// The original variable being captured.
    pub(crate) var: VarId,
    /// Nesting depth (1 = direct, 2 = through one intermediate, etc.).
    pub(crate) depth: u32,
    /// VarIds of intermediate closure result variables.
    pub(crate) intermediaries: Vec<VarId>,
}

/// Analyze hierarchical capture chains across multiple declarations.
#[must_use]
pub(crate) fn find_capture_chains(decls: &[IRDecl]) -> Vec<CaptureChain> {
    let mut chains = Vec::new();
    for decl in decls {
        let pa_results = collect_pa_results(&decl.body);
        find_chains_in_body(&decl.body, &pa_results, &mut chains);
    }
    chains.sort_by_key(|c| (c.var.0, c.depth));
    chains
}

fn collect_pa_results(body: &IRBody) -> HashSet<VarId> {
    let mut results = HashSet::new();
    collect_pa_results_inner(body, &mut results);
    results
}

fn collect_pa_results_inner(body: &IRBody, results: &mut HashSet<VarId>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if matches!(value, IRExpr::PartialApply { .. }) {
                results.insert(*var);
            }
            collect_pa_results_inner(rest, results);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_pa_results_inner(jp, results);
            collect_pa_results_inner(rest, results);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_pa_results_inner(rest, results);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_pa_results_inner(&alt.body, results);
            }
            if let Some(def) = default {
                collect_pa_results_inner(def, results);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn find_chains_in_body(body: &IRBody, pa_results: &HashSet<VarId>, chains: &mut Vec<CaptureChain>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::PartialApply { args, .. } = value {
                for arg in args {
                    if let IRArg::Var(v) = arg {
                        if pa_results.contains(v) {
                            let mut intermediaries = vec![*v];
                            let mut depth = 2u32;
                            let further = find_transitive_captures(rest, *v, pa_results);
                            for fv in &further {
                                intermediaries.push(*fv);
                                depth += 1;
                            }
                            chains.push(CaptureChain {
                                var: *v,
                                depth,
                                intermediaries,
                            });
                        } else {
                            chains.push(CaptureChain {
                                var: *v,
                                depth: 1,
                                intermediaries: vec![],
                            });
                        }
                    }
                }
            }
            find_chains_in_body(rest, pa_results, chains);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            find_chains_in_body(jp, pa_results, chains);
            find_chains_in_body(rest, pa_results, chains);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            find_chains_in_body(rest, pa_results, chains);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                find_chains_in_body(&alt.body, pa_results, chains);
            }
            if let Some(def) = default {
                find_chains_in_body(def, pa_results, chains);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn find_transitive_captures(
    body: &IRBody,
    target: VarId,
    pa_results: &HashSet<VarId>,
) -> Vec<VarId> {
    let mut result = Vec::new();
    find_transitive_inner(body, target, pa_results, &mut result);
    result
}

fn find_transitive_inner(
    body: &IRBody,
    target: VarId,
    pa_results: &HashSet<VarId>,
    out: &mut Vec<VarId>,
) {
    if let IRBody::VDecl {
        var, value, rest, ..
    } = body
    {
        if *var == target {
            if let IRExpr::PartialApply { args, .. } = value {
                for arg in args {
                    if let IRArg::Var(v) = arg {
                        if pa_results.contains(v) {
                            out.push(*v);
                        }
                    }
                }
            }
            return;
        }
        find_transitive_inner(rest, target, pa_results, out);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// FVA Statistics
// ════════════════════════════════════════════════════════════════════════════

/// Aggregate statistics from free variable analysis across declarations.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FvaStats {
    pub(crate) decl_count: usize,
    pub(crate) total_free_var_sets: usize,
    pub(crate) avg_captures_per_closure: f64,
    pub(crate) max_capture_depth: u32,
    pub(crate) sharing_ratio: f64,
    pub(crate) total_cost_bytes: u64,
    pub(crate) redundant_captures: usize,
}

/// Collect comprehensive FVA statistics across a set of declarations.
pub(crate) fn compute_fva_stats(
    decls: &[IRDecl],
    type_env: &HashMap<VarId, IRType>,
) -> Result<FvaStats, FvaExtError> {
    if decls.is_empty() {
        return Err(FvaExtError::EmptyDecls);
    }

    let mut total_captures: usize = 0;
    let mut closure_count: usize = 0;
    let mut all_captured_vars: HashSet<VarId> = HashSet::new();
    let mut redundant_count: usize = 0;
    let mut total_cost: u64 = 0;

    for decl in decls {
        let bound = bound_from_params(decl);
        let fv = free_vars_body(&decl.body, &bound);
        if fv.is_empty() {
            continue;
        }
        closure_count += 1;
        total_captures += fv.len();
        all_captured_vars.extend(&fv);
        redundant_count += find_redundant_captures(&decl.body, &fv).len();
        total_cost += total_capture_cost(&fv, type_env);
    }

    let max_depth = find_capture_chains(decls)
        .iter()
        .map(|c| c.depth)
        .max()
        .unwrap_or(0);

    let sharing_points = decls
        .iter()
        .flat_map(|d| find_sharing_points(&d.body))
        .count();
    let total_unique = all_captured_vars.len();
    let sharing_ratio = if total_unique > 0 {
        sharing_points as f64 / total_unique as f64
    } else {
        0.0
    };
    let avg = if closure_count > 0 {
        total_captures as f64 / closure_count as f64
    } else {
        0.0
    };

    Ok(FvaStats {
        decl_count: decls.len(),
        total_free_var_sets: closure_count,
        avg_captures_per_closure: avg,
        max_capture_depth: max_depth,
        sharing_ratio,
        total_cost_bytes: total_cost,
        redundant_captures: redundant_count,
    })
}
