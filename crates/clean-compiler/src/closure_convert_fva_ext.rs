// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Free Variable Analysis for L5IR — Core Module
//!
//! Builds on `closure_convert_fva` with richer capture analysis:
//! - Capture classification (read-only, mutated, passed-to-closure, escapes)
//! - Capture minimization (unused captures)
//! - Sharing analysis (variables captured by multiple closures)
//! - Capture cost estimation (memory heuristics)
//!
//! See `closure_convert_fva_ext2` for lifetime, hierarchical, and stats.
//!
//! Part of #3084 - Runtime closure support.

use crate::ir::{IRArg, IRBody, IRExpr, IRType, VarId};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error Type
// ════════════════════════════════════════════════════════════════════════════

/// Errors from extended free variable analysis.
#[derive(Debug, Error)]
pub(crate) enum FvaExtError {
    #[error("no declarations to analyze")]
    EmptyDecls,
    #[error("variable {0:?} not found in scope")]
    VarNotInScope(VarId),
}

// ════════════════════════════════════════════════════════════════════════════
// Capture Classification
// ════════════════════════════════════════════════════════════════════════════

/// How a captured variable is used inside a closure body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CaptureUsage {
    /// Variable is only read (appears in expressions but never mutated).
    ReadOnly,
    /// Variable is mutated via Set/USet/SSet/SetTag.
    Mutated,
    /// Variable is passed as an argument to another PartialApply/ClosureApply.
    PassedToClosure,
    /// Variable escapes (returned, jumped to join point, or passed to Apply).
    Escapes,
}

/// Full classification of a single captured variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CaptureClassification {
    pub(crate) var: VarId,
    pub(crate) usages: HashSet<CaptureUsage>,
}

impl CaptureClassification {
    #[must_use]
    pub(crate) fn is_read_only(&self) -> bool {
        self.usages.len() == 1 && self.usages.contains(&CaptureUsage::ReadOnly)
    }

    #[must_use]
    pub(crate) fn is_unused(&self) -> bool {
        self.usages.is_empty()
    }
}

/// Classify captured variables by their usage patterns in `body`.
///
/// `free_vars` is the set of free variables (captures) to classify.
/// Returns one `CaptureClassification` per free variable.
#[must_use]
pub(crate) fn classify_captures(
    body: &IRBody,
    free_vars: &HashSet<VarId>,
) -> Vec<CaptureClassification> {
    let mut usage_map: HashMap<VarId, HashSet<CaptureUsage>> =
        free_vars.iter().map(|v| (*v, HashSet::new())).collect();
    collect_usages(body, free_vars, &mut usage_map);
    let mut result: Vec<CaptureClassification> = usage_map
        .into_iter()
        .map(|(var, usages)| CaptureClassification { var, usages })
        .collect();
    result.sort_by_key(|c| c.var.0);
    result
}

fn collect_usages(
    body: &IRBody,
    free_vars: &HashSet<VarId>,
    usages: &mut HashMap<VarId, HashSet<CaptureUsage>>,
) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_expr_usages(value, free_vars, usages);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_usages(jp_body, free_vars, usages);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::ReadOnly);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::Set {
            var, value, rest, ..
        } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::Mutated);
            mark_if_free(*value, free_vars, usages, CaptureUsage::ReadOnly);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::SetTag { var, rest, .. } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::Mutated);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::USet {
            var, value, rest, ..
        } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::Mutated);
            mark_if_free(*value, free_vars, usages, CaptureUsage::ReadOnly);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::SSet {
            var, value, rest, ..
        } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::Mutated);
            mark_if_free(*value, free_vars, usages, CaptureUsage::ReadOnly);
            collect_usages(rest, free_vars, usages);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            mark_if_free(*scrutinee, free_vars, usages, CaptureUsage::ReadOnly);
            for alt in alts {
                collect_usages(&alt.body, free_vars, usages);
            }
            if let Some(def) = default {
                collect_usages(def, free_vars, usages);
            }
        }
        IRBody::Jmp { args, .. } => {
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::Escapes);
            }
        }
        IRBody::Ret(arg) => {
            mark_arg_if_free(arg, free_vars, usages, CaptureUsage::Escapes);
        }
        IRBody::Unreachable => {}
    }
}

fn collect_expr_usages(
    expr: &IRExpr,
    free_vars: &HashSet<VarId>,
    usages: &mut HashMap<VarId, HashSet<CaptureUsage>>,
) {
    match expr {
        IRExpr::PartialApply { args, .. } => {
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::PassedToClosure);
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            mark_arg_if_free(closure, free_vars, usages, CaptureUsage::ReadOnly);
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::PassedToClosure);
            }
        }
        IRExpr::Apply { args, .. } => {
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::Escapes);
            }
        }
        IRExpr::Ctor { args, .. } => {
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::ReadOnly);
            }
        }
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            mark_arg_if_free(arg, free_vars, usages, CaptureUsage::ReadOnly);
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::ReadOnly);
        }
        IRExpr::Reuse { var, args, .. } => {
            mark_if_free(*var, free_vars, usages, CaptureUsage::ReadOnly);
            for arg in args {
                mark_arg_if_free(arg, free_vars, usages, CaptureUsage::ReadOnly);
            }
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}

fn mark_if_free(
    var: VarId,
    free_vars: &HashSet<VarId>,
    usages: &mut HashMap<VarId, HashSet<CaptureUsage>>,
    usage: CaptureUsage,
) {
    if free_vars.contains(&var) {
        usages.entry(var).or_default().insert(usage);
    }
}

fn mark_arg_if_free(
    arg: &IRArg,
    free_vars: &HashSet<VarId>,
    usages: &mut HashMap<VarId, HashSet<CaptureUsage>>,
    usage: CaptureUsage,
) {
    if let IRArg::Var(v) = arg {
        mark_if_free(*v, free_vars, usages, usage);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Capture Minimization
// ════════════════════════════════════════════════════════════════════════════

/// Detect variables that are captured (free) but never actually referenced
/// in `body`. These are redundant captures that waste environment slots.
#[must_use]
pub(crate) fn find_redundant_captures(body: &IRBody, free_vars: &HashSet<VarId>) -> Vec<VarId> {
    let classifications = classify_captures(body, free_vars);
    let mut redundant: Vec<VarId> = classifications
        .iter()
        .filter(|c| c.is_unused())
        .map(|c| c.var)
        .collect();
    redundant.sort_by_key(|v| v.0);
    redundant
}

/// Return the minimal capture set: free variables minus redundant ones.
#[must_use]
pub(crate) fn minimize_captures(body: &IRBody, free_vars: &HashSet<VarId>) -> HashSet<VarId> {
    let redundant: HashSet<VarId> = find_redundant_captures(body, free_vars)
        .into_iter()
        .collect();
    free_vars.difference(&redundant).copied().collect()
}

// ════════════════════════════════════════════════════════════════════════════
// Sharing Analysis
// ════════════════════════════════════════════════════════════════════════════

/// A sharing point: a variable captured by multiple closures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SharingPoint {
    pub(crate) var: VarId,
    /// Labels of closures that capture this variable (`"pa@<var_id>"`).
    pub(crate) closure_sites: Vec<String>,
}

/// Find variables captured by multiple PartialApply sites.
#[must_use]
pub(crate) fn find_sharing_points(body: &IRBody) -> Vec<SharingPoint> {
    let mut var_to_sites: HashMap<VarId, Vec<String>> = HashMap::new();
    collect_pa_captures(body, &mut var_to_sites);
    let mut points: Vec<SharingPoint> = var_to_sites
        .into_iter()
        .filter(|(_, sites)| sites.len() > 1)
        .map(|(var, closure_sites)| SharingPoint { var, closure_sites })
        .collect();
    points.sort_by_key(|p| p.var.0);
    points
}

fn collect_pa_captures(body: &IRBody, out: &mut HashMap<VarId, Vec<String>>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::PartialApply { args, .. } = value {
                let label = format!("pa@{}", var.0);
                for arg in args {
                    if let IRArg::Var(v) = arg {
                        out.entry(*v).or_default().push(label.clone());
                    }
                }
            }
            collect_pa_captures(rest, out);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_pa_captures(jp, out);
            collect_pa_captures(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_pa_captures(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_pa_captures(&alt.body, out);
            }
            if let Some(def) = default {
                collect_pa_captures(def, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Capture Cost Estimation
// ════════════════════════════════════════════════════════════════════════════

/// Estimated memory cost (in bytes) of capturing a variable by type.
///
/// Object types cost a pointer (8 bytes on 64-bit). Scalar types cost
/// their `scalar_byte_size()`. Erased/Void cost 0.
#[must_use]
pub(crate) fn capture_cost(ty: &IRType) -> u64 {
    match ty {
        IRType::Object | IRType::TObject | IRType::Struct(_) | IRType::Union(_) => 8,
        _ if ty.is_scalar() => u64::from(ty.scalar_byte_size()),
        IRType::Erased | IRType::Void => 0,
        _ => 0,
    }
}

/// Estimate total capture cost for a set of variables with known types.
#[must_use]
pub(crate) fn total_capture_cost(vars: &HashSet<VarId>, type_env: &HashMap<VarId, IRType>) -> u64 {
    vars.iter()
        .map(|v| type_env.get(v).map(capture_cost).unwrap_or(8))
        .sum()
}
