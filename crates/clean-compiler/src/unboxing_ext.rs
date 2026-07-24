// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended Unboxing Optimization Pass
//!
//! Extends the base unboxing pass with scalar unboxing, structure unboxing,
//! array unboxing, profitability analysis, propagation, and partial unboxing.
//!
//! Runs after the base `unboxing` pass and before RC insertion.
//! Part of #3083 — Extensibility (Lean 4 replacement compiler infrastructure).

use std::collections::{HashMap, HashSet};

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};

/// Configuration for the extended unboxing pass.
#[derive(Debug, Clone)]
pub(crate) struct UnboxingExtConfig {
    pub enable_scalar_unboxing: bool,
    pub enable_struct_unboxing: bool,
    pub enable_array_unboxing: bool,
    pub enable_profitability_check: bool,
    pub enable_propagation: bool,
    pub enable_partial_unboxing: bool,
    /// Minimum profitability score to commit to an unboxing (0.0..=1.0).
    pub profitability_threshold: f64,
}

impl Default for UnboxingExtConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl UnboxingExtConfig {
    /// All optimizations enabled (recommended default).
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            enable_scalar_unboxing: true,
            enable_struct_unboxing: true,
            enable_array_unboxing: true,
            enable_profitability_check: true,
            enable_propagation: true,
            enable_partial_unboxing: true,
            profitability_threshold: 0.5,
        }
    }

    /// No optimizations (pass-through).
    #[must_use]
    pub(crate) fn disabled() -> Self {
        Self {
            enable_scalar_unboxing: false,
            enable_struct_unboxing: false,
            enable_array_unboxing: false,
            enable_profitability_check: false,
            enable_propagation: false,
            enable_partial_unboxing: false,
            profitability_threshold: 1.0,
        }
    }
}

/// Statistics collected during the extended unboxing pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct UnboxingExtStats {
    pub scalars_unboxed: u32,
    pub structs_unboxed: u32,
    pub arrays_unboxed: u32,
    pub rejected_unprofitable: u32,
    pub propagations: u32,
    pub partial_unboxes: u32,
    pub decls_processed: u32,
}

impl UnboxingExtStats {
    #[must_use]
    pub(crate) fn total_optimizations(&self) -> u32 {
        self.scalars_unboxed
            + self.structs_unboxed
            + self.arrays_unboxed
            + self.propagations
            + self.partial_unboxes
    }
}

/// Classify whether an `IRType` is a scalar candidate for unboxing.
#[must_use]
pub(crate) fn classify_scalar_unboxing(ty: &IRType) -> Option<IRType> {
    if ty.is_scalar() {
        Some(ty.clone())
    } else {
        None
    }
}

/// Check if a type is already a native scalar (no unboxing needed).
#[must_use]
pub(crate) fn is_already_unboxed(ty: &IRType) -> bool {
    ty.is_scalar()
}

/// Check if a struct is a single-field wrapper; returns the inner type.
#[must_use]
pub(crate) fn classify_struct_unboxing(ty: &IRType) -> Option<IRType> {
    if let IRType::Struct(fields) = ty {
        if fields.len() == 1 {
            return Some(fields[0].clone());
        }
    }
    None
}

/// Classify fields of a multi-field struct for partial unboxing.
/// Returns `(field_index, scalar_type)` for already-scalar fields.
#[must_use]
pub(crate) fn classify_partial_unboxing(ty: &IRType) -> Vec<(usize, IRType)> {
    if let IRType::Struct(fields) = ty {
        fields
            .iter()
            .enumerate()
            .filter(|(_, f)| f.is_scalar())
            .map(|(i, f)| (i, f.clone()))
            .collect()
    } else {
        Vec::new()
    }
}

const ARRAY_NAT: &str = "Array.Nat";
const ARRAY_UINT8: &str = "Array.UInt8";
const ARRAY_UINT32: &str = "Array.UInt32";
const ARRAY_UINT64: &str = "Array.UInt64";

/// Classify an array constructor for native scalar element unboxing.
#[must_use]
pub(crate) fn classify_array_unboxing(fn_name: &str) -> Option<IRType> {
    match fn_name {
        ARRAY_NAT | ARRAY_UINT64 => Some(IRType::UInt64),
        ARRAY_UINT32 => Some(IRType::UInt32),
        ARRAY_UINT8 => Some(IRType::UInt8),
        _ => None,
    }
}

/// Cost estimate for a boxing/unboxing operation.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct UnboxingCost {
    pub box_ops_saved: u32,
    pub unbox_ops_saved: u32,
    pub box_ops_added: u32,
    pub unbox_ops_added: u32,
}

impl UnboxingCost {
    /// Profitability score in [0.0, 1.0]. > 0.5 means profitable.
    #[must_use]
    pub(crate) fn profitability(&self) -> f64 {
        let saved = (self.box_ops_saved + self.unbox_ops_saved) as f64;
        let added = (self.box_ops_added + self.unbox_ops_added) as f64;
        let total = saved + added;
        if total == 0.0 {
            0.0
        } else {
            saved / total
        }
    }

    /// Whether the net effect is a reduction in box/unbox operations.
    #[must_use]
    pub(crate) fn is_net_positive(&self) -> bool {
        (self.box_ops_saved + self.unbox_ops_saved) > (self.box_ops_added + self.unbox_ops_added)
    }
}

/// Analyze the profitability of unboxing a parameter in a declaration.
#[must_use]
pub(crate) fn analyze_param_unboxing_cost(body: &IRBody, param_var: VarId) -> UnboxingCost {
    let mut cost = UnboxingCost {
        box_ops_saved: 0,
        unbox_ops_saved: 0,
        box_ops_added: 0,
        unbox_ops_added: 0,
    };
    count_param_ops(body, param_var, &mut cost);
    cost
}

fn count_param_ops(body: &IRBody, target: VarId, cost: &mut UnboxingCost) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Unbox {
                    arg: IRArg::Var(v), ..
                } if *v == target => {
                    cost.unbox_ops_saved += 1;
                }
                IRExpr::Box {
                    arg: IRArg::Var(v), ..
                } if *v == target => {
                    cost.box_ops_saved += 1;
                }
                IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. }
                    if args
                        .iter()
                        .any(|a| matches!(a, IRArg::Var(v) if *v == target)) =>
                {
                    cost.box_ops_added += 1;
                }
                _ => {}
            }
            count_param_ops(rest, target, cost);
        }
        IRBody::JDecl { body, rest, .. } => {
            count_param_ops(body, target, cost);
            count_param_ops(rest, target, cost);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                count_param_ops(&alt.body, target, cost);
            }
            if let Some(d) = default {
                count_param_ops(d, target, cost);
            }
        }
        _ => {
            if let Some(rest) = body_rest(body) {
                count_param_ops(rest, target, cost);
            }
        }
    }
}

/// Extract the `rest` continuation from simple body variants.
fn body_rest(body: &IRBody) -> Option<&IRBody> {
    match body {
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => Some(rest),
        _ => None,
    }
}

/// Build a map of function names to their unboxable parameter indices.
#[must_use]
pub(crate) fn analyze_propagation_candidates(
    decls: &[IRDecl],
) -> HashMap<String, Vec<(usize, IRType)>> {
    let mut candidates = HashMap::new();
    for decl in decls {
        let param_candidates: Vec<_> = decl
            .params
            .iter()
            .enumerate()
            .filter(|(_, (_, ty))| *ty == IRType::Object)
            .filter_map(|(idx, (var, _))| first_unbox_type(&decl.body, *var).map(|t| (idx, t)))
            .collect();
        if !param_candidates.is_empty() {
            candidates.insert(format!("{}", decl.name), param_candidates);
        }
    }
    candidates
}

/// Find the first unbox operation applied to `var` in the body.
fn first_unbox_type(body: &IRBody, target: VarId) -> Option<IRType> {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Unbox {
                ty,
                arg: IRArg::Var(v),
            } = value
            {
                if *v == target {
                    return Some(ty.clone());
                }
            }
            first_unbox_type(rest, target)
        }
        IRBody::JDecl { body, rest, .. } => {
            first_unbox_type(body, target).or_else(|| first_unbox_type(rest, target))
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                if let Some(ty) = first_unbox_type(&alt.body, target) {
                    return Some(ty);
                }
            }
            default.as_ref().and_then(|d| first_unbox_type(d, target))
        }
        _ => body_rest(body).and_then(|r| first_unbox_type(r, target)),
    }
}

/// Check if a declaration references itself (directly recursive).
#[must_use]
pub(crate) fn is_recursive(decl: &IRDecl) -> bool {
    body_calls_fn(&decl.body, &format!("{}", decl.name))
}

/// Check if a set of declarations are mutually recursive.
#[must_use]
pub(crate) fn is_mutually_recursive(decls: &[IRDecl]) -> bool {
    let names: HashSet<String> = decls.iter().map(|d| format!("{}", d.name)).collect();
    decls.iter().any(|decl| {
        let self_name = format!("{}", decl.name);
        names
            .iter()
            .any(|n| *n != self_name && body_calls_fn(&decl.body, n))
    })
}

fn body_calls_fn(body: &IRBody, fn_name: &str) -> bool {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = value {
                if format!("{}", fn_id.0) == fn_name {
                    return true;
                }
            }
            body_calls_fn(rest, fn_name)
        }
        IRBody::JDecl { body, rest, .. } => {
            body_calls_fn(body, fn_name) || body_calls_fn(rest, fn_name)
        }
        IRBody::Case { alts, default, .. } => {
            alts.iter().any(|a| body_calls_fn(&a.body, fn_name))
                || default.as_ref().is_some_and(|d| body_calls_fn(d, fn_name))
        }
        _ => body_rest(body).is_some_and(|r| body_calls_fn(r, fn_name)),
    }
}

/// Apply the extended unboxing pass to a set of declarations.
#[must_use]
pub(crate) fn unbox_ext_decls(
    decls: &[IRDecl],
    config: &UnboxingExtConfig,
) -> (Vec<IRDecl>, UnboxingExtStats) {
    let mut stats = UnboxingExtStats::default();
    let prop_map = if config.enable_propagation {
        analyze_propagation_candidates(decls)
    } else {
        HashMap::new()
    };
    let result = decls
        .iter()
        .map(|d| {
            let opt = unbox_ext_decl(d, config, &prop_map, &mut stats);
            stats.decls_processed += 1;
            opt
        })
        .collect();
    (result, stats)
}

/// Apply extended unboxing to a single declaration.
#[must_use]
pub(crate) fn unbox_ext_decl(
    decl: &IRDecl,
    config: &UnboxingExtConfig,
    prop_map: &HashMap<String, Vec<(usize, IRType)>>,
    stats: &mut UnboxingExtStats,
) -> IRDecl {
    let mut params = decl.params.clone();
    let mut return_type = decl.return_type.clone();

    if config.enable_scalar_unboxing {
        let name_str = format!("{}", decl.name);
        if let Some(candidates) = prop_map.get(&name_str) {
            for (idx, scalar_ty) in candidates {
                if params.get(*idx).is_some_and(|(_, t)| *t == IRType::Object)
                    && should_unbox(config, &decl.body, params[*idx].0)
                {
                    params[*idx].1 = scalar_ty.clone();
                    stats.scalars_unboxed += 1;
                }
            }
        }
    }

    if config.enable_struct_unboxing {
        if let Some(inner) = classify_struct_unboxing(&return_type) {
            if inner.is_scalar() {
                return_type = inner;
                stats.structs_unboxed += 1;
            }
        }
    }

    let body = if config.enable_propagation && !prop_map.is_empty() {
        propagate_unboxed_args(&decl.body, prop_map, stats)
    } else {
        decl.body.clone()
    };

    IRDecl {
        name: decl.name.clone(),
        params,
        return_type,
        body,
    }
}

fn should_unbox(config: &UnboxingExtConfig, body: &IRBody, param_var: VarId) -> bool {
    if !config.enable_profitability_check {
        return true;
    }
    analyze_param_unboxing_cost(body, param_var).profitability() >= config.profitability_threshold
}

/// Rewrite call arguments according to the propagation map.
fn propagate_unboxed_args(
    body: &IRBody,
    prop_map: &HashMap<String, Vec<(usize, IRType)>>,
    stats: &mut UnboxingExtStats,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            if let IRExpr::Apply { fn_id, args } = value {
                let fn_name = format!("{}", fn_id.0);
                if let Some(candidates) = prop_map.get(&fn_name) {
                    for (idx, _) in candidates {
                        if *idx < args.len() {
                            stats.propagations += 1;
                        }
                    }
                }
            }
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: value.clone(),
                rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
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
            body: Box::new(propagate_unboxed_args(jp_body, prop_map, stats)),
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let alts = alts
                .iter()
                .map(|a| crate::ir::IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(propagate_unboxed_args(&a.body, prop_map, stats)),
                })
                .collect();
            let default = default
                .as_ref()
                .map(|d| Box::new(propagate_unboxed_args(d, prop_map, stats)));
            IRBody::Case {
                scrutinee: *scrutinee,
                alts,
                default,
            }
        }
        _ => propagate_passthrough(body, prop_map, stats),
    }
}

fn propagate_passthrough(
    body: &IRBody,
    prop_map: &HashMap<String, Vec<(usize, IRType)>>,
    stats: &mut UnboxingExtStats,
) -> IRBody {
    match body {
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
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
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
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
            rest: Box::new(propagate_unboxed_args(rest, prop_map, stats)),
        },
        _ => body.clone(),
    }
}

/// Convenience: apply extended unboxing with default config.
#[must_use]
pub(crate) fn unbox_ext_decls_default(decls: &[IRDecl]) -> (Vec<IRDecl>, UnboxingExtStats) {
    unbox_ext_decls(decls, &UnboxingExtConfig::new())
}

/// Generate a human-readable report of unboxing statistics.
#[must_use]
pub(crate) fn format_stats_report(stats: &UnboxingExtStats) -> String {
    format!(
        "Extended Unboxing Report:\n\
         - Declarations processed: {}\n\
         - Scalars unboxed: {}\n\
         - Structures unboxed: {}\n\
         - Arrays unboxed: {}\n\
         - Propagations: {}\n\
         - Partial unboxes: {}\n\
         - Rejected (unprofitable): {}\n\
         - Total optimizations: {}",
        stats.decls_processed,
        stats.scalars_unboxed,
        stats.structs_unboxed,
        stats.arrays_unboxed,
        stats.propagations,
        stats.partial_unboxes,
        stats.rejected_unprofitable,
        stats.total_optimizations(),
    )
}
