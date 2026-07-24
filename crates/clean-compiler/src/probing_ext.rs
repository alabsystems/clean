// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IR probing: lookup, size, var usage, call graph, captures, types,
//! case depth, RC ops, module summary, and query interface. Part of #3083.

use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use std::collections::HashMap;

/// Find a declaration by name.
#[must_use]
pub(crate) fn find_decl<'a>(decls: &'a [IRDecl], name: &str) -> Option<&'a IRDecl> {
    decls.iter().find(|d| d.name.to_string() == name)
}

/// Count the total number of IR nodes in a function body.
#[must_use]
pub(crate) fn body_size(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. } => 1 + body_size(rest),
        IRBody::JDecl { body: jp, rest, .. } => 1 + body_size(jp) + body_size(rest),
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + body_size(rest),
        IRBody::Case { alts, default, .. } => {
            let alt_size: usize = alts.iter().map(|a| body_size(&a.body)).sum();
            let def_size = default.as_ref().map_or(0, |d| body_size(d));
            1 + alt_size + def_size
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

/// Count how many times each variable is referenced in a body.
#[must_use]
pub(crate) fn var_usage_counts(body: &IRBody) -> HashMap<VarId, usize> {
    let mut counts = HashMap::new();
    count_vars_body(body, &mut counts);
    counts
}

fn bump(counts: &mut HashMap<VarId, usize>, v: VarId) {
    *counts.entry(v).or_insert(0) += 1;
}

fn count_vars_arg(arg: &IRArg, counts: &mut HashMap<VarId, usize>) {
    if let IRArg::Var(v) = arg {
        bump(counts, *v);
    }
}

fn count_vars_args(args: &[IRArg], counts: &mut HashMap<VarId, usize>) {
    for a in args {
        count_vars_arg(a, counts);
    }
}

fn count_vars_expr(expr: &IRExpr, counts: &mut HashMap<VarId, usize>) {
    match expr {
        IRExpr::Ctor { args, .. } => count_vars_args(args, counts),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => count_vars_arg(arg, counts),
        IRExpr::Lit(_) | IRExpr::String(_) => {}
        IRExpr::Apply { args, .. } | IRExpr::PartialApply { args, .. } => {
            count_vars_args(args, counts);
        }
        IRExpr::ClosureApply { closure, args } => {
            count_vars_arg(closure, counts);
            count_vars_args(args, counts);
        }
        IRExpr::UProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var)
        | IRExpr::SProj { var, .. } => bump(counts, *var),
        IRExpr::Reuse { var, args, .. } => {
            bump(counts, *var);
            count_vars_args(args, counts);
        }
    }
}

fn count_vars_body(body: &IRBody, counts: &mut HashMap<VarId, usize>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            count_vars_expr(value, counts);
            count_vars_body(rest, counts);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            count_vars_body(jp, counts);
            count_vars_body(rest, counts);
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest, .. } => {
            bump(counts, *var);
            count_vars_body(rest, counts);
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
            bump(counts, *var);
            bump(counts, *value);
            count_vars_body(rest, counts);
        }
        IRBody::SetTag { var, rest, .. } => {
            bump(counts, *var);
            count_vars_body(rest, counts);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            bump(counts, *scrutinee);
            for alt in alts {
                count_vars_body(&alt.body, counts);
            }
            if let Some(d) = default {
                count_vars_body(d, counts);
            }
        }
        IRBody::Jmp { args, .. } => count_vars_args(args, counts),
        IRBody::Ret(arg) => count_vars_arg(arg, counts),
        IRBody::Unreachable => {}
    }
}

/// Build a call graph: maps each function name to the sorted, deduplicated
/// list of functions it calls.
#[must_use]
pub(crate) fn call_graph(decls: &[IRDecl]) -> HashMap<String, Vec<String>> {
    decls
        .iter()
        .map(|d| {
            let mut callees = Vec::new();
            collect_callees_body(&d.body, &mut callees);
            callees.sort();
            callees.dedup();
            (d.name.to_string(), callees)
        })
        .collect()
}

fn collect_callees_expr(expr: &IRExpr, callees: &mut Vec<String>) {
    match expr {
        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
            callees.push(fn_id.0.to_string());
        }
        _ => {}
    }
}

fn collect_callees_body(body: &IRBody, callees: &mut Vec<String>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_callees_expr(value, callees);
            collect_callees_body(rest, callees);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_callees_body(jp, callees);
            collect_callees_body(rest, callees);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_callees_body(rest, callees),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_callees_body(&alt.body, callees);
            }
            if let Some(d) = default {
                collect_callees_body(d, callees);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct CaptureInfo {
    pub(crate) fn_name: String,
    pub(crate) captured_vars: Vec<VarId>,
}

/// Find all closure capture sites (partial applications) in a body.
#[must_use]
pub(crate) fn closure_captures(body: &IRBody) -> Vec<CaptureInfo> {
    let mut result = Vec::new();
    captures_body(body, &mut result);
    result
}

fn captures_expr(expr: &IRExpr, result: &mut Vec<CaptureInfo>) {
    if let IRExpr::PartialApply { fn_id, args, .. } = expr {
        let captured: Vec<VarId> = args
            .iter()
            .filter_map(|a| {
                if let IRArg::Var(v) = a {
                    Some(*v)
                } else {
                    None
                }
            })
            .collect();
        result.push(CaptureInfo {
            fn_name: fn_id.0.to_string(),
            captured_vars: captured,
        });
    }
}

fn captures_body(body: &IRBody, result: &mut Vec<CaptureInfo>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            captures_expr(value, result);
            captures_body(rest, result);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            captures_body(jp, result);
            captures_body(rest, result);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => captures_body(rest, result),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                captures_body(&alt.body, result);
            }
            if let Some(d) = default {
                captures_body(d, result);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn type_name(ty: &IRType) -> &'static str {
    match ty {
        IRType::Bool => "Bool",
        IRType::UInt8 => "UInt8",
        IRType::UInt16 => "UInt16",
        IRType::UInt32 => "UInt32",
        IRType::UInt64 => "UInt64",
        IRType::USize => "USize",
        IRType::Float32 => "Float32",
        IRType::Float64 => "Float64",
        IRType::Object => "Object",
        IRType::TObject => "TObject",
        IRType::Struct(_) => "Struct",
        IRType::Union(_) => "Union",
        IRType::Erased => "Erased",
        IRType::Void => "Void",
    }
}

/// Count occurrences of each IR type in a body.
#[must_use]
pub(crate) fn type_occurrences(body: &IRBody) -> HashMap<String, usize> {
    let mut counts = HashMap::new();
    types_body(body, &mut counts);
    counts
}

fn bump_type(counts: &mut HashMap<String, usize>, ty: &IRType) {
    *counts.entry(type_name(ty).to_owned()).or_insert(0) += 1;
}

fn types_expr(expr: &IRExpr, counts: &mut HashMap<String, usize>) {
    match expr {
        IRExpr::Proj { ty, .. }
        | IRExpr::Box { ty, .. }
        | IRExpr::Unbox { ty, .. }
        | IRExpr::SProj { ty, .. } => bump_type(counts, ty),
        IRExpr::Ctor { info, .. } | IRExpr::Reuse { ctor: info, .. } => {
            for ft in &info.field_types {
                bump_type(counts, ft);
            }
        }
        _ => {}
    }
}

fn types_body(body: &IRBody, counts: &mut HashMap<String, usize>) {
    match body {
        IRBody::VDecl {
            ty, value, rest, ..
        } => {
            bump_type(counts, ty);
            types_expr(value, counts);
            types_body(rest, counts);
        }
        IRBody::JDecl {
            params,
            body: jp,
            rest,
            ..
        } => {
            for (_, ty) in params {
                bump_type(counts, ty);
            }
            types_body(jp, counts);
            types_body(rest, counts);
        }
        IRBody::SSet { ty, rest, .. } => {
            bump_type(counts, ty);
            types_body(rest, counts);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. } => types_body(rest, counts),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                types_body(&alt.body, counts);
            }
            if let Some(d) = default {
                types_body(d, counts);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Compute the maximum nesting depth of Case expressions.
#[must_use]
pub(crate) fn case_depth(body: &IRBody) -> usize {
    case_depth_impl(body, 0)
}

fn case_depth_impl(body: &IRBody, depth: usize) -> usize {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => case_depth_impl(rest, depth),
        IRBody::JDecl { body: jp, rest, .. } => {
            case_depth_impl(jp, depth).max(case_depth_impl(rest, depth))
        }
        IRBody::Case { alts, default, .. } => {
            let inner = depth + 1;
            let mut max_d = inner;
            for alt in alts {
                max_d = max_d.max(case_depth_impl(&alt.body, inner));
            }
            if let Some(d) = default {
                max_d = max_d.max(case_depth_impl(d, inner));
            }
            max_d
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => depth,
    }
}

/// Counts of reference counting operations in a function body.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct RcOpCounts {
    pub(crate) inc: usize,
    pub(crate) dec: usize,
    pub(crate) reset: usize,
    pub(crate) reuse: usize,
}

/// Count Inc/Dec/Reset/Reuse operations in a body.
#[must_use]
pub(crate) fn rc_op_counts(body: &IRBody) -> RcOpCounts {
    let mut counts = RcOpCounts::default();
    rc_ops_body(body, &mut counts);
    counts
}

fn rc_ops_expr(expr: &IRExpr, counts: &mut RcOpCounts) {
    match expr {
        IRExpr::Reset(_) => counts.reset += 1,
        IRExpr::Reuse { .. } => counts.reuse += 1,
        _ => {}
    }
}

fn rc_ops_body(body: &IRBody, counts: &mut RcOpCounts) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            rc_ops_expr(value, counts);
            rc_ops_body(rest, counts);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            rc_ops_body(jp, counts);
            rc_ops_body(rest, counts);
        }
        IRBody::Inc { rest, .. } => {
            counts.inc += 1;
            rc_ops_body(rest, counts);
        }
        IRBody::Dec { rest, .. } => {
            counts.dec += 1;
            rc_ops_body(rest, counts);
        }
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => rc_ops_body(rest, counts),
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                rc_ops_body(&alt.body, counts);
            }
            if let Some(d) = default {
                rc_ops_body(d, counts);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Aggregate statistics for a collection of IR declarations.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ModuleSummary {
    pub(crate) num_decls: usize,
    pub(crate) total_body_size: usize,
    pub(crate) total_params: usize,
    pub(crate) rc_ops: RcOpCounts,
    pub(crate) type_counts: HashMap<String, usize>,
    pub(crate) avg_body_size: f64,
}

/// Compute aggregate statistics over a slice of declarations.
#[must_use]
pub(crate) fn module_summary(decls: &[IRDecl]) -> ModuleSummary {
    let num_decls = decls.len();
    let mut total_body_size = 0usize;
    let mut total_params = 0usize;
    let mut rc_ops = RcOpCounts::default();
    let mut type_counts: HashMap<String, usize> = HashMap::new();

    for d in decls {
        total_body_size += body_size(&d.body);
        total_params += d.params.len();

        for (_, ty) in &d.params {
            *type_counts.entry(type_name(ty).to_owned()).or_insert(0) += 1;
        }
        *type_counts
            .entry(type_name(&d.return_type).to_owned())
            .or_insert(0) += 1;

        let body_types = type_occurrences(&d.body);
        for (k, v) in body_types {
            *type_counts.entry(k).or_insert(0) += v;
        }

        let ops = rc_op_counts(&d.body);
        rc_ops.inc += ops.inc;
        rc_ops.dec += ops.dec;
        rc_ops.reset += ops.reset;
        rc_ops.reuse += ops.reuse;
    }

    let avg_body_size = if num_decls > 0 {
        total_body_size as f64 / num_decls as f64
    } else {
        0.0
    };

    ModuleSummary {
        num_decls,
        total_body_size,
        total_params,
        rc_ops,
        type_counts,
        avg_body_size,
    }
}

/// Find all function names that call the given target function.
#[must_use]
pub(crate) fn query_callers(decls: &[IRDecl], target: &str) -> Vec<String> {
    let graph = call_graph(decls);
    let mut callers: Vec<String> = graph
        .iter()
        .filter(|(_, callees)| callees.iter().any(|c| c == target))
        .map(|(caller, _)| caller.clone())
        .collect();
    callers.sort();
    callers
}
