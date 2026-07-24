// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended dead code elimination analysis for L5IR.
//!
//! Builds on the core DCE pass (`dce`) with reachability analysis,
//! dead declaration/parameter detection, impact estimation, reporting,
//! and conservative vs aggressive analysis modes.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::dce::LivenessAnalyzer;
use crate::dce_local::collect_used;
use crate::ir::{IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

/// Errors from extended DCE analysis.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub(crate) enum DceExtError {
    #[error("unknown entry point: {0}")]
    UnknownEntryPoint(String),
    #[error("no entry points specified for reachability analysis")]
    NoEntryPoints,
}

/// Analysis precision level for DCE.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum DceMode {
    /// Conservative: only eliminates provably dead code.
    #[default]
    Conservative,
    /// Aggressive: assumes static call graph is complete.
    Aggressive,
}

/// Information about a dead (unused) parameter in a declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadParam {
    pub(crate) decl_name: Name,
    pub(crate) param_index: usize,
    pub(crate) var_id: VarId,
    pub(crate) param_type: IRType,
}

/// Information about a dead (unreachable) declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeadDecl {
    pub(crate) name: Name,
    pub(crate) estimated_size: usize,
}

/// Statistics from extended DCE analysis.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DceExtStats {
    pub(crate) total_decls: usize,
    pub(crate) reachable_decls: usize,
    pub(crate) dead_decls: usize,
    pub(crate) total_params: usize,
    pub(crate) dead_params: usize,
    pub(crate) dead_node_count: usize,
    pub(crate) total_node_count: usize,
}

impl DceExtStats {
    pub(crate) fn dead_decl_fraction(&self) -> f64 {
        if self.total_decls == 0 {
            0.0
        } else {
            self.dead_decls as f64 / self.total_decls as f64
        }
    }
    pub(crate) fn dead_param_fraction(&self) -> f64 {
        if self.total_params == 0 {
            0.0
        } else {
            self.dead_params as f64 / self.total_params as f64
        }
    }
    pub(crate) fn estimated_size_reduction(&self) -> f64 {
        if self.total_node_count == 0 {
            0.0
        } else {
            self.dead_node_count as f64 / self.total_node_count as f64
        }
    }
}

/// Human-readable DCE analysis report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DceReport {
    pub(crate) stats: DceExtStats,
    pub(crate) dead_decls: Vec<DeadDecl>,
    pub(crate) dead_params: Vec<DeadParam>,
    pub(crate) mode: DceMode,
}

impl fmt::Display for DceReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mode_str = match self.mode {
            DceMode::Conservative => "conservative",
            DceMode::Aggressive => "aggressive",
        };
        writeln!(f, "DCE Analysis Report (mode: {mode_str})")?;
        writeln!(f, "================================")?;
        let s = &self.stats;
        writeln!(
            f,
            "Declarations: {}/{} dead ({:.1}%)",
            s.dead_decls,
            s.total_decls,
            s.dead_decl_fraction() * 100.0
        )?;
        writeln!(
            f,
            "Parameters:   {}/{} dead ({:.1}%)",
            s.dead_params,
            s.total_params,
            s.dead_param_fraction() * 100.0
        )?;
        writeln!(
            f,
            "Size impact:  {}/{} nodes ({:.1}% reduction)",
            s.dead_node_count,
            s.total_node_count,
            s.estimated_size_reduction() * 100.0
        )?;
        if !self.dead_decls.is_empty() {
            writeln!(f, "\nDead declarations:")?;
            for dd in &self.dead_decls {
                writeln!(f, "  - {} (~{} nodes)", dd.name, dd.estimated_size)?;
            }
        }
        if !self.dead_params.is_empty() {
            writeln!(f, "\nDead parameters:")?;
            for dp in &self.dead_params {
                writeln!(
                    f,
                    "  - {}[{}]: {:?} (VarId({}))",
                    dp.decl_name, dp.param_index, dp.param_type, dp.var_id.0
                )?;
            }
        }
        Ok(())
    }
}

// -- IR node counting -----------------------------------------------------

/// Estimate the number of IR nodes in a function body.
#[must_use]
pub(crate) fn count_body_nodes(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { value, rest, .. } => 1 + count_expr_nodes(value) + count_body_nodes(rest),
        IRBody::JDecl {
            body: jp,
            rest,
            params,
            ..
        } => 1 + params.len() + count_body_nodes(jp) + count_body_nodes(rest),
        IRBody::Inc { rest, .. } | IRBody::Dec { rest, .. } => 1 + count_body_nodes(rest),
        IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + count_body_nodes(rest),
        IRBody::Case { alts, default, .. } => {
            let ac: usize = alts.iter().map(|a| 1 + count_body_nodes(&a.body)).sum();
            1 + ac + default.as_ref().map_or(0, |d| count_body_nodes(d))
        }
        IRBody::Jmp { args, .. } => 1 + args.len(),
        IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

fn count_expr_nodes(expr: &IRExpr) -> usize {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. }
        | IRExpr::Reuse { args, .. } => 1 + args.len(),
        IRExpr::ClosureApply { args, .. } => 2 + args.len(),
        _ => 1,
    }
}

/// Estimate the number of IR nodes in a declaration (params + body).
#[must_use]
pub(crate) fn count_decl_nodes(decl: &IRDecl) -> usize {
    decl.params.len() + count_body_nodes(&decl.body)
}

// -- Reachability analysis ------------------------------------------------

/// Compute reachable declaration names from entry points via call-graph traversal.
#[must_use]
pub(crate) fn compute_reachable(decls: &[IRDecl], entry_points: &[Name]) -> HashSet<Name> {
    let mut analyzer = LivenessAnalyzer::new();
    for ep in entry_points {
        analyzer.add_entry_point(ep);
    }
    for decl in decls {
        analyzer.analyze_decl(decl);
    }
    analyzer.compute_live_set()
}

/// Compute reachable set with entry-point validation.
pub(crate) fn compute_reachable_validated(
    decls: &[IRDecl],
    entry_points: &[Name],
) -> Result<HashSet<Name>, DceExtError> {
    if entry_points.is_empty() {
        return Err(DceExtError::NoEntryPoints);
    }
    let names: HashSet<&Name> = decls.iter().map(|d| &d.name).collect();
    for ep in entry_points {
        if !names.contains(ep) {
            return Err(DceExtError::UnknownEntryPoint(ep.to_string()));
        }
    }
    Ok(compute_reachable(decls, entry_points))
}

// -- Dead declaration detection -------------------------------------------

/// Find declarations not reachable from any entry point.
#[must_use]
pub(crate) fn find_dead_decls(decls: &[IRDecl], reachable: &HashSet<Name>) -> Vec<DeadDecl> {
    decls
        .iter()
        .filter(|d| !reachable.contains(&d.name))
        .map(|d| DeadDecl {
            name: d.name.clone(),
            estimated_size: count_decl_nodes(d),
        })
        .collect()
}

// -- Dead parameter detection ---------------------------------------------

/// Find unused parameters across all declarations.
///
/// Conservative mode skips functions called by others (removing their params
/// would require updating call sites). Aggressive mode checks all.
#[must_use]
pub(crate) fn find_dead_params(decls: &[IRDecl], mode: DceMode) -> Vec<DeadParam> {
    let called_fns: HashSet<Name> = if mode == DceMode::Conservative {
        let mut called = HashSet::new();
        for decl in decls {
            collect_called_names(&decl.body, &mut called);
        }
        called
    } else {
        HashSet::new()
    };
    let mut result = Vec::new();
    for decl in decls {
        if mode == DceMode::Conservative && called_fns.contains(&decl.name) {
            continue;
        }
        let mut used_vars = HashSet::new();
        let mut used_jps = HashSet::new();
        collect_used(&decl.body, &mut used_vars, &mut used_jps);
        for (i, (v, ty)) in decl.params.iter().enumerate() {
            if !used_vars.contains(v) {
                result.push(DeadParam {
                    decl_name: decl.name.clone(),
                    param_index: i,
                    var_id: *v,
                    param_type: ty.clone(),
                });
            }
        }
    }
    result
}

fn collect_called_names(body: &IRBody, out: &mut HashSet<Name>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_called_names_expr(value, out);
            collect_called_names(rest, out);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_called_names(jp, out);
            collect_called_names(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_called_names(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_called_names(&alt.body, out);
            }
            if let Some(d) = default {
                collect_called_names(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_called_names_expr(expr: &IRExpr, out: &mut HashSet<Name>) {
    if let IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } = expr {
        out.insert(fn_id.0.clone());
    }
}

// -- Impact estimation ----------------------------------------------------

/// Estimated impact of eliminating dead code.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DceImpact {
    pub(crate) removable_nodes: usize,
    pub(crate) total_nodes: usize,
    pub(crate) removable_decls: usize,
    pub(crate) removable_params: usize,
}

impl DceImpact {
    pub(crate) fn reduction_fraction(&self) -> f64 {
        if self.total_nodes == 0 {
            0.0
        } else {
            self.removable_nodes as f64 / self.total_nodes as f64
        }
    }
}

/// Estimate the impact of DCE on a set of declarations.
#[must_use]
pub(crate) fn estimate_impact(
    decls: &[IRDecl],
    dead_decls: &[DeadDecl],
    dead_params: &[DeadParam],
) -> DceImpact {
    DceImpact {
        removable_nodes: dead_decls.iter().map(|d| d.estimated_size).sum(),
        total_nodes: decls.iter().map(count_decl_nodes).sum(),
        removable_decls: dead_decls.len(),
        removable_params: dead_params.len(),
    }
}

// -- Full analysis --------------------------------------------------------

/// Run the complete extended DCE analysis and return a report.
#[must_use]
pub(crate) fn analyze_dce(decls: &[IRDecl], entry_points: &[Name], mode: DceMode) -> DceReport {
    let reachable = compute_reachable(decls, entry_points);
    let dead_decls = find_dead_decls(decls, &reachable);
    let dead_params = find_dead_params(decls, mode);
    let total_node_count: usize = decls.iter().map(count_decl_nodes).sum();
    let dead_node_count: usize = dead_decls.iter().map(|d| d.estimated_size).sum();
    let total_params: usize = decls.iter().map(|d| d.params.len()).sum();
    DceReport {
        stats: DceExtStats {
            total_decls: decls.len(),
            reachable_decls: reachable.len(),
            dead_decls: dead_decls.len(),
            total_params,
            dead_params: dead_params.len(),
            dead_node_count,
            total_node_count,
        },
        dead_decls,
        dead_params,
        mode,
    }
}

/// Build a call graph: declaration name -> set of called names.
#[must_use]
pub(crate) fn build_call_graph(decls: &[IRDecl]) -> HashMap<Name, HashSet<Name>> {
    decls
        .iter()
        .map(|d| {
            let mut callees = HashSet::new();
            collect_called_names(&d.body, &mut callees);
            (d.name.clone(), callees)
        })
        .collect()
}

/// Find declarations that have no callers (potential entry points or dead roots).
#[must_use]
pub(crate) fn find_uncalled_decls(decls: &[IRDecl]) -> Vec<Name> {
    let graph = build_call_graph(decls);
    let all_called: HashSet<Name> = graph.values().flat_map(|v| v.iter().cloned()).collect();
    let all_names: HashSet<Name> = decls.iter().map(|d| d.name.clone()).collect();
    all_names.difference(&all_called).cloned().collect()
}

/// Collect the set of VarIds used in a body.
#[must_use]
pub(crate) fn collect_used_vars(body: &IRBody) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    let mut jps = HashSet::new();
    collect_used(body, &mut vars, &mut jps);
    vars
}

/// Check if a parameter at `param_index` is used in the given body.
#[must_use]
pub(crate) fn is_param_used(params: &[(VarId, IRType)], param_index: usize, body: &IRBody) -> bool {
    param_index < params.len() && collect_used_vars(body).contains(&params[param_index].0)
}
