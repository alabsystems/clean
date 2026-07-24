// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended compiler environment analysis and management.
//!
//! Provides environment statistics, dependency analysis, diff computation,
//! declaration search, consistency validation, snapshot/restore, and
//! human-readable summaries. Complements `compiler_env` (core lookup).

use crate::compiler_env::CompilerEnv;
use crate::ir::{IRBody, IRDecl, IRExpr};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use std::fmt;
use thiserror::Error;

// ── Errors ───────────────────────────────────────────────────────────────

/// Errors from environment validation.
#[derive(Debug, Clone, Error)]
pub(crate) enum EnvValidationError {
    #[error("declaration `{0}` references undefined function `{1}`")]
    DanglingRef(String, String),
    #[error("duplicate declaration name `{0}`")]
    DuplicateName(String),
    #[error("declaration `{0}` has empty body (Unreachable) with parameters")]
    UnreachableWithParams(String),
}

// ── Environment statistics ───────────────────────────────────────────────

/// Aggregate statistics about declarations in an environment.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct EnvStats {
    /// Total declaration count.
    pub(crate) total_decls: usize,
    /// Declarations with zero parameters (constants/thunks).
    pub(crate) nullary_decls: usize,
    /// Declarations with at least one parameter.
    pub(crate) function_decls: usize,
    /// Declarations whose body is `IRBody::Unreachable`.
    pub(crate) unreachable_decls: usize,
    /// Sum of IR body node counts across all declarations.
    pub(crate) total_ir_nodes: usize,
}

/// Compute aggregate statistics for a slice of declarations.
#[must_use]
pub(crate) fn env_stats(decls: &[IRDecl]) -> EnvStats {
    let mut s = EnvStats {
        total_decls: decls.len(),
        ..EnvStats::default()
    };
    for d in decls {
        if d.params.is_empty() {
            s.nullary_decls += 1;
        } else {
            s.function_decls += 1;
        }
        if matches!(d.body, IRBody::Unreachable) {
            s.unreachable_decls += 1;
        }
        s.total_ir_nodes += body_node_count(&d.body);
    }
    s
}

/// Average IR node count per declaration (0 if no declarations).
#[must_use]
pub(crate) fn avg_function_size(decls: &[IRDecl]) -> usize {
    if decls.is_empty() {
        return 0;
    }
    let total: usize = decls.iter().map(|d| body_node_count(&d.body)).sum();
    total / decls.len()
}

/// Count IR body nodes in a single body (recursive).
fn body_node_count(body: &IRBody) -> usize {
    match body {
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => 1 + body_node_count(rest),
        IRBody::JDecl { body: jp, rest, .. } => 1 + body_node_count(jp) + body_node_count(rest),
        IRBody::Case { alts, default, .. } => {
            let alt_sum: usize = alts.iter().map(|a| body_node_count(&a.body)).sum();
            let def_sum = default.as_ref().map_or(0, |d| body_node_count(d));
            1 + alt_sum + def_sum
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => 1,
    }
}

// ── Dependency analysis ──────────────────────────────────────────────────

/// Build a dependency graph: for each declaration name, the set of names it
/// references via `Apply` or `PartialApply`.
#[must_use]
pub(crate) fn dependency_graph(decls: &[IRDecl]) -> HashMap<Name, HashSet<Name>> {
    decls
        .iter()
        .map(|d| {
            let mut deps = HashSet::new();
            collect_call_refs_body(&d.body, &mut deps);
            (d.name.clone(), deps)
        })
        .collect()
}

fn collect_call_refs_body(body: &IRBody, deps: &mut HashSet<Name>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_call_refs_expr(value, deps);
            collect_call_refs_body(rest, deps);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            collect_call_refs_body(jp, deps);
            collect_call_refs_body(rest, deps);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_call_refs_body(rest, deps);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_call_refs_body(&alt.body, deps);
            }
            if let Some(d) = default {
                collect_call_refs_body(d, deps);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_call_refs_expr(expr: &IRExpr, deps: &mut HashSet<Name>) {
    match expr {
        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
            deps.insert(fn_id.0.clone());
        }
        _ => {}
    }
}

/// Find strongly connected components via Tarjan's algorithm.
/// Returns SCCs in reverse topological order (leaves first).
#[must_use]
pub(crate) fn strongly_connected_components(
    graph: &HashMap<Name, HashSet<Name>>,
) -> Vec<Vec<Name>> {
    let mut state = TarjanState {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        indices: HashMap::new(),
        lowlinks: HashMap::new(),
        result: Vec::new(),
    };
    for node in graph.keys() {
        if !state.indices.contains_key(node) {
            tarjan_dfs(node, graph, &mut state);
        }
    }
    state.result
}

struct TarjanState {
    index_counter: usize,
    stack: Vec<Name>,
    on_stack: HashSet<Name>,
    indices: HashMap<Name, usize>,
    lowlinks: HashMap<Name, usize>,
    result: Vec<Vec<Name>>,
}

fn tarjan_dfs(v: &Name, graph: &HashMap<Name, HashSet<Name>>, state: &mut TarjanState) {
    let idx = state.index_counter;
    state.index_counter += 1;
    state.indices.insert(v.clone(), idx);
    state.lowlinks.insert(v.clone(), idx);
    state.stack.push(v.clone());
    state.on_stack.insert(v.clone());

    if let Some(neighbors) = graph.get(v) {
        for w in neighbors {
            if let Some(&w_idx) = state.indices.get(w) {
                if state.on_stack.contains(w) {
                    let v_low = state.lowlinks[v];
                    if w_idx < v_low {
                        state.lowlinks.insert(v.clone(), w_idx);
                    }
                }
            } else if graph.contains_key(w) {
                tarjan_dfs(w, graph, state);
                let w_low = state.lowlinks[w];
                let v_low = state.lowlinks[v];
                if w_low < v_low {
                    state.lowlinks.insert(v.clone(), w_low);
                }
            }
        }
    }

    if state.lowlinks[v] == state.indices[v] {
        let mut component = Vec::new();
        loop {
            let w = state
                .stack
                .pop()
                .expect("invariant: stack not empty in SCC");
            state.on_stack.remove(&w);
            component.push(w.clone());
            if &w == v {
                break;
            }
        }
        state.result.push(component);
    }
}

// ── Environment diff ─────────────────────────────────────────────────────

/// Differences between two declaration sets.
#[derive(Debug, Clone, Default)]
pub(crate) struct EnvDiff {
    /// Names present in `new` but not in `old`.
    pub(crate) added: Vec<Name>,
    /// Names present in `old` but not in `new`.
    pub(crate) removed: Vec<Name>,
    /// Names present in both but with different parameter counts or body sizes.
    pub(crate) modified: Vec<Name>,
}

impl EnvDiff {
    /// True if the two environments are structurally identical.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.modified.is_empty()
    }

    /// Total number of changes.
    #[must_use]
    pub(crate) fn change_count(&self) -> usize {
        self.added.len() + self.removed.len() + self.modified.len()
    }
}

/// Compare two declaration slices and return the diff.
///
/// Two declarations with the same name are considered "modified" if they
/// differ in parameter count or body node count.
#[must_use]
pub(crate) fn env_diff(old: &[IRDecl], new: &[IRDecl]) -> EnvDiff {
    let old_map: HashMap<&Name, &IRDecl> = old.iter().map(|d| (&d.name, d)).collect();
    let new_map: HashMap<&Name, &IRDecl> = new.iter().map(|d| (&d.name, d)).collect();

    let mut diff = EnvDiff::default();
    for (name, new_d) in &new_map {
        match old_map.get(name) {
            None => diff.added.push((*name).clone()),
            Some(old_d) => {
                if old_d.params.len() != new_d.params.len()
                    || body_node_count(&old_d.body) != body_node_count(&new_d.body)
                {
                    diff.modified.push((*name).clone());
                }
            }
        }
    }
    for name in old_map.keys() {
        if !new_map.contains_key(name) {
            diff.removed.push((*name).clone());
        }
    }
    diff.added.sort_by_key(|a| a.to_string());
    diff.removed.sort_by_key(|a| a.to_string());
    diff.modified.sort_by_key(|a| a.to_string());
    diff
}

// ── Declaration search ───────────────────────────────────────────────────

/// Search declarations whose name contains `pattern` (case-sensitive substring).
#[must_use]
pub(crate) fn search_by_name<'a>(decls: &'a [IRDecl], pattern: &str) -> Vec<&'a IRDecl> {
    decls
        .iter()
        .filter(|d| d.name.to_string().contains(pattern))
        .collect()
}

/// Search declarations by arity (exact parameter count).
#[must_use]
pub(crate) fn search_by_arity(decls: &[IRDecl], arity: usize) -> Vec<&IRDecl> {
    decls.iter().filter(|d| d.params.len() == arity).collect()
}

/// Search declarations whose body size exceeds `threshold` nodes.
#[must_use]
pub(crate) fn search_large_bodies(decls: &[IRDecl], threshold: usize) -> Vec<&IRDecl> {
    decls
        .iter()
        .filter(|d| body_node_count(&d.body) > threshold)
        .collect()
}

/// Search declarations that contain at least one `Case` node.
#[must_use]
pub(crate) fn search_with_cases(decls: &[IRDecl]) -> Vec<&IRDecl> {
    decls.iter().filter(|d| body_has_case(&d.body)).collect()
}

fn body_has_case(body: &IRBody) -> bool {
    match body {
        IRBody::Case { .. } => true,
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => body_has_case(rest),
        IRBody::JDecl { body: jp, rest, .. } => body_has_case(jp) || body_has_case(rest),
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => false,
    }
}

// ── Environment validation ───────────────────────────────────────────────

/// Validate environment consistency: no duplicate names, no dangling function
/// references, no declarations with parameters but `Unreachable` body.
/// Pass `allow_external` to skip the dangling-ref check for known externals.
pub(crate) fn validate_env(
    decls: &[IRDecl],
    allow_external: &HashSet<Name>,
) -> Vec<EnvValidationError> {
    let mut errors = Vec::new();
    let known: HashSet<&Name> = decls.iter().map(|d| &d.name).collect();

    // Duplicate names.
    let mut seen = HashSet::new();
    for d in decls {
        if !seen.insert(&d.name) {
            errors.push(EnvValidationError::DuplicateName(d.name.to_string()));
        }
    }

    // Dangling refs.
    for d in decls {
        let mut refs = HashSet::new();
        collect_call_refs_body(&d.body, &mut refs);
        for r in &refs {
            if !known.contains(r) && !allow_external.contains(r) {
                errors.push(EnvValidationError::DanglingRef(
                    d.name.to_string(),
                    r.to_string(),
                ));
            }
        }
    }

    // Unreachable with params.
    for d in decls {
        if !d.params.is_empty() && matches!(d.body, IRBody::Unreachable) {
            errors.push(EnvValidationError::UnreachableWithParams(
                d.name.to_string(),
            ));
        }
    }

    errors
}

// ── Snapshot / restore ───────────────────────────────────────────────────

/// A lightweight snapshot of an environment for incremental compilation.
///
/// Stores cloned declarations so the original can be mutated. Restore
/// rebuilds a `CompilerEnv` from the snapshot.
#[derive(Debug, Clone)]
pub(crate) struct EnvSnapshot {
    decls: Vec<IRDecl>,
}

impl EnvSnapshot {
    /// Capture a snapshot of the current declarations.
    #[must_use]
    pub(crate) fn capture(decls: &[IRDecl]) -> Self {
        Self {
            decls: decls.to_vec(),
        }
    }

    /// Restore the snapshot: returns the stored declarations and a fresh
    /// `CompilerEnv` built from them.
    #[must_use]
    pub(crate) fn restore(&self) -> (Vec<IRDecl>, CompilerEnv) {
        let env = CompilerEnv::from_decls(&self.decls);
        (self.decls.clone(), env)
    }

    /// Number of declarations in the snapshot.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.decls.len()
    }

    /// Whether the snapshot is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }
}

// ── Environment summary ──────────────────────────────────────────────────

/// Human-readable summary of an environment's contents.
#[derive(Debug, Clone)]
pub(crate) struct EnvSummary {
    pub(crate) stats: EnvStats,
    pub(crate) largest_decls: Vec<(String, usize)>,
    pub(crate) scc_count: usize,
    pub(crate) recursive_sccs: usize,
}

impl fmt::Display for EnvSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Environment Summary")?;
        writeln!(f, "  declarations: {}", self.stats.total_decls)?;
        writeln!(f, "  functions:    {}", self.stats.function_decls)?;
        writeln!(f, "  constants:    {}", self.stats.nullary_decls)?;
        writeln!(f, "  unreachable:  {}", self.stats.unreachable_decls)?;
        writeln!(f, "  total IR nodes: {}", self.stats.total_ir_nodes)?;
        writeln!(
            f,
            "  SCCs: {} ({} recursive)",
            self.scc_count, self.recursive_sccs
        )?;
        if !self.largest_decls.is_empty() {
            writeln!(f, "  largest declarations:")?;
            for (name, size) in &self.largest_decls {
                writeln!(f, "    {name}: {size} nodes")?;
            }
        }
        Ok(())
    }
}

/// Build a human-readable summary of the environment.
///
/// `top_n` controls how many of the largest declarations to include.
#[must_use]
pub(crate) fn env_summary(decls: &[IRDecl], top_n: usize) -> EnvSummary {
    let stats = env_stats(decls);
    let graph = dependency_graph(decls);
    let sccs = strongly_connected_components(&graph);
    let recursive_sccs = sccs
        .iter()
        .filter(|scc| {
            if scc.len() > 1 {
                return true;
            }
            // Single-node SCC is recursive only if it references itself.
            if let Some(name) = scc.first() {
                if let Some(deps) = graph.get(name) {
                    return deps.contains(name);
                }
            }
            false
        })
        .count();

    let mut sizes: Vec<(String, usize)> = decls
        .iter()
        .map(|d| (d.name.to_string(), body_node_count(&d.body)))
        .collect();
    sizes.sort_by_key(|b| std::cmp::Reverse(b.1));
    sizes.truncate(top_n);

    EnvSummary {
        stats,
        largest_decls: sizes,
        scc_count: sccs.len(),
        recursive_sccs,
    }
}
