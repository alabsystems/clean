// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dead Code Elimination (DCE) for L5IR.
//!
//! Two-phase DCE pass that operates on the low-level IR with explicit
//! reference counting:
//!
//! 1. **Dead local elimination** (`dce_local`) -- removes unused `VDecl`
//!    let-bindings within function bodies.
//! 2. **Dead global elimination** -- removes top-level `IRDecl`s that
//!    are unreachable from a set of entry points via call-graph analysis.
//!
//! Part of #3084 - IO/FFI/Native epic.

pub(crate) use crate::dce_local::eliminate_dead_locals;
use crate::ir::{IRBody, IRDecl, IRExpr};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};

// -----------------------------------------------------------------------
// Configuration
// -----------------------------------------------------------------------

/// Configuration for the DCE pass.
#[derive(Debug, Clone)]
pub(crate) struct DceConfig {
    /// Remove unused local let-bindings within function bodies.
    pub eliminate_locals: bool,
    /// Remove unreachable top-level definitions.
    pub eliminate_globals: bool,
    /// Entry-point names (always kept alive during global DCE).
    pub entry_points: Vec<Name>,
}

impl Default for DceConfig {
    fn default() -> Self {
        Self {
            eliminate_locals: true,
            eliminate_globals: true,
            entry_points: Vec::new(),
        }
    }
}

// -----------------------------------------------------------------------
// Result
// -----------------------------------------------------------------------

/// Statistics from a DCE pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct DceResult {
    /// Number of local VDecl bindings removed.
    pub removed_locals: usize,
    /// Number of top-level definitions removed.
    pub removed_globals: usize,
    /// Set of names that were determined to be live.
    pub live_definitions: HashSet<Name>,
}

// -----------------------------------------------------------------------
// Liveness analyzer (global call-graph)
// -----------------------------------------------------------------------

/// Worklist-based liveness analyzer over the inter-procedural call graph.
pub(crate) struct LivenessAnalyzer {
    live: HashSet<Name>,
    worklist: Vec<Name>,
    call_graph: HashMap<Name, HashSet<Name>>,
}

impl LivenessAnalyzer {
    /// Create an empty analyzer.
    pub(crate) fn new() -> Self {
        Self {
            live: HashSet::new(),
            worklist: Vec::new(),
            call_graph: HashMap::new(),
        }
    }

    /// Mark `name` as a live root (entry point).
    pub(crate) fn add_entry_point(&mut self, name: &Name) {
        self.worklist.push(name.clone());
    }

    /// Record the callees of a single declaration into the call graph.
    pub(crate) fn analyze_decl(&mut self, decl: &IRDecl) {
        let mut callees = HashSet::new();
        collect_callees_body(&decl.body, &mut callees);
        self.call_graph.insert(decl.name.clone(), callees);
    }

    /// Iterate to fixpoint and return the set of live names.
    pub(crate) fn compute_live_set(mut self) -> HashSet<Name> {
        while let Some(name) = self.worklist.pop() {
            if self.live.insert(name.clone()) {
                if let Some(callees) = self.call_graph.get(&name) {
                    for callee in callees {
                        if !self.live.contains(callee) {
                            self.worklist.push(callee.clone());
                        }
                    }
                }
            }
        }
        self.live
    }
}

// -----------------------------------------------------------------------
// Call-graph helpers
// -----------------------------------------------------------------------

/// Collect all `FnId` names referenced by expressions in `body`.
fn collect_callees_body(body: &IRBody, out: &mut HashSet<Name>) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            collect_callees_expr(value, out);
            collect_callees_body(rest, out);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            collect_callees_body(jp_body, out);
            collect_callees_body(rest, out);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_callees_body(rest, out);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_callees_body(&alt.body, out);
            }
            if let Some(d) = default {
                collect_callees_body(d, out);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn collect_callees_expr(expr: &IRExpr, out: &mut HashSet<Name>) {
    match expr {
        IRExpr::Apply { fn_id, .. } | IRExpr::PartialApply { fn_id, .. } => {
            out.insert(fn_id.0.clone());
        }
        _ => {}
    }
}

// -----------------------------------------------------------------------
// Global DCE — dead definition removal
// -----------------------------------------------------------------------

/// Filter declarations to only those whose names are in `live_set`.
pub(crate) fn eliminate_dead_globals(decls: &[IRDecl], live_set: &HashSet<Name>) -> Vec<IRDecl> {
    decls
        .iter()
        .filter(|d| live_set.contains(&d.name))
        .cloned()
        .collect()
}

// -----------------------------------------------------------------------
// Top-level pass
// -----------------------------------------------------------------------

/// Run the full DCE pass on a list of IR declarations.
///
/// Performs both local dead-binding elimination (within each function body)
/// and global dead-definition removal (across the call graph) according to
/// `config`.
#[must_use]
pub(crate) fn run_dce(decls: &[IRDecl], config: &DceConfig) -> (Vec<IRDecl>, DceResult) {
    let mut result = DceResult::default();
    let mut working = decls.to_vec();

    // Phase 1: local DCE within each body
    if config.eliminate_locals {
        for decl in &mut working {
            let (new_body, removed) = eliminate_dead_locals(&decl.body);
            result.removed_locals += removed;
            decl.body = new_body;
        }
    }

    // Phase 2: global DCE via liveness analysis
    if config.eliminate_globals {
        let mut analyzer = LivenessAnalyzer::new();

        for ep in &config.entry_points {
            analyzer.add_entry_point(ep);
        }

        for decl in &working {
            analyzer.analyze_decl(decl);
        }

        let live_set = analyzer.compute_live_set();
        let before = working.len();
        working = eliminate_dead_globals(&working, &live_set);
        result.removed_globals = before - working.len();
        result.live_definitions = live_set;
    } else {
        result.live_definitions = working.iter().map(|d| d.name.clone()).collect();
    }

    (working, result)
}

#[cfg(test)]
#[path = "dce_tests.rs"]
mod tests;
