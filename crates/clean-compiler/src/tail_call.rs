// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tail call optimization analysis for L5IR.
//!
//! Detects self-recursive and mutually recursive tail calls in L5IR function
//! bodies. A call is in *tail position* when its result is returned directly,
//! possibly after reference-counting operations (inc/dec) on other variables.
//!
//! Lean 4 guarantees tail call elimination for self-recursive functions in
//! tail position. This pass identifies such calls so backends can emit loops
//! or use the `musttail` attribute instead of regular calls.
//!
//! # Algorithm
//!
//! 1. Walk the body to find VDecl nodes whose value is an Apply or
//!    ClosureApply expression.
//! 2. For each such VDecl, check whether the `rest` only performs RC
//!    operations (Inc, Dec, SetTag) on *other* variables before returning
//!    the declared variable.
//! 3. Recurse into Case arms (each arm is in tail position) and JDecl
//!    bodies (a join point's body is in tail position if the join point
//!    is only jumped to from tail positions).
//! 4. Classify each tail-position call as self or mutual.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, JoinPointId, VarId};
use clean_kernel::Name;
use std::collections::HashSet;

// -----------------------------------------------------------------------
// Configuration
// -----------------------------------------------------------------------

/// Configuration for tail call analysis.
#[derive(Clone, Debug)]
pub(crate) struct TailCallConfig {
    /// Whether tail call analysis is enabled.
    pub enabled: bool,
    /// Whether to detect mutual tail calls across a set of functions.
    pub detect_mutual: bool,
}

impl Default for TailCallConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            detect_mutual: true,
        }
    }
}

// -----------------------------------------------------------------------
// Statistics
// -----------------------------------------------------------------------

/// Statistics collected during tail call analysis.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct TailCallStats {
    /// Number of self-recursive tail calls found.
    pub self_tail_calls: usize,
    /// Number of mutually recursive tail calls found.
    pub mutual_tail_calls: usize,
    /// Total Apply expressions encountered.
    pub total_apply_calls: usize,
    /// Total ClosureApply expressions encountered.
    pub total_closure_calls: usize,
}

// -----------------------------------------------------------------------
// Analysis result
// -----------------------------------------------------------------------

/// Result of tail call analysis for a single function.
#[derive(Clone, Debug)]
pub(crate) struct TailCallAnalysis {
    /// Name of the analyzed function.
    pub fn_name: Name,
    /// VarIds of VDecl nodes containing tail calls.
    pub tail_call_vars: HashSet<VarId>,
    /// Collected statistics.
    pub stats: TailCallStats,
}

impl TailCallAnalysis {
    /// True if any tail calls (self or mutual) were detected.
    #[must_use]
    pub fn has_tail_calls(&self) -> bool {
        !self.tail_call_vars.is_empty()
    }

    /// Total number of tail calls detected.
    #[must_use]
    pub fn tail_call_count(&self) -> usize {
        self.stats.self_tail_calls + self.stats.mutual_tail_calls
    }
}

// -----------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------

/// Analyze a single IRDecl for tail calls (self-recursion only).
///
/// Returns a `TailCallAnalysis` describing which VDecl positions contain
/// tail calls and associated statistics.
#[must_use]
pub(crate) fn analyze_tail_calls(decl: &IRDecl, config: &TailCallConfig) -> TailCallAnalysis {
    let mutual_fns = HashSet::new();
    analyze_tail_calls_inner(decl, config, &mutual_fns)
}

/// Analyze mutual tail calls across a set of declarations.
///
/// Each declaration is analyzed with knowledge of all function names in
/// the set, so that calls between them can be marked as mutual tail calls.
#[must_use]
pub(crate) fn analyze_mutual_tail_calls(
    decls: &[IRDecl],
    config: &TailCallConfig,
) -> Vec<TailCallAnalysis> {
    if !config.enabled {
        return decls
            .iter()
            .map(|d| TailCallAnalysis {
                fn_name: d.name.clone(),
                tail_call_vars: HashSet::new(),
                stats: TailCallStats::default(),
            })
            .collect();
    }

    let mutual_fns: HashSet<Name> = if config.detect_mutual {
        decls.iter().map(|d| d.name.clone()).collect()
    } else {
        HashSet::new()
    };

    decls
        .iter()
        .map(|d| analyze_tail_calls_inner(d, config, &mutual_fns))
        .collect()
}

// -----------------------------------------------------------------------
// Internal implementation
// -----------------------------------------------------------------------

fn analyze_tail_calls_inner(
    decl: &IRDecl,
    config: &TailCallConfig,
    mutual_fns: &HashSet<Name>,
) -> TailCallAnalysis {
    let mut tail_vars = HashSet::new();
    let mut stats = TailCallStats::default();

    if config.enabled {
        // First pass: count total calls for statistics.
        count_all_calls(&decl.body, &mut stats);

        // Second pass: collect join points jumped to from tail positions.
        let tail_jps = collect_tail_join_points(&decl.body);

        // Third pass: find tail calls.
        find_tail_calls(
            &decl.body,
            &decl.name,
            mutual_fns,
            &tail_jps,
            &mut tail_vars,
            &mut stats,
        );
    }

    TailCallAnalysis {
        fn_name: decl.name.clone(),
        tail_call_vars: tail_vars,
        stats,
    }
}

/// Check whether `rest` only performs RC operations on variables other than
/// `var` before returning `var`. This is the key tail-position test.
///
/// Allowed intermediate operations: Inc, Dec, SetTag on variables != `var`.
fn rest_returns_var(var: VarId, rest: &IRBody) -> bool {
    match rest {
        IRBody::Ret(IRArg::Var(v)) => *v == var,
        IRBody::Inc {
            var: inc_var,
            rest: inner,
            ..
        } => *inc_var != var && rest_returns_var(var, inner),
        IRBody::Dec {
            var: dec_var,
            rest: inner,
        } => *dec_var != var && rest_returns_var(var, inner),
        IRBody::SetTag {
            var: tag_var,
            rest: inner,
            ..
        } => *tag_var != var && rest_returns_var(var, inner),
        _ => false,
    }
}

/// Check if an expression is a function call (Apply or ClosureApply).
fn is_call_expr(expr: &IRExpr) -> bool {
    matches!(expr, IRExpr::Apply { .. } | IRExpr::ClosureApply { .. })
}

/// Extract the FnId from an Apply expression, if any.
fn call_fn_id(expr: &IRExpr) -> Option<&FnId> {
    match expr {
        IRExpr::Apply { fn_id, .. } => Some(fn_id),
        _ => None,
    }
}

/// Classify a tail-position call as self, mutual, or neither and update stats.
fn classify_tail_call(
    expr: &IRExpr,
    fn_name: &Name,
    mutual_fns: &HashSet<Name>,
    stats: &mut TailCallStats,
) -> bool {
    if let Some(called_fn) = call_fn_id(expr) {
        if called_fn.0 == *fn_name {
            stats.self_tail_calls += 1;
            return true;
        }
        if mutual_fns.contains(&called_fn.0) && called_fn.0 != *fn_name {
            stats.mutual_tail_calls += 1;
            return true;
        }
    }
    // ClosureApply is a dynamic call; we cannot know the target statically,
    // so we do not mark it as a tail call (backends would need runtime
    // support for tail-calling closures).
    false
}

/// Find tail calls in a body, given the function's own name and the set of
/// mutual function names.
fn find_tail_calls(
    body: &IRBody,
    fn_name: &Name,
    mutual_fns: &HashSet<Name>,
    tail_jps: &HashSet<JoinPointId>,
    tail_vars: &mut HashSet<VarId>,
    stats: &mut TailCallStats,
) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            // Check if this VDecl is a call in tail position.
            if is_call_expr(value)
                && rest_returns_var(*var, rest)
                && classify_tail_call(value, fn_name, mutual_fns, stats)
            {
                tail_vars.insert(*var);
            }
            // Continue searching in rest (for case arms reached later, etc.)
            find_tail_calls(rest, fn_name, mutual_fns, tail_jps, tail_vars, stats);
        }
        IRBody::JDecl {
            jp,
            body: jp_body,
            rest,
            ..
        } => {
            // A join point's body is in tail position only if the JP is
            // jumped to exclusively from tail positions.
            if tail_jps.contains(jp) {
                find_tail_calls(jp_body, fn_name, mutual_fns, tail_jps, tail_vars, stats);
            }
            find_tail_calls(rest, fn_name, mutual_fns, tail_jps, tail_vars, stats);
        }
        IRBody::Case { alts, default, .. } => {
            // Each case arm is in tail position if the Case itself is.
            for alt in alts {
                find_tail_calls(&alt.body, fn_name, mutual_fns, tail_jps, tail_vars, stats);
            }
            if let Some(def) = default {
                find_tail_calls(def, fn_name, mutual_fns, tail_jps, tail_vars, stats);
            }
        }
        // RC operations pass through — continue to rest.
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            find_tail_calls(rest, fn_name, mutual_fns, tail_jps, tail_vars, stats);
        }
        // Terminals: nothing to do.
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Count total Apply and ClosureApply calls in a body for statistics.
fn count_all_calls(body: &IRBody, stats: &mut TailCallStats) {
    match body {
        IRBody::VDecl { value, rest, .. } => {
            match value {
                IRExpr::Apply { .. } => stats.total_apply_calls += 1,
                IRExpr::ClosureApply { .. } => stats.total_closure_calls += 1,
                _ => {}
            }
            count_all_calls(rest, stats);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            count_all_calls(jp_body, stats);
            count_all_calls(rest, stats);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            count_all_calls(rest, stats);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                count_all_calls(&alt.body, stats);
            }
            if let Some(def) = default {
                count_all_calls(def, stats);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Collect join points that are only jumped to from tail positions.
///
/// A join point is in a tail position if every Jmp to it appears as the
/// terminal of another tail-position block. We approximate this
/// conservatively: a JP is tail if it is only jumped to from:
/// - The tail position of Case arms
/// - After RC operations in tail position
///
/// We over-approximate by marking a JP as tail unless we find a Jmp to it
/// in a non-tail context.
fn collect_tail_join_points(body: &IRBody) -> HashSet<JoinPointId> {
    let mut all_jps = HashSet::new();
    let mut non_tail_jps = HashSet::new();

    // Collect all JP declarations.
    collect_jp_ids(body, &mut all_jps);

    // Find JPs that appear in non-tail contexts.
    mark_non_tail_jps(body, true, &mut non_tail_jps);

    // JPs not in non_tail set are tail-position JPs.
    all_jps.difference(&non_tail_jps).copied().collect()
}

/// Collect all JoinPointId declarations in the body.
fn collect_jp_ids(body: &IRBody, jps: &mut HashSet<JoinPointId>) {
    match body {
        IRBody::JDecl {
            jp,
            body: jp_body,
            rest,
            ..
        } => {
            jps.insert(*jp);
            collect_jp_ids(jp_body, jps);
            collect_jp_ids(rest, jps);
        }
        IRBody::VDecl { rest, .. }
        | IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            collect_jp_ids(rest, jps);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts {
                collect_jp_ids(&alt.body, jps);
            }
            if let Some(def) = default {
                collect_jp_ids(def, jps);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

/// Walk the body and mark JPs that are jumped to from non-tail contexts.
/// `is_tail` tracks whether the current position is in tail position.
fn mark_non_tail_jps(body: &IRBody, is_tail: bool, non_tail: &mut HashSet<JoinPointId>) {
    match body {
        IRBody::VDecl { rest, .. } => {
            // The VDecl's rest inherits the tail context.
            mark_non_tail_jps(rest, is_tail, non_tail);
        }
        IRBody::JDecl {
            body: jp_body,
            rest,
            ..
        } => {
            // JP body inherits tail (we handle it separately in find_tail_calls).
            mark_non_tail_jps(jp_body, is_tail, non_tail);
            mark_non_tail_jps(rest, is_tail, non_tail);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => {
            mark_non_tail_jps(rest, is_tail, non_tail);
        }
        IRBody::Case { alts, default, .. } => {
            // Case arms are in tail position if the Case itself is.
            for alt in alts {
                mark_non_tail_jps(&alt.body, is_tail, non_tail);
            }
            if let Some(def) = default {
                mark_non_tail_jps(def, is_tail, non_tail);
            }
        }
        IRBody::Jmp { jp, .. } => {
            if !is_tail {
                non_tail.insert(*jp);
            }
        }
        IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}
