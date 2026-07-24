// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended optimization analysis and orchestration for L5CNF.
//!
//! Builds on [`crate::opt`] with pass profiling, optimization statistics,
//! pass ordering analysis, fixed-point detection, human-readable reports,
//! per-pass configuration, and IR size tracking through the pipeline.
//!
//! Part of #3082 - Compiler optimization extensions.

use std::collections::HashMap;
use std::time::Duration;

use crate::lcnf::{Code, Decl, DeclValue, LetValue};
use crate::opt::OptConfig;

/// Errors from the extended optimization module.
#[derive(Debug, thiserror::Error)]
pub(crate) enum OptExtError {
    #[error("pass `{name}` not found in registry")]
    PassNotFound { name: String },
    #[error("invalid priority {priority} for pass `{name}`: must be > 0")]
    InvalidPriority { name: String, priority: u32 },
    #[error("duplicate pass name: `{0}`")]
    DuplicatePass(String),
    #[error("empty pipeline: no passes configured")]
    EmptyPipeline,
}

// ---------------------------------------------------------------------------
// Pass identification
// ---------------------------------------------------------------------------

/// Named optimization pass for tracking and configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum OptPassId {
    Dce,
    Cse,
    ConstantFold,
    SimpValue,
    Inline,
    JoinPoints,
    Specialize,
    LambdaLift,
    ExtractClosed,
    PullLetDecls,
}

impl OptPassId {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Dce => "dce",
            Self::Cse => "cse",
            Self::ConstantFold => "constant_fold",
            Self::SimpValue => "simp_value",
            Self::Inline => "inline",
            Self::JoinPoints => "join_points",
            Self::Specialize => "specialize",
            Self::LambdaLift => "lambda_lift",
            Self::ExtractClosed => "extract_closed",
            Self::PullLetDecls => "pull_let_decls",
        }
    }

    /// All pass IDs in default pipeline order.
    pub(crate) fn all() -> &'static [OptPassId] {
        &[
            Self::LambdaLift,
            Self::ExtractClosed,
            Self::Specialize,
            Self::PullLetDecls,
            Self::Dce,
            Self::Cse,
            Self::ConstantFold,
            Self::SimpValue,
            Self::Inline,
            Self::JoinPoints,
        ]
    }

    /// Iterative passes (run in the fixpoint loop).
    pub(crate) fn iterative_passes() -> &'static [OptPassId] {
        &[
            Self::Dce,
            Self::Cse,
            Self::ConstantFold,
            Self::SimpValue,
            Self::Inline,
        ]
    }

    /// Batch-only passes (run once, before/after the loop).
    pub(crate) fn batch_passes() -> &'static [OptPassId] {
        &[
            Self::LambdaLift,
            Self::ExtractClosed,
            Self::Specialize,
            Self::PullLetDecls,
        ]
    }

    /// Finalization passes (run once after the loop).
    pub(crate) fn finalization_passes() -> &'static [OptPassId] {
        &[Self::JoinPoints]
    }
}

// ---------------------------------------------------------------------------
// Per-pass statistics
// ---------------------------------------------------------------------------

/// Statistics for one invocation of a pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct PassProfile {
    pub(crate) duration: Duration,
    pub(crate) ir_size_before: usize,
    pub(crate) ir_size_after: usize,
    pub(crate) changed: bool,
}

impl PassProfile {
    #[must_use]
    pub(crate) fn size_delta(&self) -> isize {
        self.ir_size_after as isize - self.ir_size_before as isize
    }

    #[must_use]
    pub(crate) fn shrank(&self) -> bool {
        self.ir_size_after < self.ir_size_before
    }
}

/// Aggregated statistics across multiple runs of a single pass.
#[derive(Debug, Clone, Default)]
pub(crate) struct PassAggregateStats {
    pub(crate) invocations: u32,
    pub(crate) total_duration: Duration,
    pub(crate) total_size_delta: isize,
    pub(crate) times_changed: u32,
    pub(crate) times_shrank: u32,
}

// ---------------------------------------------------------------------------
// Optimization statistics collector
// ---------------------------------------------------------------------------

/// Tracks detailed statistics about all optimization passes in a pipeline run.
#[derive(Debug, Clone, Default)]
pub(crate) struct OptimizationStats {
    pub(crate) profiles: Vec<(OptPassId, PassProfile)>,
    pub(crate) total_duration: Duration,
    pub(crate) iterations: u32,
    pub(crate) reached_fixpoint: bool,
    pub(crate) initial_ir_size: usize,
    pub(crate) final_ir_size: usize,
}

impl OptimizationStats {
    /// Aggregate statistics per pass type.
    #[must_use]
    pub(crate) fn aggregate_by_pass(&self) -> HashMap<OptPassId, PassAggregateStats> {
        let mut map: HashMap<OptPassId, PassAggregateStats> = HashMap::new();
        for (id, profile) in &self.profiles {
            let agg = map.entry(*id).or_default();
            agg.invocations += 1;
            agg.total_duration += profile.duration;
            agg.total_size_delta += profile.size_delta();
            if profile.changed {
                agg.times_changed += 1;
            }
            if profile.shrank() {
                agg.times_shrank += 1;
            }
        }
        map
    }

    #[must_use]
    pub(crate) fn total_size_delta(&self) -> isize {
        self.final_ir_size as isize - self.initial_ir_size as isize
    }

    /// Passes that never changed the IR.
    #[must_use]
    pub(crate) fn ineffective_passes(&self) -> Vec<OptPassId> {
        let agg = self.aggregate_by_pass();
        let mut result: Vec<OptPassId> = agg
            .iter()
            .filter(|(_, s)| s.times_changed == 0)
            .map(|(&id, _)| id)
            .collect();
        result.sort_by_key(|id| id.name());
        result
    }
}

// ---------------------------------------------------------------------------
// IR size measurement for Code (L5CNF)
// ---------------------------------------------------------------------------

/// Count the number of nodes in an L5CNF Code tree.
#[must_use]
pub(crate) fn count_code_nodes(code: &Code) -> usize {
    match code {
        Code::Let(let_decl, rest) => {
            1 + count_let_value_nodes(&let_decl.value) + count_code_nodes(rest)
        }
        Code::Fun(fun_decl, rest) => 1 + count_code_nodes(&fun_decl.body) + count_code_nodes(rest),
        Code::JoinPoint(fun_decl, rest) => {
            1 + count_code_nodes(&fun_decl.body) + count_code_nodes(rest)
        }
        Code::Cases(cases) => {
            1 + cases
                .alts
                .iter()
                .map(|a| count_code_nodes(a.body()))
                .sum::<usize>()
        }
        Code::Jmp { args, .. } => 1 + args.len(),
        Code::Return(_) | Code::Unreachable(_) => 1,
    }
}

fn count_let_value_nodes(value: &LetValue) -> usize {
    match value {
        LetValue::Erased | LetValue::Lit(_) | LetValue::Proj { .. } => 1,
        LetValue::Const { args, .. }
        | LetValue::FVar { args, .. }
        | LetValue::Ctor { args, .. }
        | LetValue::Reuse { args, .. } => 1 + args.len(),
    }
}

/// Count the total IR size of a declaration.
#[must_use]
pub(crate) fn decl_code_size(decl: &Decl) -> usize {
    match &decl.body {
        DeclValue::Code(code) => count_code_nodes(code),
        DeclValue::Extern(_) => 0,
    }
}

/// Count total IR size across a batch of declarations.
#[must_use]
pub(crate) fn batch_code_size(decls: &[Decl]) -> usize {
    decls.iter().map(decl_code_size).sum()
}

// ---------------------------------------------------------------------------
// Fixed-point detection
// ---------------------------------------------------------------------------

/// Result of a single optimization iteration.
#[derive(Debug, Clone)]
pub(crate) struct IterationResult {
    pub(crate) iteration: u32,
    pub(crate) size_before: usize,
    pub(crate) size_after: usize,
    pub(crate) changed: bool,
}

/// Detect whether a pipeline has reached a fixed point.
#[must_use]
pub(crate) fn detect_fixpoint(before: &Code, after: &Code) -> bool {
    before == after
}

/// Detect fixpoint for a batch of declarations.
#[must_use]
pub(crate) fn detect_fixpoint_batch(before: &[Decl], after: &[Decl]) -> bool {
    before.len() == after.len() && before.iter().zip(after.iter()).all(|(b, a)| b == a)
}

// ---------------------------------------------------------------------------
// Pass ordering analysis
// ---------------------------------------------------------------------------

/// Suggested dependency between two passes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PassDependency {
    pub(crate) before: OptPassId,
    pub(crate) after: OptPassId,
    pub(crate) reason: &'static str,
}

/// Return the known ordering dependencies between passes.
#[must_use]
pub(crate) fn known_pass_dependencies() -> Vec<PassDependency> {
    vec![
        PassDependency {
            before: OptPassId::Dce,
            after: OptPassId::Cse,
            reason: "DCE removes dead bindings that would pollute CSE hash maps",
        },
        PassDependency {
            before: OptPassId::Cse,
            after: OptPassId::ConstantFold,
            reason: "CSE deduplicates expressions before constant evaluation",
        },
        PassDependency {
            before: OptPassId::ConstantFold,
            after: OptPassId::SimpValue,
            reason: "constant folding creates values that simp_value can simplify",
        },
        PassDependency {
            before: OptPassId::SimpValue,
            after: OptPassId::Inline,
            reason: "simplified values reduce inlined function body size",
        },
        PassDependency {
            before: OptPassId::LambdaLift,
            after: OptPassId::Specialize,
            reason: "lambda lifting must expose top-level functions before specialization",
        },
        PassDependency {
            before: OptPassId::Specialize,
            after: OptPassId::Dce,
            reason: "specialization may make generic versions dead",
        },
    ]
}

/// Check whether a given pass ordering respects all known dependencies.
#[must_use]
pub(crate) fn check_pass_order(order: &[OptPassId]) -> Vec<PassDependency> {
    let deps = known_pass_dependencies();
    let pos: HashMap<OptPassId, usize> = order.iter().enumerate().map(|(i, &id)| (id, i)).collect();
    deps.into_iter()
        .filter(|dep| match (pos.get(&dep.before), pos.get(&dep.after)) {
            (Some(&b), Some(&a)) => b >= a,
            _ => false,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Pass configuration
// ---------------------------------------------------------------------------

/// Per-pass enable/disable with priority settings.
#[derive(Debug, Clone)]
pub(crate) struct PassConfig {
    pub(crate) id: OptPassId,
    pub(crate) enabled: bool,
    pub(crate) priority: u32,
}

impl PassConfig {
    pub(crate) fn new(id: OptPassId) -> Self {
        Self {
            id,
            enabled: true,
            priority: 100,
        }
    }

    #[must_use]
    pub(crate) fn with_enabled(mut self, enabled: bool) -> Self {
        self.enabled = enabled;
        self
    }

    #[must_use]
    pub(crate) fn with_priority(mut self, priority: u32) -> Self {
        self.priority = priority;
        self
    }
}

/// Extended pipeline configuration wrapping OptConfig with per-pass controls.
#[derive(Debug, Clone)]
pub(crate) struct ExtOptConfig {
    pub(crate) base: OptConfig,
    pub(crate) pass_configs: Vec<PassConfig>,
    pub(crate) profiling: bool,
    pub(crate) bloat_warn_percent: f64,
}

impl Default for ExtOptConfig {
    fn default() -> Self {
        Self {
            base: OptConfig::default(),
            pass_configs: Vec::new(),
            profiling: false,
            bloat_warn_percent: 20.0,
        }
    }
}

impl ExtOptConfig {
    /// Check whether a pass is enabled (per-pass override, then base config).
    #[must_use]
    pub(crate) fn is_pass_enabled(&self, id: OptPassId) -> bool {
        if let Some(pc) = self.pass_configs.iter().find(|c| c.id == id) {
            return pc.enabled;
        }
        match id {
            OptPassId::Dce => self.base.enable_dce,
            OptPassId::Cse => self.base.enable_cse,
            OptPassId::ConstantFold => self.base.enable_constant_fold,
            OptPassId::SimpValue => self.base.enable_simp_value,
            OptPassId::Inline => self.base.enable_inline,
            OptPassId::JoinPoints => self.base.enable_join_points,
            OptPassId::Specialize => self.base.enable_specialize,
            OptPassId::LambdaLift => self.base.enable_lambda_lift,
            OptPassId::ExtractClosed => self.base.enable_extract_closed,
            OptPassId::PullLetDecls => self.base.enable_pull_let_decls,
        }
    }

    #[must_use]
    pub(crate) fn pass_priority(&self, id: OptPassId) -> u32 {
        self.pass_configs
            .iter()
            .find(|c| c.id == id)
            .map(|c| c.priority)
            .unwrap_or(100)
    }

    /// Return iterative passes sorted by priority (descending).
    #[must_use]
    pub(crate) fn sorted_iterative_passes(&self) -> Vec<OptPassId> {
        let mut passes: Vec<OptPassId> = OptPassId::iterative_passes()
            .iter()
            .copied()
            .filter(|&id| self.is_pass_enabled(id))
            .collect();
        passes.sort_by_key(|b| std::cmp::Reverse(self.pass_priority(*b)));
        passes
    }

    pub(crate) fn validate(&self) -> Result<(), OptExtError> {
        for pc in &self.pass_configs {
            if pc.priority == 0 {
                return Err(OptExtError::InvalidPriority {
                    name: pc.id.name().to_owned(),
                    priority: pc.priority,
                });
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// IR size tracking
// ---------------------------------------------------------------------------

/// A snapshot of IR sizes at a point in the pipeline.
#[derive(Debug, Clone)]
pub(crate) struct IrSizeSnapshot {
    pub(crate) label: String,
    pub(crate) total_nodes: usize,
    pub(crate) decl_count: usize,
}

/// Track IR size through the optimization pipeline to detect code bloat.
#[derive(Debug, Clone, Default)]
pub(crate) struct IrSizeTracker {
    pub(crate) snapshots: Vec<IrSizeSnapshot>,
}

impl IrSizeTracker {
    pub(crate) fn new() -> Self {
        Self {
            snapshots: Vec::new(),
        }
    }

    pub(crate) fn record(&mut self, label: &str, decls: &[Decl]) {
        self.snapshots.push(IrSizeSnapshot {
            label: label.to_owned(),
            total_nodes: batch_code_size(decls),
            decl_count: decls.len(),
        });
    }

    pub(crate) fn record_single(&mut self, label: &str, code: &Code) {
        self.snapshots.push(IrSizeSnapshot {
            label: label.to_owned(),
            total_nodes: count_code_nodes(code),
            decl_count: 1,
        });
    }

    #[must_use]
    pub(crate) fn peak_size(&self) -> usize {
        self.snapshots
            .iter()
            .map(|s| s.total_nodes)
            .max()
            .unwrap_or(0)
    }

    /// Detect bloat above the given percentage relative to previous snapshot.
    #[must_use]
    pub(crate) fn bloat_warnings(&self, threshold_percent: f64) -> Vec<(String, f64)> {
        let mut warnings = Vec::new();
        for w in self.snapshots.windows(2) {
            let (prev, curr) = (w[0].total_nodes, w[1].total_nodes);
            if prev > 0 && curr > prev {
                let pct = ((curr - prev) as f64 / prev as f64) * 100.0;
                if pct > threshold_percent {
                    warnings.push((w[1].label.clone(), pct));
                }
            }
        }
        warnings
    }

    #[must_use]
    pub(crate) fn total_delta(&self) -> isize {
        match (self.snapshots.first(), self.snapshots.last()) {
            (Some(f), Some(l)) => l.total_nodes as isize - f.total_nodes as isize,
            _ => 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Optimization report
// ---------------------------------------------------------------------------

/// Generate a human-readable report of optimization results.
#[must_use]
pub(crate) fn generate_report(stats: &OptimizationStats, tracker: &IrSizeTracker) -> String {
    let mut r = String::from("=== Optimization Report ===\n\n");
    r.push_str(&format!(
        "Iterations: {} (fixpoint: {})\n",
        stats.iterations,
        if stats.reached_fixpoint { "yes" } else { "no" }
    ));
    r.push_str(&format!(
        "IR size: {} -> {} (delta: {:+})\n",
        stats.initial_ir_size,
        stats.final_ir_size,
        stats.total_size_delta()
    ));
    r.push_str(&format!(
        "Total time: {:.3}ms\n\n",
        stats.total_duration.as_secs_f64() * 1000.0
    ));

    let agg = stats.aggregate_by_pass();
    if !agg.is_empty() {
        r.push_str("--- Pass Statistics ---\n");
        let mut sorted: Vec<_> = agg.iter().collect();
        sorted.sort_by_key(|(id, _)| id.name());
        for (id, s) in &sorted {
            r.push_str(&format!(
                "  {:16} invocations={:3}  changed={:3}  shrank={:3}  \
                delta={:+6}  time={:.3}ms\n",
                id.name(),
                s.invocations,
                s.times_changed,
                s.times_shrank,
                s.total_size_delta,
                s.total_duration.as_secs_f64() * 1000.0
            ));
        }
        r.push('\n');
    }

    let ineffective = stats.ineffective_passes();
    if !ineffective.is_empty() {
        let names: Vec<&str> = ineffective.iter().map(|id| id.name()).collect();
        r.push_str(&format!(
            "Ineffective passes (never changed IR): {}\n\n",
            names.join(", ")
        ));
    }

    let warnings = tracker.bloat_warnings(10.0);
    if !warnings.is_empty() {
        r.push_str("--- Bloat Warnings ---\n");
        for (label, pct) in &warnings {
            r.push_str(&format!("  {} increased IR by {:.1}%\n", label, pct));
        }
        r.push('\n');
    }

    if tracker.snapshots.len() > 1 {
        r.push_str("--- Size Trace ---\n");
        for snap in &tracker.snapshots {
            r.push_str(&format!(
                "  {:20} nodes={:6}  decls={}\n",
                snap.label, snap.total_nodes, snap.decl_count
            ));
        }
    }
    r
}
