// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IO monad analysis: effect classification, purity checking,
//! effect ordering, IO statistics, sandboxing analysis, effect boundary
//! detection, and IO operation cost modeling.
//!
//! This module provides static analysis over IO expression trees to support
//! optimization decisions (parallelization, sandboxing) and correctness
//! checking (purity enforcement, effect ordering).
//!
//! Reference: Lean 4 `src/Init/System/IO.lean`, `src/Init/Control/`.

use crate::error::ElabError;
use clean_parser::SurfaceExpr;

// ---------------------------------------------------------------------------
// Effect classification
// ---------------------------------------------------------------------------

/// Classification of IO effects by category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum EffectKind {
    /// Console read (stdin, getLine).
    Read,
    /// Console write (stdout, stderr, println, print).
    Write,
    /// Network operations (sockets, HTTP).
    Network,
    /// Process management (spawn, exit, run).
    Process,
    /// Filesystem operations (readFile, writeFile, removeFile, readDir).
    Filesystem,
    /// Mutable reference operations (IORef.get, set, modify, swap).
    MutableRef,
    /// Environment queries (getEnv, getCwd).
    Environment,
    /// Task/concurrency operations (Task.spawn, Task.get).
    Concurrency,
    /// Error handling (throw, catch, tryCatch, tryFinally).
    ErrorHandling,
    /// Pure operation wrapped in IO (IO.pure, IO.map).
    Pure,
}

impl std::fmt::Display for EffectKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EffectKind::Read => write!(f, "read"),
            EffectKind::Write => write!(f, "write"),
            EffectKind::Network => write!(f, "network"),
            EffectKind::Process => write!(f, "process"),
            EffectKind::Filesystem => write!(f, "filesystem"),
            EffectKind::MutableRef => write!(f, "mutable-ref"),
            EffectKind::Environment => write!(f, "environment"),
            EffectKind::Concurrency => write!(f, "concurrency"),
            EffectKind::ErrorHandling => write!(f, "error-handling"),
            EffectKind::Pure => write!(f, "pure"),
        }
    }
}

/// Classify an IO operation name into its effect kind.
#[must_use]
pub(crate) fn classify_effect(op_name: &str) -> Option<EffectKind> {
    match op_name {
        "IO.getLine" => Some(EffectKind::Read),

        "IO.println" | "IO.print" | "IO.eprintln" => Some(EffectKind::Write),

        "IO.Process.run" | "IO.Process.spawn" | "IO.Process.exit" => Some(EffectKind::Process),

        "IO.FS.readFile" | "IO.FS.writeFile" | "IO.FS.removeFile" | "IO.FS.readDir" => {
            Some(EffectKind::Filesystem)
        }

        "IO.Ref.new" | "IO.Ref.get" | "IO.Ref.set" | "IO.Ref.modify" | "IORef.mk" | "IORef.get"
        | "IORef.set" | "IORef.modify" | "IORef.swap" => Some(EffectKind::MutableRef),

        "IO.getEnv" | "IO.getCwd" | "IO.currentDir" => Some(EffectKind::Environment),

        "Task.spawn" | "Task.get" => Some(EffectKind::Concurrency),

        "IO.throw" | "IO.catch" | "IO.tryCatch" | "IO.tryFinally" => {
            Some(EffectKind::ErrorHandling)
        }

        "IO.pure" | "IO.map" | "IO.bind" => Some(EffectKind::Pure),

        "IO.monoMsNow" | "IO.panic" => Some(EffectKind::Process),

        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Sandboxing level
// ---------------------------------------------------------------------------

/// Sandboxing requirement for an IO effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub(crate) enum SandboxLevel {
    /// No sandboxing needed (pure, environment reads).
    None,
    /// Light sandboxing (console IO, mutable refs).
    Light,
    /// Medium sandboxing (filesystem, error handling).
    Medium,
    /// Heavy sandboxing (process spawn, network, concurrency).
    Heavy,
}

/// Determine sandboxing level for a given effect kind.
#[must_use]
pub(crate) fn sandbox_level(kind: EffectKind) -> SandboxLevel {
    match kind {
        EffectKind::Pure => SandboxLevel::None,
        EffectKind::Environment | EffectKind::Read => SandboxLevel::Light,
        EffectKind::Write | EffectKind::MutableRef | EffectKind::ErrorHandling => {
            SandboxLevel::Light
        }
        EffectKind::Filesystem => SandboxLevel::Medium,
        EffectKind::Process | EffectKind::Network | EffectKind::Concurrency => SandboxLevel::Heavy,
    }
}

// ---------------------------------------------------------------------------
// IO operation cost model
// ---------------------------------------------------------------------------

/// Relative cost estimate for an IO operation (arbitrary units).
///
/// Used by the optimizer to decide inlining and batching thresholds.
/// Higher values mean more expensive.
#[must_use]
pub(crate) fn operation_cost(kind: EffectKind) -> u32 {
    match kind {
        EffectKind::Pure => 1,
        EffectKind::MutableRef => 2,
        EffectKind::ErrorHandling => 3,
        EffectKind::Read | EffectKind::Write => 10,
        EffectKind::Environment => 10,
        EffectKind::Filesystem => 100,
        EffectKind::Process => 500,
        EffectKind::Concurrency => 200,
        EffectKind::Network => 1000,
    }
}

// ---------------------------------------------------------------------------
// IO statistics
// ---------------------------------------------------------------------------

/// Aggregated statistics from an IO expression analysis pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct IoStats {
    pub(crate) total_ops: usize,
    pub(crate) read_count: usize,
    pub(crate) write_count: usize,
    pub(crate) network_count: usize,
    pub(crate) process_count: usize,
    pub(crate) filesystem_count: usize,
    pub(crate) mutable_ref_count: usize,
    pub(crate) environment_count: usize,
    pub(crate) concurrency_count: usize,
    pub(crate) error_handling_count: usize,
    pub(crate) pure_count: usize,
}

impl IoStats {
    /// Total "effect surface area": count of non-pure operations.
    #[must_use]
    pub(crate) fn effect_surface_area(&self) -> usize {
        self.total_ops.saturating_sub(self.pure_count)
    }

    /// Maximum sandbox level required by any operation in the stats.
    #[must_use]
    pub(crate) fn max_sandbox_level(&self) -> SandboxLevel {
        if self.network_count > 0 || self.process_count > 0 || self.concurrency_count > 0 {
            SandboxLevel::Heavy
        } else if self.filesystem_count > 0 {
            SandboxLevel::Medium
        } else if self.read_count > 0
            || self.write_count > 0
            || self.mutable_ref_count > 0
            || self.error_handling_count > 0
            || self.environment_count > 0
        {
            SandboxLevel::Light
        } else {
            SandboxLevel::None
        }
    }

    /// Total estimated cost across all operations.
    #[must_use]
    pub(crate) fn total_cost(&self) -> u64 {
        let costs: &[(usize, EffectKind)] = &[
            (self.read_count, EffectKind::Read),
            (self.write_count, EffectKind::Write),
            (self.network_count, EffectKind::Network),
            (self.process_count, EffectKind::Process),
            (self.filesystem_count, EffectKind::Filesystem),
            (self.mutable_ref_count, EffectKind::MutableRef),
            (self.environment_count, EffectKind::Environment),
            (self.concurrency_count, EffectKind::Concurrency),
            (self.error_handling_count, EffectKind::ErrorHandling),
            (self.pure_count, EffectKind::Pure),
        ];
        costs
            .iter()
            .map(|(count, kind)| *count as u64 * operation_cost(*kind) as u64)
            .sum()
    }

    fn record(&mut self, kind: EffectKind) {
        self.total_ops += 1;
        match kind {
            EffectKind::Read => self.read_count += 1,
            EffectKind::Write => self.write_count += 1,
            EffectKind::Network => self.network_count += 1,
            EffectKind::Process => self.process_count += 1,
            EffectKind::Filesystem => self.filesystem_count += 1,
            EffectKind::MutableRef => self.mutable_ref_count += 1,
            EffectKind::Environment => self.environment_count += 1,
            EffectKind::Concurrency => self.concurrency_count += 1,
            EffectKind::ErrorHandling => self.error_handling_count += 1,
            EffectKind::Pure => self.pure_count += 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Effect boundary detection
// ---------------------------------------------------------------------------

/// A boundary point where code transitions between pure and effectful.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectBoundary {
    /// Name of the IO operation at the boundary (if identified).
    pub(crate) operation: String,
    /// The effect entering at this boundary.
    pub(crate) entering_effect: EffectKind,
    /// Whether this boundary transitions from pure to effectful.
    pub(crate) pure_to_effectful: bool,
}

// ---------------------------------------------------------------------------
// Effect ordering (parallelizability)
// ---------------------------------------------------------------------------

/// Whether two effect kinds can safely run in parallel.
///
/// Conservative: only returns `true` when there is provably no data
/// dependency or ordering constraint between the two effect kinds.
#[must_use]
pub(crate) fn effects_parallelizable(a: EffectKind, b: EffectKind) -> bool {
    match (a, b) {
        // Pure operations can always run in parallel with anything.
        (EffectKind::Pure, _) | (_, EffectKind::Pure) => true,

        // Two reads are safe to parallelize.
        (EffectKind::Read, EffectKind::Read) => true,

        // Environment queries are read-only and parallelizable with each other
        // and with reads/writes.
        (EffectKind::Environment, EffectKind::Environment) => true,
        (EffectKind::Environment, EffectKind::Read)
        | (EffectKind::Read, EffectKind::Environment) => true,

        // Writes to different streams might be safe, but stdout ordering
        // matters so we conservatively say no.
        // MutableRef operations must be sequenced.
        // Filesystem, Process, Network, Concurrency must be sequenced.
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Expression analysis
// ---------------------------------------------------------------------------

/// Errors specific to IO monad ext2 analysis.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum IoMonadExt2Error {
    #[error("effect analysis depth exceeded maximum {max}")]
    DepthExceeded { max: usize },
    #[error("unrecognized IO operation in analysis: {0}")]
    UnrecognizedOp(String),
}

impl From<IoMonadExt2Error> for ElabError {
    fn from(err: IoMonadExt2Error) -> Self {
        ElabError::NotImplemented(err.to_string())
    }
}

/// Maximum recursion depth for expression analysis.
const MAX_ANALYSIS_DEPTH: usize = 256;

/// Collect IO statistics from an expression tree.
///
/// Walks the expression recursively, classifying every IO operation it
/// encounters and accumulating counts into `IoStats`.
pub(crate) fn collect_io_stats(expr: &SurfaceExpr) -> Result<IoStats, IoMonadExt2Error> {
    let mut stats = IoStats::default();
    collect_stats_inner(expr, &mut stats, 0)?;
    Ok(stats)
}

fn collect_stats_inner(
    expr: &SurfaceExpr,
    stats: &mut IoStats,
    depth: usize,
) -> Result<(), IoMonadExt2Error> {
    if depth > MAX_ANALYSIS_DEPTH {
        return Err(IoMonadExt2Error::DepthExceeded {
            max: MAX_ANALYSIS_DEPTH,
        });
    }
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if let Some(kind) = classify_effect(name) {
                    stats.record(kind);
                }
            }
            collect_stats_inner(func, stats, depth + 1)?;
            for arg in args {
                collect_stats_inner(&arg.expr, stats, depth + 1)?;
            }
            Ok(())
        }
        SurfaceExpr::Lambda(_, _, body) => collect_stats_inner(body, stats, depth + 1),
        SurfaceExpr::Let(_, _, val, body) => {
            collect_stats_inner(val, stats, depth + 1)?;
            collect_stats_inner(body, stats, depth + 1)
        }
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            collect_stats_inner(cond, stats, depth + 1)?;
            collect_stats_inner(then_br, stats, depth + 1)?;
            collect_stats_inner(else_br, stats, depth + 1)
        }
        SurfaceExpr::Ident(_, name) => {
            if let Some(kind) = classify_effect(name) {
                stats.record(kind);
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Check whether a surface expression is pure (contains no IO effects).
///
/// An expression is pure if it contains no IO operations that produce side
/// effects. `IO.pure` and `IO.map` are considered pure wrappers.
#[must_use]
pub(crate) fn is_pure_expr(expr: &SurfaceExpr) -> bool {
    is_pure_inner(expr, 0)
}

fn is_pure_inner(expr: &SurfaceExpr, depth: usize) -> bool {
    if depth > MAX_ANALYSIS_DEPTH {
        return false; // conservatively impure on deep nesting
    }
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if let Some(kind) = classify_effect(name) {
                    if kind != EffectKind::Pure {
                        return false;
                    }
                }
            }
            is_pure_inner(func, depth + 1) && args.iter().all(|a| is_pure_inner(&a.expr, depth + 1))
        }
        SurfaceExpr::Lambda(_, _, body) => is_pure_inner(body, depth + 1),
        SurfaceExpr::Let(_, _, val, body) => {
            is_pure_inner(val, depth + 1) && is_pure_inner(body, depth + 1)
        }
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            is_pure_inner(cond, depth + 1)
                && is_pure_inner(then_br, depth + 1)
                && is_pure_inner(else_br, depth + 1)
        }
        SurfaceExpr::Ident(_, name) => {
            // A bare identifier referencing an IO op like "IO.getLine" is effectful.
            classify_effect(name).is_none_or(|k| k == EffectKind::Pure)
        }
        _ => true,
    }
}

/// Detect effect boundaries in an expression tree.
///
/// Returns a list of boundaries where code transitions from pure to effectful
/// or vice versa. Only top-level IO operation applications are reported.
pub(crate) fn detect_effect_boundaries(expr: &SurfaceExpr) -> Vec<EffectBoundary> {
    let mut boundaries = Vec::new();
    detect_boundaries_inner(expr, true, &mut boundaries, 0);
    boundaries
}

fn detect_boundaries_inner(
    expr: &SurfaceExpr,
    in_pure_context: bool,
    out: &mut Vec<EffectBoundary>,
    depth: usize,
) {
    if depth > MAX_ANALYSIS_DEPTH {
        return;
    }
    match expr {
        SurfaceExpr::App(_, func, args) => {
            if let SurfaceExpr::Ident(_, name) = func.as_ref() {
                if let Some(kind) = classify_effect(name) {
                    let is_pure_op = kind == EffectKind::Pure;
                    if in_pure_context && !is_pure_op {
                        out.push(EffectBoundary {
                            operation: name.clone(),
                            entering_effect: kind,
                            pure_to_effectful: true,
                        });
                    } else if !in_pure_context && is_pure_op {
                        out.push(EffectBoundary {
                            operation: name.clone(),
                            entering_effect: kind,
                            pure_to_effectful: false,
                        });
                    }
                    // Recurse into arguments with updated context
                    for arg in args {
                        detect_boundaries_inner(&arg.expr, is_pure_op, out, depth + 1);
                    }
                    return;
                }
            }
            detect_boundaries_inner(func, in_pure_context, out, depth + 1);
            for arg in args {
                detect_boundaries_inner(&arg.expr, in_pure_context, out, depth + 1);
            }
        }
        SurfaceExpr::Lambda(_, _, body) => {
            detect_boundaries_inner(body, in_pure_context, out, depth + 1);
        }
        SurfaceExpr::Let(_, _, val, body) => {
            detect_boundaries_inner(val, in_pure_context, out, depth + 1);
            detect_boundaries_inner(body, in_pure_context, out, depth + 1);
        }
        SurfaceExpr::If(_, cond, then_br, else_br) => {
            detect_boundaries_inner(cond, in_pure_context, out, depth + 1);
            detect_boundaries_inner(then_br, in_pure_context, out, depth + 1);
            detect_boundaries_inner(else_br, in_pure_context, out, depth + 1);
        }
        _ => {}
    }
}

/// Analyze a list of IO operation names for parallelizability.
///
/// Returns pairs of indices that can safely run in parallel.
#[must_use]
pub(crate) fn find_parallelizable_pairs(ops: &[&str]) -> Vec<(usize, usize)> {
    let classified: Vec<Option<EffectKind>> = ops.iter().map(|op| classify_effect(op)).collect();
    let mut pairs = Vec::new();
    for i in 0..classified.len() {
        for j in (i + 1)..classified.len() {
            if let (Some(a), Some(b)) = (classified[i], classified[j]) {
                if effects_parallelizable(a, b) {
                    pairs.push((i, j));
                }
            }
        }
    }
    pairs
}
