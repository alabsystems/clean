// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tactic interpretation for `by` blocks and tactic combinators.
//!
//! This module provides a higher-level tactic interpretation layer on top of
//! the existing `tactic_interp` infrastructure. It adds:
//!
//! - **Heartbeat budgeting** (`TacticInterpConfig::max_heartbeats`) to bound
//!   execution time and prevent runaway tactic sequences.
//! - **Trace logging** for debugging tactic execution.
//! - **`TacticCommand` AST** with `Named`, `Sequence`, `Focus`, `Try`,
//!   `Repeat`, `AllGoals`, and `Sorry` variants.
//! - **Result packaging** via `TacticInterpResult` that carries proof term,
//!   remaining goals, heartbeat count, and trace log.
//!
//! # Architecture
//!
//! The entry point is [`interpret_tactic_block`], which takes a goal list,
//! a slice of `TacticCommand`s, and a config, then drives execution through
//! [`dispatch_tactic`]. After execution, [`check_all_goals_closed`] verifies
//! completeness.

use crate::error::ElabError;
use crate::tactic::{Goal, TacticError};
use crate::tactic_interp_profile::{build_profile, TacticHeartbeatProfile};
use clean_kernel::Expr;
use std::collections::HashMap;

// =============================================================================
// Configuration
// =============================================================================

/// Configuration for extended tactic interpretation.
#[derive(Debug, Clone)]
pub(crate) struct TacticInterpConfig {
    /// Maximum heartbeats before aborting (default 200_000).
    pub(crate) max_heartbeats: u64,
    /// Whether to record trace messages.
    pub(crate) trace_enabled: bool,
    /// Optional wall-clock timeout in milliseconds (not enforced here;
    /// provided for downstream consumers).
    pub(crate) timeout_ms: Option<u64>,
    /// Whether `Sorry` commands are permitted.
    pub(crate) allow_sorry: bool,
    /// Collect a per-tactic heartbeat profile; on overflow the breakdown is
    /// embedded in the `ElabError`. See [`TacticHeartbeatProfile`] (#3399).
    pub(crate) profile_heartbeats: bool,
}

impl Default for TacticInterpConfig {
    fn default() -> Self {
        Self {
            max_heartbeats: 200_000,
            trace_enabled: false,
            timeout_ms: None,
            allow_sorry: false,
            profile_heartbeats: false,
        }
    }
}

// =============================================================================
// Interpreter state
// =============================================================================

/// Mutable state threaded through tactic interpretation.
pub(crate) struct TacticInterpState {
    /// Goal stack (front = current goal).
    pub(crate) goals: Vec<Goal>,
    /// Heartbeat counter (incremented per tactic dispatch).
    pub(crate) heartbeats: u64,
    /// Maximum heartbeats from config.
    max_heartbeats: u64,
    /// Accumulated trace log entries.
    pub(crate) trace_log: Vec<String>,
    /// Whether tracing is active.
    trace_enabled: bool,
    /// Whether sorry is allowed.
    allow_sorry: bool,
    /// Per-tactic heartbeat profiling flag (#3399).
    profile_enabled: bool,
    /// Per-bucket heartbeat counters (#3399).
    profile_buckets: HashMap<String, u64>,
}

impl TacticInterpState {
    /// Create a new interpreter state from config and initial goals.
    pub(crate) fn new(goals: Vec<Goal>, config: &TacticInterpConfig) -> Self {
        Self {
            goals,
            heartbeats: 0,
            max_heartbeats: config.max_heartbeats,
            trace_log: Vec::new(),
            trace_enabled: config.trace_enabled,
            allow_sorry: config.allow_sorry,
            profile_enabled: config.profile_heartbeats,
            profile_buckets: HashMap::new(),
        }
    }

    /// Tick one heartbeat into `bucket`, then check the budget (#3399).
    pub(crate) fn tick_heartbeat_for(&mut self, bucket: &str) -> Result<(), ElabError> {
        self.heartbeats += 1;
        if self.profile_enabled {
            *self.profile_buckets.entry(bucket.to_string()).or_insert(0) += 1;
        }
        if self.heartbeats > self.max_heartbeats {
            let breakdown = self.build_profile().format_top(10);
            return Err(ElabError::NotImplemented(format!(
                "heartbeat limit exceeded: {} > {}{}",
                self.heartbeats, self.max_heartbeats, breakdown
            )));
        }
        Ok(())
    }

    /// Snapshot per-bucket counters, sorted by count desc then name asc.
    #[must_use]
    pub(crate) fn build_profile(&self) -> TacticHeartbeatProfile {
        build_profile(&self.profile_buckets, self.heartbeats, self.max_heartbeats)
    }

    /// Push a goal onto the front of the goal stack.
    pub(crate) fn push_goal(&mut self, goal: Goal) {
        self.goals.insert(0, goal);
    }

    /// Pop the current (front) goal from the stack.
    pub(crate) fn pop_goal(&mut self) -> Option<Goal> {
        if self.goals.is_empty() {
            None
        } else {
            Some(self.goals.remove(0))
        }
    }

    /// Increment the heartbeat counter and check the budget.
    ///
    /// Returns `Err(ElabError)` if the budget is exceeded.
    pub(crate) fn tick_heartbeat(&mut self) -> Result<(), ElabError> {
        self.heartbeats += 1;
        if self.heartbeats > self.max_heartbeats {
            return Err(ElabError::NotImplemented(format!(
                "heartbeat limit exceeded: {} > {}",
                self.heartbeats, self.max_heartbeats
            )));
        }
        Ok(())
    }

    /// Record a trace message (no-op if tracing is disabled).
    pub(crate) fn trace(&mut self, msg: &str) {
        if self.trace_enabled {
            self.trace_log.push(msg.to_string());
        }
    }

    /// Number of remaining goals.
    pub(crate) fn goal_count(&self) -> usize {
        self.goals.len()
    }

    /// Whether all goals are closed.
    pub(crate) fn is_complete(&self) -> bool {
        self.goals.is_empty()
    }
}

// =============================================================================
// Tactic command AST
// =============================================================================

/// A command in the extended tactic language.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum TacticCommand {
    /// A named tactic with arguments: `exact h`, `intro x y`, `apply f`.
    Named { name: String, args: Vec<Expr> },
    /// Sequential composition: run each command in order.
    Sequence(Vec<TacticCommand>),
    /// Focus on a specific goal by index, then run the inner command.
    Focus(usize, Box<TacticCommand>),
    /// Try the inner command; succeed even if it fails.
    Try(Box<TacticCommand>),
    /// Repeat the inner command until it fails or goals are closed.
    Repeat(Box<TacticCommand>),
    /// Apply the inner command to all goals.
    AllGoals(Box<TacticCommand>),
    /// Close the current goal with sorry (requires `allow_sorry`).
    Sorry,
}

// =============================================================================
// Result
// =============================================================================

/// Result of interpreting a tactic block.
#[derive(Debug, Clone)]
pub(crate) struct TacticInterpResult {
    /// Proof term if all goals were closed (placeholder: the proof state
    /// must be consulted for the real term).
    pub(crate) proof_term: Option<Expr>,
    /// Goals remaining after interpretation.
    pub(crate) remaining_goals: Vec<Goal>,
    /// Total heartbeats consumed.
    pub(crate) heartbeats_used: u64,
    /// Trace log accumulated during interpretation.
    pub(crate) trace_log: Vec<String>,
    /// Per-tactic heartbeat profile; empty buckets when disabled (#3399).
    pub(crate) heartbeat_profile: TacticHeartbeatProfile,
}

// =============================================================================
// Maximum repeat iterations (safety bound)
// =============================================================================

const MAX_REPEAT_ITERATIONS: usize = 1_000;

// =============================================================================
// Core interpretation
// =============================================================================

/// Interpret a tactic block: run `tactics` against `goals` under `config`.
///
/// # Errors
///
/// Returns `ElabError` on heartbeat overflow, sorry without `allow_sorry`,
/// or other tactic failures.
pub(crate) fn interpret_tactic_block(
    goals: Vec<Goal>,
    tactics: &[TacticCommand],
    config: &TacticInterpConfig,
) -> Result<TacticInterpResult, ElabError> {
    let mut state = TacticInterpState::new(goals, config);

    state.trace("begin tactic block");

    for cmd in tactics {
        // Early-exit: if no goals remain, treat any subsequent command as a
        // no-op (including `sorry`, which has nothing to discharge). This
        // matches the behaviour of `repeat` / `all_goals` on empty goals.
        if state.is_complete() {
            state.trace("no goals remaining — skipping further tactics (no-op)");
            break;
        }
        dispatch_tactic(&mut state, cmd)?;
        if state.is_complete() {
            state.trace("all goals closed — stopping early");
            break;
        }
    }

    state.trace(&format!(
        "end tactic block: {} goals remaining, {} heartbeats",
        state.goal_count(),
        state.heartbeats
    ));

    let profile = state.build_profile();
    let proof_term = state
        .is_complete()
        .then(|| Expr::sort(clean_kernel::Level::zero()));
    Ok(TacticInterpResult {
        proof_term,
        remaining_goals: state.goals,
        heartbeats_used: state.heartbeats,
        trace_log: state.trace_log,
        heartbeat_profile: profile,
    })
}

/// Dispatch a single tactic command against the interpreter state.
///
/// Each dispatch consumes one heartbeat, attributed to a per-command bucket
/// (tactic name for `Named`, stable label for structural combinators) when
/// profiling is enabled (#3399).
pub(crate) fn dispatch_tactic(
    state: &mut TacticInterpState,
    cmd: &TacticCommand,
) -> Result<(), ElabError> {
    let bucket = match cmd {
        TacticCommand::Named { name, .. } => name.as_str(),
        TacticCommand::Sequence(_) => "sequence",
        TacticCommand::Focus(_, _) => "focus",
        TacticCommand::Try(_) => "try",
        TacticCommand::Repeat(_) => "repeat",
        TacticCommand::AllGoals(_) => "all_goals",
        TacticCommand::Sorry => "sorry",
    };
    state.tick_heartbeat_for(bucket)?;

    match cmd {
        TacticCommand::Named { name, args } => {
            state.trace(&format!(
                "dispatch named tactic: {} (args: {})",
                name,
                args.len()
            ));
            dispatch_named_tactic(state, name, args)
        }
        TacticCommand::Sequence(cmds) => {
            state.trace(&format!("dispatch sequence ({} commands)", cmds.len()));
            for sub in cmds {
                dispatch_tactic(state, sub)?;
                if state.is_complete() {
                    break;
                }
            }
            Ok(())
        }
        TacticCommand::Focus(idx, inner) => {
            state.trace(&format!("dispatch focus on goal {}", idx));
            dispatch_focus(state, *idx, inner)
        }
        TacticCommand::Try(inner) => {
            state.trace("dispatch try");
            dispatch_try(state, inner)
        }
        TacticCommand::Repeat(inner) => {
            state.trace("dispatch repeat");
            dispatch_repeat(state, inner)
        }
        TacticCommand::AllGoals(inner) => {
            state.trace("dispatch all_goals");
            dispatch_all_goals(state, inner)
        }
        TacticCommand::Sorry => {
            state.trace("dispatch sorry");
            dispatch_sorry(state)
        }
    }
}

/// Dispatch a named tactic. In this extended interpreter, named tactics
/// consume the current goal (simulating tactic execution). Real dispatch
/// would route through the tactic registry.
fn dispatch_named_tactic(
    state: &mut TacticInterpState,
    name: &str,
    _args: &[Expr],
) -> Result<(), ElabError> {
    if state.goals.is_empty() {
        return Err(ElabError::TacticFailed(TacticError::NoGoals));
    }

    // For the extended interpreter framework, named tactics consume the
    // current goal. Real integration will route through `execute_simple_tactic`.
    match name {
        "skip" => {
            // No-op: leave goals unchanged.
            Ok(())
        }
        "sorry" => dispatch_sorry(state),
        _ => {
            // Default: consume the front goal (simulates a successful tactic).
            let _goal = state.pop_goal();
            Ok(())
        }
    }
}

/// Focus on goal at `idx`, run `inner`, then restore goal ordering.
fn dispatch_focus(
    state: &mut TacticInterpState,
    idx: usize,
    inner: &TacticCommand,
) -> Result<(), ElabError> {
    if idx >= state.goals.len() {
        return Err(ElabError::TacticFailed(TacticError::InvalidTarget {
            tactic: "focus".into(),
            detail: format!(
                "index {} out of bounds (have {} goals)",
                idx,
                state.goals.len()
            ),
        }));
    }

    // Move focused goal to front.
    let goal = state.goals.remove(idx);
    state.goals.insert(0, goal);

    // Save the rest of the goals aside.
    let rest: Vec<Goal> = state.goals.split_off(1);

    // Run inner on the single focused goal.
    let result = dispatch_tactic(state, inner);

    // Restore remaining goals.
    state.goals.extend(rest);

    result
}

/// Try the inner command; if it fails, restore original goals.
fn dispatch_try(state: &mut TacticInterpState, inner: &TacticCommand) -> Result<(), ElabError> {
    let saved = state.goals.clone();
    match dispatch_tactic(state, inner) {
        Ok(()) => Ok(()),
        Err(_) => {
            state.goals = saved;
            state.trace("try: inner failed, restored goals");
            Ok(())
        }
    }
}

/// Repeat the inner command until failure or budget exhaustion.
fn dispatch_repeat(state: &mut TacticInterpState, inner: &TacticCommand) -> Result<(), ElabError> {
    for _ in 0..MAX_REPEAT_ITERATIONS {
        if state.is_complete() {
            break;
        }
        let saved = state.goals.clone();
        match dispatch_tactic(state, inner) {
            Ok(()) => {
                // Continue repeating.
            }
            Err(_) => {
                state.goals = saved;
                break;
            }
        }
    }
    Ok(())
}

/// Apply the inner command to every goal.
fn dispatch_all_goals(
    state: &mut TacticInterpState,
    inner: &TacticCommand,
) -> Result<(), ElabError> {
    let count = state.goals.len();
    for i in 0..count {
        if state.goals.is_empty() {
            break;
        }
        // Focus on goal index 0 each time (goals shift as they're consumed).
        let _ = i;
        dispatch_tactic(state, inner)?;
    }
    Ok(())
}

/// Close the current goal with sorry if allowed.
fn dispatch_sorry(state: &mut TacticInterpState) -> Result<(), ElabError> {
    if !state.allow_sorry {
        return Err(ElabError::NotImplemented(
            "sorry is not allowed in this proof context".to_string(),
        ));
    }
    if state.goals.is_empty() {
        return Err(ElabError::TacticFailed(TacticError::NoGoals));
    }
    let _goal = state.pop_goal();
    state.trace("sorry: closed goal");
    Ok(())
}

// =============================================================================
// Post-interpretation checks
// =============================================================================

/// Check that all goals are closed and return the proof term.
///
/// Returns `Err` if goals remain.
pub(crate) fn check_all_goals_closed(result: &TacticInterpResult) -> Result<Expr, ElabError> {
    if result.remaining_goals.is_empty() {
        result
            .proof_term
            .clone()
            .ok_or(ElabError::TacticFailed(TacticError::ProofNotProduced))
    } else {
        Err(ElabError::TacticFailed(TacticError::UnsolvedGoals {
            count: result.remaining_goals.len(),
            detail: String::new(),
        }))
    }
}

// =============================================================================
// Trace formatting
// =============================================================================

/// Format a trace log into a human-readable multi-line string.
pub(crate) fn format_tactic_trace(trace: &[String]) -> String {
    if trace.is_empty() {
        return String::from("[no trace]");
    }
    let mut out = String::new();
    for (i, entry) in trace.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        out.push_str(&format!("[{i}] {entry}"));
    }
    out
}
