// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Heartbeat profiler for diagnosing where the type checker spends heartbeat budget.
//!
//! The profiler is opt-in and complements `heartbeat.rs`: it records consumed
//! heartbeats by high-level kernel operation, by constant name, by tactic
//! invocation, and by surface source position. This makes heartbeat-limit
//! failures actionable by surfacing the hottest categories, names, tactics,
//! and positions in a compact report.
//!
//! Module layout (Phase A of #3399):
//! - `types` — POD entry structs, category/position/estimate/tactic-entry types
//! - `profiler` — the `HeartbeatProfiler` struct (counters + stacks)
//! - `profile` — `HeartbeatProfile`, Display rendering, sort helpers
//! - `tests` — unit tests (only compiled under `#[cfg(test)]`)
//!
//! Memory bound: the `position_counts` map is capped at
//! `MAX_DISTINCT_POSITIONS` (10 000). Once the cap is reached, further
//! positions are coalesced into a coarser bucket (`line / 10`, column 0)
//! to preserve signal without unbounded allocation.

pub(crate) mod profile;
pub(crate) mod profiler;
pub(crate) mod types;

#[cfg(test)]
mod tests;

pub use profile::HeartbeatProfile;
pub use types::{
    HeartbeatProfileCategory, OverrunEstimate, ProfileEntry, ProfileNameEntry,
    ProfilePositionEntry, ProfileTacticEntry, SourcePos,
};

pub(crate) use profiler::HeartbeatProfiler;

/// Maximum number of distinct `SourcePos` keys we will track before
/// coalescing further positions into a coarser bucket.
pub(crate) const MAX_DISTINCT_POSITIONS: usize = 10_000;

/// Heartbeat-limit suggestion rounding granularity (ticks).
pub(crate) const SUGGESTION_ROUND_UP: u64 = 50_000;
