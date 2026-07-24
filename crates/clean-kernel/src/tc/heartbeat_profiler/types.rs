// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! POD types for the heartbeat profiler: categories, entries, source
//! positions, overrun estimates.

use super::SUGGESTION_ROUND_UP;
use crate::name::Name;
use std::fmt;

/// Category of kernel operation consuming heartbeats.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HeartbeatProfileCategory {
    /// Weak-head normal form reduction (`whnf_impl`).
    Whnf,
    /// Definitional equality checking (`is_def_eq_impl`).
    IsDefEq,
    /// Type inference (`infer_type` / `tick_heartbeat`).
    InferType,
}

impl fmt::Display for HeartbeatProfileCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Whnf => write!(f, "whnf"),
            Self::IsDefEq => write!(f, "isDefEq"),
            Self::InferType => write!(f, "inferType"),
        }
    }
}

/// A single heartbeat profile entry for a category breakdown.
///
/// Category entries use `name: None`; name-specific reporting is stored in
/// `HeartbeatProfile::top_names`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileEntry {
    /// The operation category being reported.
    pub category: HeartbeatProfileCategory,
    /// Optional constant name associated with the entry.
    pub name: Option<Name>,
    /// Number of heartbeats consumed by this entry.
    pub heartbeats: u64,
}

/// A heartbeat profile entry for per-name breakdown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileNameEntry {
    /// The constant name.
    pub name: Name,
    /// Number of heartbeats attributed to this name.
    pub heartbeats: u64,
}

/// A heartbeat profile entry for per-tactic breakdown.
///
/// Tracks both heartbeats consumed and the number of push/pop scopes observed
/// for a given tactic. Part of #3399 Phase A.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfileTacticEntry {
    /// Tactic name (e.g. "simp", "cases", "rewrite", or a combinator path
    /// such as "repeat > simp").
    pub tactic: String,
    /// Total heartbeats attributed to this tactic.
    pub heartbeats: u64,
    /// Number of times this tactic was pushed onto the stack.
    pub invocations: u64,
}

/// A source-location key for heartbeat attribution.
///
/// `file_id == 0` is reserved for "unknown file"; non-zero values are
/// interned integers supplied by the elaborator/parser layers. Line and
/// column use 1-based indexing to match the parser's convention; `(0, 0)`
/// means "no position available".
///
/// Part of #3399 Phase A.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SourcePos {
    /// Interned file identifier; 0 means "unknown".
    pub file_id: u32,
    /// 1-based line number, or 0 if unknown.
    pub line: u32,
    /// 1-based column number, or 0 if unknown.
    pub column: u32,
}

impl SourcePos {
    /// Construct an "unknown" source position.
    #[must_use]
    pub const fn unknown() -> Self {
        Self {
            file_id: 0,
            line: 0,
            column: 0,
        }
    }

    /// Construct a source position from `(file_id, line, column)`.
    #[must_use]
    pub const fn new(file_id: u32, line: u32, column: u32) -> Self {
        Self {
            file_id,
            line,
            column,
        }
    }

    /// Coalesce this position into a coarser bucket (line rounded down to
    /// nearest 10, column reset to 0). Used when the distinct-positions
    /// cap is reached.
    #[must_use]
    pub(crate) fn coalesced(self) -> Self {
        Self {
            file_id: self.file_id,
            line: self.line / 10,
            column: 0,
        }
    }
}

impl fmt::Display for SourcePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.file_id == 0 && self.line == 0 && self.column == 0 {
            write!(f, "<unknown>")
        } else if self.file_id == 0 {
            write!(f, "{}:{}", self.line, self.column)
        } else {
            write!(f, "#{}:{}:{}", self.file_id, self.line, self.column)
        }
    }
}

/// A heartbeat profile entry for per-source-position breakdown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProfilePositionEntry {
    /// Source position.
    pub position: SourcePos,
    /// Total heartbeats attributed to this position.
    pub heartbeats: u64,
}

/// An extrapolation of the currently-consumed heartbeat budget into a
/// projected total and a suggested `maxHeartbeats` for a retry.
///
/// The numbers are advisory, not a soundness claim. Part of #3399 Phase A.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OverrunEstimate {
    /// Heartbeats projected for a complete run, extrapolated from the
    /// consumed budget.
    pub projected_total: u64,
    /// Suggested next `maxHeartbeats` value, rounded up to the next
    /// `SUGGESTION_ROUND_UP` boundary and always `>= consumed`.
    pub suggested_limit: u32,
}

impl OverrunEstimate {
    /// Build an estimate from `consumed` ticks. Produces a conservative
    /// `projected_total = consumed * 2` hint and rounds the suggested
    /// limit up to the next `SUGGESTION_ROUND_UP` multiple.
    #[must_use]
    pub fn from_consumed(consumed: u64) -> Self {
        let projected_total = consumed.saturating_mul(2);
        let suggested_limit = round_up_to_next(projected_total, SUGGESTION_ROUND_UP);
        Self {
            projected_total,
            suggested_limit: clamp_u32(suggested_limit),
        }
    }
}

/// Round `value` up to the next strictly-greater multiple of `step`.
///
/// `round_up_to_next(k*step, step) == (k+1)*step`, so an exact multiple
/// still advances — guaranteeing `suggested_limit > consumed` whenever
/// `projected_total >= consumed`.
pub(crate) fn round_up_to_next(value: u64, step: u64) -> u64 {
    if step == 0 {
        return value;
    }
    let next_boundary = (value / step).saturating_add(1).saturating_mul(step);
    next_boundary.max(step)
}

/// Saturating conversion `u64 -> u32`.
pub(crate) fn clamp_u32(value: u64) -> u32 {
    if value > u32::MAX as u64 {
        u32::MAX
    } else {
        value as u32
    }
}
