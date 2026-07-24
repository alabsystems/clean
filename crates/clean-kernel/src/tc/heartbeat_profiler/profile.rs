// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `HeartbeatProfile`: the structured report surfaced on timeout.

use super::types::{
    HeartbeatProfileCategory, OverrunEstimate, ProfileEntry, ProfileNameEntry,
    ProfilePositionEntry, ProfileTacticEntry,
};
use crate::name::Name;
use std::fmt;

/// Structured heartbeat profile report.
///
/// Returned by `HeartbeatProfiler::report()` and formatted into timeout errors.
/// Provides per-category, per-name, per-tactic, and per-source-position
/// heartbeat breakdowns plus an `OverrunEstimate` that projects a reasonable
/// `maxHeartbeats` suggestion.
///
/// New in #3399 Phase A: `top_tactics`, `top_positions`, `overrun`.
#[derive(Debug, Clone)]
pub struct HeartbeatProfile {
    pub(crate) total: u64,
    pub(crate) limit: u32,
    /// Per-category heartbeat breakdown (whnf, isDefEq, inferType).
    pub categories: Vec<ProfileEntry>,
    /// Top constant-name hotspots sorted by heartbeats descending.
    pub top_names: Vec<ProfileNameEntry>,
    /// Top tactic hotspots sorted by heartbeats descending, then by
    /// invocations descending, then by tactic name ascending.
    pub top_tactics: Vec<ProfileTacticEntry>,
    /// Top source-position hotspots sorted by heartbeats descending.
    pub top_positions: Vec<ProfilePositionEntry>,
    /// Overrun estimate (projected total + suggested limit).
    pub overrun: OverrunEstimate,
}

impl HeartbeatProfile {
    /// Total heartbeats consumed.
    #[must_use]
    pub fn total(&self) -> u64 {
        self.total
    }

    /// Configured heartbeat limit.
    #[must_use]
    pub fn limit(&self) -> u32 {
        self.limit
    }

    /// Per-category entries sorted by heartbeats descending.
    #[must_use]
    pub fn categories(&self) -> &[ProfileEntry] {
        &self.categories
    }

    /// Top constant-name hotspots sorted by heartbeats descending.
    #[must_use]
    pub fn top_names(&self) -> &[ProfileNameEntry] {
        &self.top_names
    }

    /// Top tactic hotspots sorted by heartbeats descending.
    #[must_use]
    pub fn top_tactics(&self) -> &[ProfileTacticEntry] {
        &self.top_tactics
    }

    /// Top source-position hotspots sorted by heartbeats descending.
    #[must_use]
    pub fn top_positions(&self) -> &[ProfilePositionEntry] {
        &self.top_positions
    }

    /// Overrun estimate (projected total and suggested `maxHeartbeats`).
    #[must_use]
    pub fn overrun(&self) -> OverrunEstimate {
        self.overrun
    }

    /// Check if the profile is empty (no ticks recorded).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total == 0
    }
}

impl fmt::Display for HeartbeatProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Heartbeat profile ({}/{})", self.total, self.limit)?;

        if !self.categories.is_empty() {
            writeln!(f)?;
            writeln!(f, "By operation:")?;
            for entry in &self.categories {
                write_entry_line(f, entry.category, entry.heartbeats, self.total)?;
            }
        }

        if !self.top_names.is_empty() {
            writeln!(f)?;
            writeln!(f, "Top consumers by name:")?;
            for entry in &self.top_names {
                write_name_line(f, &entry.name, entry.heartbeats, self.total)?;
            }
        }

        if !self.top_tactics.is_empty() {
            writeln!(f)?;
            writeln!(f, "Top tactics:")?;
            for entry in &self.top_tactics {
                write_tactic_line(f, entry, self.total)?;
            }
        }

        if !self.top_positions.is_empty() {
            writeln!(f)?;
            writeln!(f, "Top positions:")?;
            for entry in &self.top_positions {
                write_position_line(f, entry, self.total)?;
            }
        }

        writeln!(f)?;
        writeln!(
            f,
            "Projected total: ~{} hb (consumed {}/{})",
            self.overrun.projected_total, self.total, self.limit
        )?;
        writeln!(
            f,
            "Suggestion: set_option maxHeartbeats {}",
            self.overrun.suggested_limit
        )?;

        Ok(())
    }
}

pub(crate) fn sort_profile_entries(entries: &mut [ProfileEntry]) {
    entries.sort_by(|left, right| {
        right
            .heartbeats
            .cmp(&left.heartbeats)
            .then_with(|| left.category.cmp(&right.category))
            .then_with(|| left.name.cmp(&right.name))
    });
}

pub(crate) fn sort_name_entries(entries: &mut [ProfileNameEntry]) {
    entries.sort_by(|left, right| {
        right
            .heartbeats
            .cmp(&left.heartbeats)
            .then_with(|| left.name.cmp(&right.name))
    });
}

pub(crate) fn sort_tactic_entries(entries: &mut [ProfileTacticEntry]) {
    entries.sort_by(|left, right| {
        right
            .heartbeats
            .cmp(&left.heartbeats)
            .then_with(|| right.invocations.cmp(&left.invocations))
            .then_with(|| left.tactic.cmp(&right.tactic))
    });
}

pub(crate) fn sort_position_entries(entries: &mut [ProfilePositionEntry]) {
    entries.sort_by(|left, right| {
        right
            .heartbeats
            .cmp(&left.heartbeats)
            .then_with(|| left.position.cmp(&right.position))
    });
}

fn write_entry_line(
    f: &mut fmt::Formatter<'_>,
    category: HeartbeatProfileCategory,
    heartbeats: u64,
    total: u64,
) -> fmt::Result {
    writeln!(
        f,
        "  {:<12} {:>10} hb ({:.1}%)",
        category,
        heartbeats,
        percentage(heartbeats, total)
    )
}

fn write_name_line(
    f: &mut fmt::Formatter<'_>,
    name: &Name,
    heartbeats: u64,
    total: u64,
) -> fmt::Result {
    writeln!(
        f,
        "  {:<40} {:>10} hb ({:.1}%)",
        name,
        heartbeats,
        percentage(heartbeats, total)
    )
}

fn write_tactic_line(
    f: &mut fmt::Formatter<'_>,
    entry: &ProfileTacticEntry,
    total: u64,
) -> fmt::Result {
    writeln!(
        f,
        "  {:<24} {:>10} hb ({:.1}%, {} invocations)",
        entry.tactic,
        entry.heartbeats,
        percentage(entry.heartbeats, total),
        entry.invocations
    )
}

fn write_position_line(
    f: &mut fmt::Formatter<'_>,
    entry: &ProfilePositionEntry,
    total: u64,
) -> fmt::Result {
    writeln!(
        f,
        "  {:<24} {:>10} hb ({:.1}%)",
        entry.position,
        entry.heartbeats,
        percentage(entry.heartbeats, total)
    )
}

fn percentage(heartbeats: u64, total: u64) -> f64 {
    if total == 0 {
        return 0.0;
    }
    (heartbeats as f64 / total as f64) * 100.0
}
