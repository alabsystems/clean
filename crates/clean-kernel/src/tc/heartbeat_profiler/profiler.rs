// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `HeartbeatProfiler` struct: counters, stacks, tick/push/pop API.

use super::profile::HeartbeatProfile;
use super::types::{
    HeartbeatProfileCategory, OverrunEstimate, ProfileEntry, ProfileNameEntry,
    ProfilePositionEntry, ProfileTacticEntry, SourcePos,
};
use super::MAX_DISTINCT_POSITIONS;
use crate::name::Name;
use crate::tc::TcHashMap;
use std::cell::{Cell, RefCell};

/// Tracks consumed heartbeats by operation category, constant name,
/// tactic, and source position.
///
/// The profiler itself uses `Cell`/`RefCell` for interior mutability so
/// callers can record ticks through `&self`, matching the TypeChecker
/// pattern.
#[derive(Debug, Clone, Default)]
pub(crate) struct HeartbeatProfiler {
    category_counts: RefCell<TcHashMap<HeartbeatProfileCategory, u64>>,
    name_counts: RefCell<TcHashMap<Name, u64>>,
    total_ticks: Cell<u64>,
    active_name: RefCell<Option<Name>>,
    /// Stack of currently-active tactic names. The innermost (top) entry
    /// receives attribution for any ticks recorded while it is active.
    tactic_stack: RefCell<Vec<String>>,
    /// Stack of currently-active source positions.
    position_stack: RefCell<Vec<SourcePos>>,
    /// Per-tactic consumed-heartbeat counts.
    tactic_counts: RefCell<TcHashMap<String, u64>>,
    /// Per-tactic invocation counts (push counts).
    tactic_invocations: RefCell<TcHashMap<String, u64>>,
    /// Per-position consumed-heartbeat counts.
    position_counts: RefCell<TcHashMap<SourcePos, u64>>,
}

impl HeartbeatProfiler {
    /// Create a new empty profiler.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Set the active constant name for subsequent heartbeat attribution.
    pub(crate) fn set_active_name(&self, name: Name) {
        *self.active_name.borrow_mut() = Some(name);
    }

    /// Clear the active constant name.
    pub(crate) fn clear_active_name(&self) {
        *self.active_name.borrow_mut() = None;
    }

    /// Push a tactic name onto the attribution stack.
    ///
    /// Each push is counted as one invocation. Callers must pair this with
    /// `pop_tactic` (RAII recommended in elab layers).
    pub(crate) fn push_tactic(&self, tactic: &str) {
        self.tactic_stack.borrow_mut().push(tactic.to_owned());
        let mut invocations = self.tactic_invocations.borrow_mut();
        let entry = invocations.entry(tactic.to_owned()).or_insert(0);
        *entry = entry.saturating_add(1);
    }

    /// Pop the innermost tactic scope. No-op when the stack is empty
    /// (defensive: keeps the pop infallible even on panic unwind in elab).
    pub(crate) fn pop_tactic(&self) {
        self.tactic_stack.borrow_mut().pop();
    }

    /// Push a source position onto the attribution stack.
    pub(crate) fn push_position(&self, pos: SourcePos) {
        self.position_stack.borrow_mut().push(pos);
    }

    /// Pop the innermost source position. No-op when the stack is empty.
    pub(crate) fn pop_position(&self) {
        self.position_stack.borrow_mut().pop();
    }

    /// Current depth of the tactic stack (for tests/debug).
    #[cfg(test)]
    pub(crate) fn tactic_depth(&self) -> usize {
        self.tactic_stack.borrow().len()
    }

    /// Current depth of the position stack (for tests/debug).
    #[cfg(test)]
    pub(crate) fn position_depth(&self) -> usize {
        self.position_stack.borrow().len()
    }

    /// Expose the position-counts map size (tests / memory-cap checks).
    #[cfg(test)]
    pub(crate) fn position_count_len(&self) -> usize {
        self.position_counts.borrow().len()
    }

    /// Expose whether a coalesced key is present (tests).
    #[cfg(test)]
    pub(crate) fn position_counts_has(&self, pos: SourcePos) -> bool {
        self.position_counts.borrow().contains_key(&pos)
    }

    /// Record one consumed heartbeat in the given category.
    ///
    /// If `name` is `None`, the profiler falls back to the currently active
    /// name, if any. The innermost tactic and source position (if any) are
    /// always credited.
    #[inline]
    pub(crate) fn tick(&self, category: HeartbeatProfileCategory, name: Option<&Name>) {
        self.total_ticks
            .set(self.total_ticks.get().saturating_add(1));

        {
            let mut category_counts = self.category_counts.borrow_mut();
            let heartbeats = category_counts.entry(category).or_insert(0);
            *heartbeats = heartbeats.saturating_add(1);
        }

        let effective_name = name.cloned().or_else(|| self.active_name.borrow().clone());
        if let Some(name) = effective_name {
            let mut name_counts = self.name_counts.borrow_mut();
            let heartbeats = name_counts.entry(name).or_insert(0);
            *heartbeats = heartbeats.saturating_add(1);
        }

        let active_tactic = self.tactic_stack.borrow().last().cloned();
        if let Some(tactic) = active_tactic {
            let mut tactic_counts = self.tactic_counts.borrow_mut();
            let entry = tactic_counts.entry(tactic).or_insert(0);
            *entry = entry.saturating_add(1);
        }

        let active_pos = self.position_stack.borrow().last().copied();
        if let Some(pos) = active_pos {
            let mut position_counts = self.position_counts.borrow_mut();
            let key = if position_counts.len() >= MAX_DISTINCT_POSITIONS
                && !position_counts.contains_key(&pos)
            {
                pos.coalesced()
            } else {
                pos
            };
            let entry = position_counts.entry(key).or_insert(0);
            *entry = entry.saturating_add(1);
        }
    }

    /// Generate a profile report with the top-N name / tactic / position hotspots.
    #[must_use]
    pub(crate) fn report(&self, limit: u32, top_n: usize) -> HeartbeatProfile {
        let categories = self.collect_categories();
        let top_names = self.collect_top_names(top_n);
        let top_tactics = self.collect_top_tactics(top_n);
        let top_positions = self.collect_top_positions(top_n);
        let total = self.total_ticks.get();
        let overrun = OverrunEstimate::from_consumed(total);

        HeartbeatProfile {
            total,
            limit,
            categories,
            top_names,
            top_tactics,
            top_positions,
            overrun,
        }
    }

    fn collect_categories(&self) -> Vec<ProfileEntry> {
        let mut categories: Vec<ProfileEntry> = self
            .category_counts
            .borrow()
            .iter()
            .map(|(&category, &heartbeats)| ProfileEntry {
                category,
                name: None,
                heartbeats,
            })
            .collect();
        super::profile::sort_profile_entries(&mut categories);
        categories
    }

    fn collect_top_names(&self, top_n: usize) -> Vec<ProfileNameEntry> {
        let mut entries: Vec<ProfileNameEntry> = self
            .name_counts
            .borrow()
            .iter()
            .map(|(name, &heartbeats)| ProfileNameEntry {
                name: name.clone(),
                heartbeats,
            })
            .collect();
        super::profile::sort_name_entries(&mut entries);
        entries.truncate(top_n);
        entries
    }

    fn collect_top_tactics(&self, top_n: usize) -> Vec<ProfileTacticEntry> {
        let tactic_counts = self.tactic_counts.borrow();
        let invocations = self.tactic_invocations.borrow();
        let mut entries: Vec<ProfileTacticEntry> = tactic_counts
            .iter()
            .map(|(tactic, &heartbeats)| {
                let invocations = invocations.get(tactic).copied().unwrap_or(0);
                ProfileTacticEntry {
                    tactic: tactic.clone(),
                    heartbeats,
                    invocations,
                }
            })
            .chain(
                // Tactics pushed/popped without consuming ticks still show up
                // in the invocation roll-up.
                invocations
                    .iter()
                    .filter(|(tactic, _)| !tactic_counts.contains_key(*tactic))
                    .map(|(tactic, &invocations)| ProfileTacticEntry {
                        tactic: tactic.clone(),
                        heartbeats: 0,
                        invocations,
                    }),
            )
            .collect();
        super::profile::sort_tactic_entries(&mut entries);
        entries.truncate(top_n);
        entries
    }

    fn collect_top_positions(&self, top_n: usize) -> Vec<ProfilePositionEntry> {
        let mut entries: Vec<ProfilePositionEntry> = self
            .position_counts
            .borrow()
            .iter()
            .map(|(&position, &heartbeats)| ProfilePositionEntry {
                position,
                heartbeats,
            })
            .collect();
        super::profile::sort_position_entries(&mut entries);
        entries.truncate(top_n);
        entries
    }

    /// Clear all accumulated counters and name context.
    #[cfg(test)]
    pub(crate) fn reset(&self) {
        self.category_counts.borrow_mut().clear();
        self.name_counts.borrow_mut().clear();
        self.total_ticks.set(0);
        self.clear_active_name();
        self.tactic_stack.borrow_mut().clear();
        self.position_stack.borrow_mut().clear();
        self.tactic_counts.borrow_mut().clear();
        self.tactic_invocations.borrow_mut().clear();
        self.position_counts.borrow_mut().clear();
    }

    // ── test-only accessors ──────────────────────────────────────────

    #[cfg(test)]
    pub(crate) fn total_ticks_raw(&self) -> u64 {
        self.total_ticks.get()
    }

    #[cfg(test)]
    pub(crate) fn category_counts_empty(&self) -> bool {
        self.category_counts.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn name_counts_empty(&self) -> bool {
        self.name_counts.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn active_name_is_none(&self) -> bool {
        self.active_name.borrow().is_none()
    }

    #[cfg(test)]
    pub(crate) fn tactic_stack_empty(&self) -> bool {
        self.tactic_stack.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn position_stack_empty(&self) -> bool {
        self.position_stack.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn tactic_counts_empty(&self) -> bool {
        self.tactic_counts.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn tactic_invocations_empty(&self) -> bool {
        self.tactic_invocations.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn position_counts_empty(&self) -> bool {
        self.position_counts.borrow().is_empty()
    }

    #[cfg(test)]
    pub(crate) fn category_count_for(&self, category: HeartbeatProfileCategory) -> u64 {
        self.category_counts
            .borrow()
            .get(&category)
            .copied()
            .unwrap_or(0)
    }

    #[cfg(test)]
    pub(crate) fn name_count_for(&self, name: &Name) -> u64 {
        self.name_counts.borrow().get(name).copied().unwrap_or(0)
    }
}
