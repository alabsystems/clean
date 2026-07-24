// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Thread-local elaboration failure tracking.

use std::cell::{Cell, RefCell};

use crate::error::ElabError;

const TRACK_ELAB_FAILURES_ENV_VAR: &str = "CLEAN_TRACK_ELAB_FAILURES";

/// Coarse categories for elaboration failures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ElabFailureCategory {
    TypeMismatch,
    NotImplemented,
    UnknownIdentifier,
    TacticFailure,
    UniverseError,
    Other,
}

impl ElabFailureCategory {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TypeMismatch => "TypeMismatch",
            Self::NotImplemented => "NotImplemented",
            Self::UnknownIdentifier => "UnknownIdentifier",
            Self::TacticFailure => "TacticFailure",
            Self::UniverseError => "UniverseError",
            Self::Other => "Other",
        }
    }
}

impl std::fmt::Display for ElabFailureCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Per-thread elaboration failure counts, bucketed into coarse categories.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ElabFailureTracker {
    type_mismatch: u64,
    not_implemented: u64,
    unknown_identifier: u64,
    tactic_failure: u64,
    universe_error: u64,
    other: u64,
}

impl ElabFailureTracker {
    /// Map an [`ElabError`] into a coarse failure category.
    #[must_use]
    pub fn categorize(error: &ElabError) -> ElabFailureCategory {
        match error {
            ElabError::TypeMismatch { .. }
            | ElabError::ProofTypeMismatch { .. }
            | ElabError::MatchArmTypeMismatch { .. }
            | ElabError::TooManyArguments { .. }
            | ElabError::InvalidProjectionTarget(_)
            | ElabError::AnonymousCtorNotInductive(_) => ElabFailureCategory::TypeMismatch,
            ElabError::NotImplemented(_) | ElabError::Unsupported { .. } => {
                ElabFailureCategory::NotImplemented
            }
            ElabError::UnknownIdent(_)
            | ElabError::UnknownIdentWithSuggestions { .. }
            | ElabError::UnknownProjectionField { .. }
            | ElabError::UnknownStructureField { .. }
            | ElabError::MissingStructureFields { .. }
            | ElabError::UnknownStruct { .. } => ElabFailureCategory::UnknownIdentifier,
            ElabError::StructureFieldTypeMismatch { .. } => ElabFailureCategory::TypeMismatch,
            ElabError::TacticFailed(_) => ElabFailureCategory::TacticFailure,
            ElabError::UniverseInstNotConst | ElabError::UniverseLevelMismatch { .. } => {
                ElabFailureCategory::UniverseError
            }
            _ => ElabFailureCategory::Other,
        }
    }

    /// Record a single elaboration failure.
    pub fn record_failure(&mut self, error: &ElabError) {
        match Self::categorize(error) {
            ElabFailureCategory::TypeMismatch => self.type_mismatch += 1,
            ElabFailureCategory::NotImplemented => self.not_implemented += 1,
            ElabFailureCategory::UnknownIdentifier => self.unknown_identifier += 1,
            ElabFailureCategory::TacticFailure => self.tactic_failure += 1,
            ElabFailureCategory::UniverseError => self.universe_error += 1,
            ElabFailureCategory::Other => self.other += 1,
        }
    }

    /// Return the count for a single category.
    #[must_use]
    pub fn count(&self, category: ElabFailureCategory) -> u64 {
        match category {
            ElabFailureCategory::TypeMismatch => self.type_mismatch,
            ElabFailureCategory::NotImplemented => self.not_implemented,
            ElabFailureCategory::UnknownIdentifier => self.unknown_identifier,
            ElabFailureCategory::TacticFailure => self.tactic_failure,
            ElabFailureCategory::UniverseError => self.universe_error,
            ElabFailureCategory::Other => self.other,
        }
    }

    /// Total failures recorded in this tracker.
    #[must_use]
    pub fn total_failures(&self) -> u64 {
        self.type_mismatch
            + self.not_implemented
            + self.unknown_identifier
            + self.tactic_failure
            + self.universe_error
            + self.other
    }

    /// Return true when no failures have been recorded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total_failures() == 0
    }

    /// Return a compact summary string for diagnostics.
    #[must_use]
    pub fn summary(&self) -> String {
        format!(
            "total={} TypeMismatch={} NotImplemented={} UnknownIdentifier={} TacticFailure={} UniverseError={} Other={}",
            self.total_failures(),
            self.type_mismatch,
            self.not_implemented,
            self.unknown_identifier,
            self.tactic_failure,
            self.universe_error,
            self.other
        )
    }
}

thread_local! {
    static THREAD_ELAB_FAILURE_TRACKER: RefCell<Option<ElabFailureTracker>> =
        const { RefCell::new(None) };
    static ELAB_FAILURE_BOUNDARY_DEPTH: Cell<u32> = const { Cell::new(0) };
}

struct ElabFailureBoundaryGuard {
    is_root: bool,
}

impl ElabFailureBoundaryGuard {
    fn enter() -> Self {
        let is_root = ELAB_FAILURE_BOUNDARY_DEPTH.with(|depth| {
            let current = depth.get();
            depth.set(current.saturating_add(1));
            current == 0
        });
        Self { is_root }
    }
}

impl Drop for ElabFailureBoundaryGuard {
    fn drop(&mut self) {
        ELAB_FAILURE_BOUNDARY_DEPTH.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
        });
    }
}

/// Return whether thread-local elaboration failure tracking is enabled.
///
/// Tracking is enabled when `CLEAN_TRACK_ELAB_FAILURES` is set to `1` or `true`.
#[must_use]
pub fn elab_failure_tracking_enabled() -> bool {
    std::env::var(TRACK_ELAB_FAILURES_ENV_VAR)
        .map(|value| value == "1" || value.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

/// Clear the current thread's tracker state.
pub fn reset_elab_failure_tracker() {
    THREAD_ELAB_FAILURE_TRACKER.with(|tracker| {
        *tracker.borrow_mut() = None;
    });
}

/// Clone the current thread's tracker state, if any failures have been recorded.
#[must_use]
pub fn current_elab_failure_tracker() -> Option<ElabFailureTracker> {
    THREAD_ELAB_FAILURE_TRACKER.with(|tracker| tracker.borrow().clone())
}

/// Return the current thread's summary string, if any failures have been recorded.
#[must_use]
pub fn current_elab_failure_summary() -> Option<String> {
    current_elab_failure_tracker().map(|tracker| tracker.summary())
}

pub(crate) fn record_elab_failure(error: &ElabError) {
    if !elab_failure_tracking_enabled() {
        return;
    }

    THREAD_ELAB_FAILURE_TRACKER.with(|tracker| {
        let mut tracker = tracker.borrow_mut();
        tracker
            .get_or_insert_with(ElabFailureTracker::default)
            .record_failure(error);
    });
}

pub(crate) fn track_elab_failure_boundary<T>(
    f: impl FnOnce() -> Result<T, ElabError>,
) -> Result<T, ElabError> {
    let guard = ElabFailureBoundaryGuard::enter();
    let result = f();
    if guard.is_root {
        if let Err(error) = &result {
            record_elab_failure(error);
        }
    }
    result
}
