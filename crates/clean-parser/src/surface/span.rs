// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Span type for source location tracking.

/// Span in source text for error reporting
///
/// Represents a byte range `[start, end)` in the source text.
/// Used for error messages and source mapping.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    /// Create a new span.
    ///
    /// # ENSURES
    /// - Returns span covering `[start, end)`
    /// - No validation that `start <= end` (caller's responsibility)
    #[must_use]
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Create a dummy span at position 0.
    ///
    /// # ENSURES
    /// - Returns `Span { start: 0, end: 0 }`
    #[must_use]
    pub fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Merge two spans to cover both.
    ///
    /// # ENSURES
    /// - `result.start == min(self.start, other.start)`
    /// - `result.end == max(self.end, other.end)`
    #[must_use]
    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}
