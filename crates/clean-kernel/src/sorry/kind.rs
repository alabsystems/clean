// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Provenance classification for sorry terms.

/// Distinguishes explicit user-written sorry from synthetic/internal sorry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SorryKind {
    Explicit,
    Synthetic,
}
