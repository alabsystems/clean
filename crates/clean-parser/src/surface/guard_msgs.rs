// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The configuration clauses of Lean 4.8.0's `#guard_msgs` command.
//!
//! Grammar: `Init/Notation.lean` (`guardMsgsSpec := "(" guardMsgsSpecElt,* ")"`,
//! `guardMsgsSpecElt := guardMsgsFilter <|> guardMsgsWhitespace <|>
//! guardMsgsOrdering`). The clauses are kept AS WRITTEN, in order, because
//! their meaning depends on it: `Lean/Elab/GuardMsgs.lean`
//! (`parseGuardMsgsSpec`) folds the filters right to left, so the leftmost
//! filter that names a message's severity decides it.

/// The severity a `#guard_msgs` filter clause names
/// (`guardMsgsFilterSeverity := &"info" <|> &"warning" <|> &"error" <|> &"all"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardMsgsSeverity {
    /// `info`
    Info,
    /// `warning`
    Warning,
    /// `error`
    Error,
    /// `all`
    All,
}

/// `whitespace := exact | normalized | lax`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardMsgsWhitespace {
    /// Exact equality after trimming.
    Exact,
    /// Newlines read as spaces (Lean's default).
    Normalized,
    /// Every whitespace run collapsed to one space.
    Lax,
}

/// `ordering := exact | sorted`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardMsgsOrdering {
    /// The messages in the order the command produced them (Lean's default).
    Exact,
    /// The messages sorted lexicographically.
    Sorted,
}

/// One clause of `#guard_msgs (clause, …) in cmd`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardMsgsSpecElt {
    /// `info` / `warning` / `error` / `all`, optionally preceded by `drop`.
    Filter {
        /// Whether the clause was written `drop …`.
        drop: bool,
        /// The severity it names.
        severity: GuardMsgsSeverity,
    },
    /// `whitespace := …`.
    Whitespace(GuardMsgsWhitespace),
    /// `ordering := …`.
    Ordering(GuardMsgsOrdering),
}
