// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Why the export writer refused to write, or refused what it wrote.
//!
//! Every variant is fail-closed: the writer stops at the first one, and a
//! caller that publishes a file must not publish a partial one (the
//! `clean_export_write` binary writes to a partial name and renames last).

use thiserror::Error;

/// A refusal of the export writer.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ExportWriteError {
    /// The output could not be written.
    #[error("cannot write the export: {0}")]
    Io(#[from] std::io::Error),
    /// A target, or a constant its cone reaches, is not in the environment.
    #[error("constant '{name}' is in the cone and not in the environment")]
    AbsentConstant {
        /// The constant.
        name: String,
    },
    /// The cone has a reference cycle between declarations.
    #[error("the cone has a dependency cycle: {}", names.join(" -> "))]
    DependencyCycle {
        /// The declarations on the cycle.
        names: Vec<String>,
    },
    /// An `unsafe` or `partial` declaration is in the cone. Lean's replay
    /// leaves such a declaration out, so an export of it is no evidence.
    #[error("'{name}' is {marker}: the writer exports the safe fragment only")]
    OutsideSafeFragment {
        /// The declaration.
        name: String,
        /// `unsafe` or `partial`.
        marker: &'static str,
    },
    /// A definition, theorem or opaque constant whose value the environment
    /// does not hold.
    #[error("'{name}' is a {kind} whose value the environment does not hold")]
    MissingValue {
        /// The declaration.
        name: String,
        /// `def`, `thm` or `opaque`.
        kind: &'static str,
    },
    /// An expression form Lean's export format has no record for.
    #[error("'{declaration}' holds {what}, which Lean's export format cannot state")]
    Unexportable {
        /// The declaration being written.
        declaration: String,
        /// The form.
        what: String,
    },
    /// A record names a constant that no earlier record declares: a reader
    /// that checks as it reads would meet an unknown constant.
    #[error(
        "'{declaration}' mentions '{constant}', which no earlier record of the export declares"
    )]
    UndeclaredReference {
        /// The declaration being written.
        declaration: String,
        /// The constant it mentions.
        constant: String,
    },
    /// An inductive block the environment holds in a shape Lean's `inductive`
    /// record cannot state.
    #[error("inductive block '{block}': {problem}")]
    BlockShape {
        /// The block's first type.
        block: String,
        /// What is wrong.
        problem: String,
    },
    /// Two records would declare one name.
    #[error("'{name}' would be declared twice")]
    DuplicateDeclaration {
        /// The name.
        name: String,
    },
    /// The export, read back by Clean's reader, was refused or declined.
    #[error("Clean's reader does not read the export back: {message} ({rule})")]
    ReadBack {
        /// The reader's rule (`NdjsonError::rule`).
        rule: &'static str,
        /// The reader's message.
        message: String,
    },
    /// The export, read back and written again, is not the export.
    #[error("the export does not read back as itself: {problem}")]
    RoundTrip {
        /// What differs.
        problem: String,
    },
}
