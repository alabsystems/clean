// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use crate::FeatureDescriptor;

/// Typed lint failures for descriptor validation helpers.
///
/// Paths in error variants are space-joined (e.g. `"kernel verify"`) so that
/// error messages match the user-facing form of a command.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum LintError {
    /// The descriptor does not provide any example commands.
    #[error("feature `{path}` has no examples")]
    NoExamples {
        /// The feature path (space-joined) that failed validation.
        path: String,
    },
    /// One of the descriptor's example commands failed to parse.
    #[error("feature `{path}` example {index} ({cmd}) failed to parse: {reason}")]
    ExampleParseFailed {
        /// The descriptor path (space-joined) that owns the failing example.
        path: String,
        /// The zero-based index of the failing example.
        index: usize,
        /// The example command string that failed to parse.
        cmd: &'static str,
        /// The parser's error text.
        reason: String,
    },
    /// Multiple descriptors share the same `path`.
    #[error("duplicate feature path `{0}`")]
    DuplicatePath(String),
}

/// Check that a descriptor exposes at least one example command.
#[must_use = "lint result must be checked"]
pub fn ensure_has_example(descriptor: &FeatureDescriptor) -> Result<(), LintError> {
    if descriptor.examples.is_empty() {
        return Err(LintError::NoExamples {
            path: descriptor.path_display(),
        });
    }

    Ok(())
}

/// Check that every example command parses under the caller-supplied parser.
///
/// The parser is injected so this crate does not pull in `clap` by default —
/// callers wire up `clap::Parser::try_parse_from` at the call site. The
/// optional `clap-interop` feature ships
/// [`crate::try_parse_example`] as a convenience wrapper.
#[must_use = "lint result must be checked"]
pub fn ensure_all_examples_parseable<P>(
    descriptor: &FeatureDescriptor,
    parser: P,
) -> Result<(), LintError>
where
    P: Fn(&str) -> Result<(), String>,
{
    for (index, example) in descriptor.examples.iter().enumerate() {
        if let Err(reason) = parser(example.cmd) {
            return Err(LintError::ExampleParseFailed {
                path: descriptor.path_display(),
                index,
                cmd: example.cmd,
                reason,
            });
        }
    }

    Ok(())
}

/// Check that no two descriptors in the slice share the same feature path.
#[must_use = "lint result must be checked"]
pub fn ensure_unique_paths(descriptors: &[&FeatureDescriptor]) -> Result<(), LintError> {
    let mut seen: HashSet<&[&'static str]> = HashSet::new();

    for descriptor in descriptors {
        if !seen.insert(descriptor.path) {
            return Err(LintError::DuplicatePath(descriptor.path_display()));
        }
    }

    Ok(())
}
