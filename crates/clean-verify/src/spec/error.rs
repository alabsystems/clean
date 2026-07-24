// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Specification error types

/// Specification error
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum SpecError {
    /// Definition name not found in the specification
    #[error("Unknown definition: {0}")]
    UnknownDefinition(String),
    /// Failed to parse the specification source
    #[error("Parse error: {0}")]
    ParseError(String),
    /// Type elaboration failed for a definition
    #[error("Elaboration error: {0}")]
    ElabError(String),
    /// Type checking failed for a definition
    #[error("Type error: {0}")]
    TypeError(String),
    /// Environment operation failed (e.g., duplicate name)
    #[error("Environment error: {0}")]
    EnvError(String),
    /// Definition exists but has no elaborated form
    #[error("Missing elaboration for definition {0}")]
    MissingElaboration(String),
}
