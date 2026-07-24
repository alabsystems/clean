// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error types for the HOL family importers.

use clean_kernel::open_theory::OpenTheoryError;
use thiserror::Error;

/// Result type for HOL import operations.
pub type HolResult<T> = Result<T, HolError>;

/// Errors raised during HOL Light / HOL4 / OpenTheory bridge import.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum HolError {
    /// Error from the kernel's OpenTheory pipeline.
    #[error("OpenTheory import error: {0}")]
    OpenTheory(#[from] OpenTheoryError),

    /// I/O error reading `.art` files from disk.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// No `.art` files found in the specified directory.
    #[error("no .art files found in directory: {path}")]
    NoArticlesFound { path: String },

    /// A specific article file failed to import.
    #[error("failed to import article {path}: {source}")]
    ArticleImportFailed {
        path: String,
        #[source]
        source: OpenTheoryError,
    },
}
