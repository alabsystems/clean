// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error type for the AFP wave session-ROOT generator.

use std::path::PathBuf;

use thiserror::Error;

/// Errors raised while planning or writing AFP wave session fragments.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum IsabelleSessionsError {
    /// Reading an input file (ROOT, `.thy`, entries list) failed.
    #[error("failed to read {path}: {source}")]
    Read {
        /// The file that failed to read.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Listing a directory (AFP thys root, spine source dir) failed.
    #[error("failed to list directory {path}: {source}")]
    ListDir {
        /// The directory that failed to list.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Writing an output fragment or manifest failed.
    #[error("failed to write {path}: {source}")]
    Write {
        /// The file that failed to write.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Creating the output directory failed.
    #[error("failed to create output dir {path}: {source}")]
    CreateDir {
        /// The directory that failed to create.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// `--cap 0` would make checkpoint chunking impossible (Python raised a
    /// bare `ValueError` from `range()`; this port refuses it loudly).
    #[error("--cap must be >= 1 (a checkpoint session holds at least one theory)")]
    ZeroCap,

    /// Spine planning needs the Isabelle installation's HOL source tree. A
    /// machine-specific developer path must never be guessed.
    #[error("spine mode requires --hol-src or ISABELLE_HOME (resolved as $ISABELLE_HOME/src/HOL)")]
    MissingHolSource,

    /// A `@`-chained spine references an upstream spine that emitted no
    /// sessions (Python died with a `KeyError` here).
    #[error("spine {spine}: upstream spine {upstream} emitted no sessions to chain on")]
    MissingUpstreamSpine {
        /// The spine whose first chunk needed the upstream heap.
        spine: String,
        /// The upstream spine that produced no captured chunks.
        upstream: String,
    },
}
