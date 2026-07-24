// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Error type for the self-healing Isabelle capture-chain driver.

use std::path::PathBuf;

use thiserror::Error;

/// Errors raised while parsing, planning, or executing a capture chain.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CaptureChainError {
    /// Reading the input spec file failed.
    #[error("failed to read chain spec {path}: {source}")]
    SpecRead {
        /// The spec file that failed to read.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Deserializing the input spec JSON failed.
    #[error("failed to parse chain spec {path}: {source}")]
    SpecParse {
        /// The spec file that failed to parse.
        path: PathBuf,
        /// Underlying JSON error.
        #[source]
        source: serde_json::Error,
    },

    /// The spec parsed but is semantically invalid (empty, duplicate session,
    /// forward parent reference, …).
    #[error("invalid chain spec: {reason}")]
    SpecInvalid {
        /// Human-readable validation failure.
        reason: String,
    },

    /// Reading the durable state file failed.
    #[error("failed to read state file {path}: {source}")]
    StateRead {
        /// The state file that failed to read.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Deserializing the durable state file JSON failed.
    #[error("failed to parse state file {path}: {source}")]
    StateParse {
        /// The state file that failed to parse.
        path: PathBuf,
        /// Underlying JSON error.
        #[source]
        source: serde_json::Error,
    },

    /// Writing the durable state file failed.
    #[error("failed to write state file {path}: {source}")]
    StateWrite {
        /// The state file that failed to write.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// A `--resume` was requested but the on-disk state was produced from a
    /// DIFFERENT spec (its hash does not match). Refusing to resume against a
    /// changed plan protects the response-ladder history.
    #[error(
        "cannot resume: state file was written for a different spec \
         (state spec-hash {state_hash}, current spec-hash {spec_hash}); \
         delete the state file to start fresh"
    )]
    SpecChanged {
        /// Spec hash recorded in the state file.
        state_hash: String,
        /// Spec hash of the spec passed on this run.
        spec_hash: String,
    },

    /// Creating a directory (segment `-d` dir, work dir, collect dir) failed.
    #[error("failed to create directory {path}: {source}")]
    CreateDir {
        /// The directory that failed to create.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Writing a generated `ROOT` file failed.
    #[error("failed to write ROOT {path}: {source}")]
    RootWrite {
        /// The ROOT file that failed to write.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Appending to the durable build log failed.
    #[error("failed to append build log {path}: {source}")]
    LogWrite {
        /// The log file that failed to append.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Spawning the `isabelle build` process (via `nice`) failed.
    #[error("failed to spawn {program}: {source}")]
    Spawn {
        /// The program that failed to spawn (`/usr/bin/nice` or `isabelle`).
        program: String,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// Moving captured files during the collect step failed.
    #[error("failed to collect captures from {path}: {source}")]
    Collect {
        /// The directory involved in the failing move.
        path: PathBuf,
        /// Underlying IO error.
        #[source]
        source: std::io::Error,
    },

    /// A segment build failed for a reason other than "Run out of store" — the
    /// driver halts (no auto-retry loops on unknown errors) and surfaces the
    /// log tail so the operator can triage.
    #[error("segment {session} build failed (not an OOM); log tail:\n{tail}")]
    BuildFailed {
        /// The session whose build failed.
        session: String,
        /// The tail of the captured build log.
        tail: String,
    },

    /// A single-theory segment already baked proofless (record_proofs=2) STILL
    /// ran out of store — the response ladder is exhausted. This is a genuine
    /// dead-end that needs human attention, not another auto-retry.
    #[error(
        "segment {session} exhausted the response ladder: single theory {theory} \
         runs out of store even at record_proofs=2 (proofless). Manual intervention needed."
    )]
    LadderExhausted {
        /// The stuck session.
        session: String,
        /// The theory that keeps blowing the store.
        theory: String,
    },
}
