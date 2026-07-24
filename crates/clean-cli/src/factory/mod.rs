// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned factory merge queue and declaration analysis surfaces (#3704).

use std::io;
use std::path::PathBuf;

use clap::{Args, Subcommand};

pub(crate) mod decl_index;
mod git;
mod merge_check;
mod module_scope;
mod queue;
pub(crate) mod theorem_index;

/// Arguments accepted by `clean factory merge-check`.
#[derive(Debug, Clone, Args)]
pub(crate) struct MergeCheckArgs {
    /// Base revision that the candidate must be checked against.
    #[arg(long, default_value = "HEAD~1")]
    pub base: String,
    /// Candidate revision to check before landing.
    #[arg(long, default_value = "HEAD")]
    pub candidate: String,
    /// Repository root containing the Git checkout.
    #[arg(long, value_name = "PATH", default_value = ".")]
    pub repo_root: PathBuf,
    /// Merge policy profile name recorded in diagnostics.
    #[arg(long, default_value = "lean-source")]
    pub profile: String,
    /// Math project manifest or directory to hygiene-check in the candidate worktree.
    #[arg(long = "math-project", value_name = "PATH")]
    pub math_projects: Vec<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean factory decl-index`.
#[derive(Debug, Clone, Args)]
pub(crate) struct DeclIndexArgs {
    /// Repository or source root to scan.
    #[arg(long, value_name = "PATH", default_value = ".")]
    pub root: PathBuf,
    /// Merge policy profile name recorded in the index.
    #[arg(long, default_value = "lean-source")]
    pub profile: String,
    /// Restrict indexing to these paths, relative to --root unless absolute.
    #[arg(long = "path", value_name = "PATH")]
    pub paths: Vec<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean factory theorem-index`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TheoremIndexArgs {
    /// Repository or source root to scan.
    #[arg(long, value_name = "PATH", default_value = ".")]
    pub root: PathBuf,
    /// Merge policy profile name recorded in the index.
    #[arg(long, default_value = "lean-source")]
    pub profile: String,
    /// Restrict indexing to these paths, relative to --root unless absolute.
    #[arg(long = "path", value_name = "PATH")]
    pub paths: Vec<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Verbs under `clean factory queue`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum QueueCommands {
    /// Add a Git revision to the Rust-owned merge queue.
    Push(QueuePushArgs),
    /// Print queue state.
    Status(QueueStatusArgs),
    /// Validate and fast-forward land the next ready queue entry.
    ProcessNext(QueueProcessNextArgs),
}

/// Arguments accepted by `clean factory queue push`.
#[derive(Debug, Clone, Args)]
pub(crate) struct QueuePushArgs {
    /// Candidate Git revision to enqueue.
    pub target: String,
    /// Base branch/ref to land into.
    #[arg(long, default_value = "main")]
    pub base: String,
    /// Queue priority; lower numbers are processed first.
    #[arg(long, default_value_t = 100)]
    pub priority: i64,
    /// Optional human note stored with the queue entry.
    #[arg(long)]
    pub note: Option<String>,
    /// Queue state file.
    #[arg(long, value_name = "PATH", default_value = queue::DEFAULT_QUEUE_PATH)]
    pub queue: PathBuf,
    /// Repository root containing the Git checkout.
    #[arg(long, value_name = "PATH", default_value = ".")]
    pub repo_root: PathBuf,
}

/// Arguments accepted by `clean factory queue status`.
#[derive(Debug, Clone, Args)]
pub(crate) struct QueueStatusArgs {
    /// Queue state file.
    #[arg(long, value_name = "PATH", default_value = queue::DEFAULT_QUEUE_PATH)]
    pub queue: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean factory queue process-next`.
#[derive(Debug, Clone, Args)]
pub(crate) struct QueueProcessNextArgs {
    /// Queue state file.
    #[arg(long, value_name = "PATH", default_value = queue::DEFAULT_QUEUE_PATH)]
    pub queue: PathBuf,
    /// Repository root containing the Git checkout.
    #[arg(long, value_name = "PATH", default_value = ".")]
    pub repo_root: PathBuf,
    /// Merge policy profile name recorded in diagnostics.
    #[arg(long, default_value = "proof-factory")]
    pub profile: String,
    /// Optional shell command run in a clean candidate worktree after merge checks.
    #[arg(long, value_name = "CMD")]
    pub verify_cmd: Option<String>,
    /// Math project manifest or directory to hygiene-check in the candidate worktree.
    #[arg(long = "math-project", value_name = "PATH")]
    pub math_projects: Vec<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub json: bool,
}

/// Errors surfaced by Rust-owned factory operations.
#[derive(Debug, thiserror::Error)]
pub(crate) enum FactoryOpsError {
    /// Reading or writing a path failed.
    #[error("factory I/O error at {path}: {source}")]
    Io {
        /// Path that failed.
        path: PathBuf,
        /// Underlying I/O error.
        #[source]
        source: io::Error,
    },
    /// Writing command output failed.
    #[error("failed to write factory output: {0}")]
    Output(#[from] io::Error),
    /// Serializing or parsing JSON failed.
    #[error("factory JSON error: {0}")]
    Json(#[from] serde_json::Error),
    /// A Git command failed.
    #[error("factory Git command failed during {action}: {message}")]
    Git {
        /// High-level operation.
        action: String,
        /// Combined Git output.
        message: String,
    },
    /// Lean parsing or elaboration failed.
    #[error("factory Lean analysis failed for {path}: {message}")]
    LeanAnalysis {
        /// File being analyzed.
        path: PathBuf,
        /// Error detail.
        message: String,
    },
    /// Merge policy rejected the candidate.
    #[error("factory merge check rejected candidate: {0}")]
    MergeRejected(String),
    /// Queue lock acquisition failed.
    #[error("factory queue is locked at {path}")]
    QueueLocked {
        /// Lock file path.
        path: PathBuf,
    },
    /// The queue does not contain a processable item.
    #[error("factory queue is empty")]
    QueueEmpty,
    /// Queue state is invalid.
    #[error("factory queue state is invalid: {0}")]
    QueueState(String),
}

pub(crate) fn run_decl_index(args: DeclIndexArgs) -> Result<(), FactoryOpsError> {
    decl_index::run_decl_index(args)
}

pub(crate) fn run_theorem_index(args: TheoremIndexArgs) -> Result<(), FactoryOpsError> {
    theorem_index::run_theorem_index(args)
}

pub(crate) fn run_merge_check(args: MergeCheckArgs) -> Result<(), FactoryOpsError> {
    merge_check::run_merge_check(args)
}

pub(crate) fn run_queue_command(command: QueueCommands) -> Result<(), FactoryOpsError> {
    queue::run_queue_command(command)
}
