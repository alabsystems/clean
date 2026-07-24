// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use clap::{Args, Subcommand, ValueEnum};

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathCommands {
    /// Project lifecycle and hygiene commands.
    Project {
        #[command(subcommand)]
        command: MathProjectCommands,
    },
    /// Domain-profile inspection commands.
    Profile {
        #[command(subcommand)]
        command: MathProfileCommands,
    },
    /// Emit a theorem index scoped to the project's theorem packs.
    TheoremIndex(MathTheoremIndexArgs),
    /// Generic proof-obligation commands.
    Obligation {
        #[command(subcommand)]
        command: MathObligationCommands,
    },
    /// External proof-artifact commands.
    Artifact {
        #[command(subcommand)]
        command: MathArtifactCommands,
    },
    /// Consumer-facing certificate-summary commands.
    Certificate {
        #[command(subcommand)]
        command: MathCertificateCommands,
    },
    /// Emit issue-ready proof work rows from project blockers.
    IssuePlan(MathIssuePlanArgs),
    /// Durable project-local proof task lifecycle commands.
    Task {
        #[command(subcommand)]
        command: MathTaskCommands,
    },
    /// Proof-state v2 bridge commands.
    ProofState {
        #[command(subcommand)]
        command: MathProofStateCommands,
    },
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathProjectCommands {
    /// Print project status from a math-project manifest.
    Status(ProjectStatusArgs),
    /// Write a starter math-project manifest.
    Init(ProjectInitArgs),
    /// Run project hygiene checks.
    Hygiene(ProjectStatusArgs),
    /// Emit a read-only project dashboard summary.
    Dashboard(ProjectStatusArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathProfileCommands {
    /// Inspect a built-in domain profile.
    Inspect(ProfileInspectArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathObligationCommands {
    /// Validate one generic obligation and compute its fingerprint.
    Validate(ObligationValidateArgs),
    /// Open one obligation as an ephemeral CLI proof-state handle.
    Open(ObligationOpenArgs),
    /// Attempt proof closure for one obligation.
    Prove(ObligationProveArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathArtifactCommands {
    /// Validate a proof-artifact-v1 envelope.
    Validate(ArtifactValidateArgs),
    /// Replay a proof-artifact-v1 payload when a public adapter exists.
    Replay(ArtifactReplayArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathCertificateCommands {
    /// Extract a consumer-facing certificate summary.
    Extract(CertificateExtractArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathTaskCommands {
    /// List durable local proof tasks.
    List(MathTaskListArgs),
    /// Show one durable local proof task.
    Status(MathTaskStatusArgs),
    /// Update one durable local proof task.
    Update(MathTaskUpdateArgs),
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathProofStateCommands {
    /// Open a theorem source location as a proof-state v2 handle.
    Open(ProofStateOpenArgs),
    /// Open a generic obligation as a proof-state v2 handle.
    OpenObligation(ProofStateOpenObligationArgs),
    /// Print a proof-state snapshot.
    Snapshot(ProofStateByStateArgs),
    /// Search theorem candidates for a proof-state goal.
    SearchTheorems(ProofStateGoalArgs),
    /// Search tactic candidates for a proof-state goal.
    SearchTactics(ProofStateGoalArgs),
    /// Apply a tactic script to a proof-state goal.
    Apply(ProofStateApplyArgs),
    /// Retain a proof state in the server lifecycle cache.
    Retain(ProofStateLifecycleArgs),
    /// Close a proof state in the server lifecycle cache.
    Close(ProofStateLifecycleArgs),
    /// Explain a failed tactic attempt.
    ExplainFailure(ProofStateAttemptArgs),
    /// Extract proof material from a proof state.
    Extract(ProofStateExtractArgs),
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProjectStatusArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProjectInitArgs {
    /// Built-in domain profile, such as `sat-pb` or `nn-verify`.
    #[arg(long, value_name = "PROFILE")]
    pub(crate) domain: String,
    /// Path to write the manifest.
    #[arg(long, value_name = "PATH")]
    pub(crate) output: PathBuf,
    /// Scaffold layout to write.
    #[arg(long, value_enum, default_value_t = ProjectInitLayout::Manifest)]
    pub(crate) layout: ProjectInitLayout,
    /// Stable project name to record in the manifest.
    #[arg(long, value_name = "NAME")]
    pub(crate) project_name: Option<String>,
    /// Emit JSON instead of a compact human-readable message.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(crate) enum ProjectInitLayout {
    /// Write only the math-project manifest at --output.
    Manifest,
    /// Create a project directory at --output with starter subdirectories.
    Full,
}

impl ProjectInitLayout {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Manifest => "manifest",
            Self::Full => "full",
        }
    }
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProfileInspectArgs {
    /// Domain profile to inspect.
    #[arg(long, value_name = "PROFILE")]
    pub(crate) domain: String,
    /// Optional project path used to resolve project-local domain_profiles/<name>.json.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: Option<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct MathTheoremIndexArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ObligationValidateArgs {
    /// Path to a `clean-obligation-v1` JSON file.
    pub(crate) path: PathBuf,
    /// Optional project manifest used for cross-validation.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: Option<PathBuf>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ObligationOpenArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Path to a `clean-obligation-v1` JSON file.
    pub(crate) path: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ObligationProveArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Path to a `clean-obligation-v1` JSON file.
    pub(crate) path: PathBuf,
    /// Opt in to the embedded server-backed proof-state path.
    #[arg(long)]
    pub(crate) proof_state: bool,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateOpenObligationArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Path to a `clean-obligation-v1` JSON file.
    pub(crate) path: PathBuf,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactValidateArgs {
    /// Path to a proof-artifact-v1 JSON file.
    pub(crate) path: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ArtifactReplayArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: Option<PathBuf>,
    /// Write the replay report into the project-local replay cache.
    #[arg(long)]
    pub(crate) cache: bool,
    /// Cache root to use when writing replay metadata. Setting this implies --cache.
    /// Relative paths are resolved from the project root.
    #[arg(long, value_name = "DIR")]
    pub(crate) cache_dir: Option<PathBuf>,
    /// Path to a proof-artifact-v1 JSON file.
    pub(crate) path: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct CertificateExtractArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Obligation fingerprint, or a path to an obligation JSON file.
    #[arg(long, value_name = "ID_OR_PATH")]
    pub(crate) obligation: String,
    /// Optional replayed artifact hash or path.
    #[arg(long, value_name = "HASH_OR_PATH")]
    pub(crate) artifact: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct MathIssuePlanArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Offline GitHub-like issue snapshot JSON used to mark existing open issues.
    #[arg(long, value_name = "SNAPSHOT_JSON")]
    pub(crate) dedupe_open: Option<PathBuf>,
    /// Directory for deterministic local issue files. Defaults to dry-run unless --write is set.
    #[arg(long, value_name = "DIR")]
    pub(crate) export_dir: Option<PathBuf>,
    /// Write local issue files into --export-dir instead of only reporting planned writes.
    #[arg(long, requires = "export_dir")]
    pub(crate) write: bool,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct MathTaskListArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct MathTaskStatusArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Obligation fingerprint, task id, issue key, or path to an obligation JSON file.
    #[arg(long, value_name = "ID_OR_PATH")]
    pub(crate) obligation: String,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct MathTaskUpdateArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Obligation fingerprint, task id, issue key, or path to an obligation JSON file.
    #[arg(long, value_name = "ID_OR_PATH")]
    pub(crate) obligation: String,
    /// Set task status.
    #[arg(long, value_enum)]
    pub(crate) status: Option<MathTaskStatusValue>,
    /// Append a durable note. Can be repeated.
    #[arg(long = "note", value_name = "TEXT")]
    pub(crate) notes: Vec<String>,
    /// Append a durable blocker. Can be repeated.
    #[arg(long = "blocker", value_name = "TEXT")]
    pub(crate) blockers: Vec<String>,
    /// Clear existing notes before appending new notes.
    #[arg(long)]
    pub(crate) clear_notes: bool,
    /// Clear existing blockers before appending new blockers.
    #[arg(long)]
    pub(crate) clear_blockers: bool,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(crate) enum MathTaskStatusValue {
    Open,
    InProgress,
    Blocked,
    Done,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateOpenArgs {
    /// Path to `math-project.json` or to a directory containing it.
    #[arg(long, value_name = "PATH")]
    pub(crate) project: PathBuf,
    /// Lean source file containing the target theorem.
    #[arg(long, value_name = "PATH")]
    pub(crate) file: PathBuf,
    /// Theorem/declaration name to open.
    #[arg(long, value_name = "NAME")]
    pub(crate) theorem: String,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateByStateArgs {
    /// Proof-state id returned by an open command.
    #[arg(long, value_name = "STATE")]
    pub(crate) state: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Snapshot format.
    #[arg(long, value_enum, default_value_t = SnapshotFormat::Llm)]
    pub(crate) format: SnapshotFormat,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub(crate) enum SnapshotFormat {
    Json,
    Llm,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateGoalArgs {
    /// Proof-state id returned by an open command.
    #[arg(long, value_name = "STATE")]
    pub(crate) state: String,
    /// Goal id inside the proof state.
    #[arg(long, value_name = "GOAL")]
    pub(crate) goal: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateApplyArgs {
    /// Proof-state id returned by an open command.
    #[arg(long, value_name = "STATE")]
    pub(crate) state: String,
    /// Goal id inside the proof state.
    #[arg(long, value_name = "GOAL")]
    pub(crate) goal: String,
    /// Tactic script to apply.
    #[arg(long, value_name = "SCRIPT")]
    pub(crate) tactic: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateAttemptArgs {
    /// Attempt id returned by `proof-state apply`.
    #[arg(long, value_name = "ATTEMPT")]
    pub(crate) attempt: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateLifecycleArgs {
    /// Proof-state id returned by an open command.
    #[arg(long, value_name = "STATE")]
    pub(crate) state: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct ProofStateExtractArgs {
    /// Proof-state id returned by an open command.
    #[arg(long, value_name = "STATE")]
    pub(crate) state: String,
    /// Persistent clean JSON-RPC server address, such as `127.0.0.1:8080`.
    #[arg(long, value_name = "HOST:PORT")]
    pub(crate) server: Option<String>,
    /// Extraction format.
    #[arg(long, default_value = "certificate")]
    pub(crate) format: String,
    /// Emit JSON instead of compact human-readable output.
    #[arg(long)]
    pub(crate) json: bool,
}
