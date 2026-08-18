// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clap argument types and the `ReplacementError` enum.

use super::*;

/// Verbs under `clean replacement`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum ReplacementCommands {
    /// Print the Lean4 replacement scorecard and HN launch gate.
    Status(ReplacementStatusArgs),
    /// Check the release issue hygiene gate.
    ReleaseIssueHygiene(ReleaseIssueHygieneArgs),
    /// Native-library replacement evidence surfaces.
    NativeLibrary {
        #[command(subcommand)]
        command: NativeLibraryCommands,
    },
    /// Validate a replacement evidence report without Python.
    ValidateReport(ValidateReportArgs),
    /// Verify axiom-audit evidence and optionally write launch evidence.
    AxiomAudit(AxiomAuditArgs),
    /// Print the tactic parity and strict reconstruction scorecard.
    TacticParity(TacticParityArgs),
    /// Print kernel differential and fallback-denial evidence.
    TrustCoreEvidence(TrustCoreEvidenceArgs),
    /// Summarize TrustBoundary TSV audit records.
    TrustBoundaryAudit(TrustBoundaryAuditArgs),
    /// Emit the Rust-first tooling migration inventory and evidence artifact.
    RustFirstTooling(RustFirstToolingEvidenceArgs),
}

/// Arguments accepted by `clean replacement status`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ReplacementStatusArgs {
    /// Emit JSON instead of a compact human-readable scorecard.
    #[arg(long)]
    pub json: bool,
    /// Render the informational (never-fail-closed) scorecard for AI-agent
    /// navigation instead of the fail-closed launch-gate report.
    #[arg(long)]
    pub informational: bool,
}

/// Arguments accepted by `clean replacement release-issue-hygiene`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ReleaseIssueHygieneArgs {
    /// Emit JSON instead of a compact human-readable NOT READY report.
    #[arg(long)]
    pub json: bool,
    /// Run a read-only live GitHub issue-list fetch with `gh issue list`.
    #[arg(long, conflicts_with = "input")]
    pub fetch: bool,
    /// Read a local gh issue-list JSON snapshot.
    #[arg(long, value_name = "SNAPSHOT")]
    pub input: Option<PathBuf>,
    /// Maximum issues to fetch with --fetch.
    #[arg(long, default_value_t = 500)]
    pub limit: usize,
}

/// Arguments accepted by `clean replacement validate-report`.
#[derive(Debug, Clone, Args)]
pub(crate) struct ValidateReportArgs {
    /// Replacement evidence report JSON to validate.
    #[arg(long, value_name = "REPORT")]
    pub report: PathBuf,
    /// Expected replacement report contract.
    #[arg(long, value_enum)]
    pub kind: ReplacementReportKind,
    /// Emit JSON instead of a compact human-readable validation summary.
    #[arg(long)]
    pub json: bool,
}

/// Supported replacement evidence report contracts.
#[derive(Debug, Clone, Copy, ValueEnum, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ReplacementReportKind {
    /// `reports/native-library-replacement.json`.
    NativeLibrary,
    /// `reports/mathverse-replay-replacement.json`.
    MathverseReplay,
    /// `reports/lsp-infoview-parity.json`.
    LspInfoview,
    /// `tests/lean4_compat/frontend_replacement_scorecard.json`.
    FrontendParity,
}

/// Arguments accepted by `clean replacement axiom-audit`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AxiomAuditArgs {
    /// Axiom audit JSON to verify.
    #[arg(long, value_name = "AUDIT")]
    pub verify: PathBuf,
    /// Optional launch evidence JSON to write after verification passes.
    #[arg(long, value_name = "EVIDENCE")]
    pub evidence: Option<PathBuf>,
    /// Emit JSON instead of a compact human-readable verification summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean replacement tactic-parity`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TacticParityArgs {
    #[command(subcommand)]
    pub command: Option<TacticParityCommands>,
    /// Emit JSON instead of a compact human-readable scorecard.
    #[arg(long)]
    pub json: bool,
}

/// Subcommands under `clean replacement tactic-parity`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum TacticParityCommands {
    /// Discover full-corpus tactic parity source manifests and real evidence inputs.
    #[command(name = "discover-full-corpus-inputs")]
    DiscoverFullCorpusInputs(TacticParityDiscoverFullCorpusInputsArgs),
    /// Generate a schema-valid, non-coverage full-corpus fixture artifact.
    #[command(name = "generate-full-corpus-fixture")]
    GenerateFullCorpusFixture(TacticParityGenerateFullCorpusFixtureArgs),
    /// Validate the full Lean4 tactic corpus acceptance artifact.
    #[command(name = "validate-full-corpus")]
    ValidateFullCorpus(TacticParityValidateFullCorpusArgs),
}

/// Arguments accepted by `clean replacement tactic-parity discover-full-corpus-inputs`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TacticParityDiscoverFullCorpusInputsArgs {
    /// Tactic parity eval registry to inspect.
    #[arg(
        long,
        value_name = "REGISTRY",
        default_value = "evals/registry/tactic-parity.yaml"
    )]
    pub registry: PathBuf,
    /// Emit JSON instead of a compact human-readable discovery summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean replacement tactic-parity generate-full-corpus-fixture`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TacticParityGenerateFullCorpusFixtureArgs {
    /// Output path for the generated non-coverage fixture artifact.
    #[arg(long, value_name = "REPORT")]
    pub output: PathBuf,
    /// Emit JSON instead of a compact human-readable generation summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean replacement tactic-parity validate-full-corpus`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TacticParityValidateFullCorpusArgs {
    /// Full-corpus tactic parity acceptance artifact to validate.
    #[arg(long, value_name = "REPORT")]
    pub report: PathBuf,
    /// Emit JSON instead of a compact human-readable validation summary.
    #[arg(long)]
    pub json: bool,
}

/// Arguments accepted by `clean replacement trust-core-evidence`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TrustCoreEvidenceArgs {
    /// Emit JSON instead of a compact human-readable scorecard.
    #[arg(long)]
    pub json: bool,
    /// Emit Rust-owned kernel soundness launch evidence instead of the aggregate report.
    #[arg(long)]
    pub kernel_soundness: bool,
    /// Emit Rust-owned DENY_SORRY launch evidence instead of the aggregate report.
    #[arg(long)]
    pub deny_sorry: bool,
    /// Optional output path for generated launch evidence.
    #[arg(long, value_name = "PATH")]
    pub evidence: Option<PathBuf>,
    /// Deterministic timestamp to record in generated launch evidence.
    #[arg(long, default_value = "1970-01-01T00:00:00Z")]
    pub generated_at: String,
}

/// Arguments accepted by `clean replacement rust-first-tooling`.
#[derive(Debug, Clone, Args)]
pub(crate) struct RustFirstToolingEvidenceArgs {
    /// Emit JSON instead of a compact human-readable inventory summary.
    #[arg(long)]
    pub json: bool,
    /// Optional evidence JSON path to write after the fail-closed checks pass.
    #[arg(long, value_name = "PATH")]
    pub evidence: Option<PathBuf>,
}

/// Arguments accepted by `clean replacement trust-boundary-audit`.
#[derive(Debug, Clone, Args)]
pub(crate) struct TrustBoundaryAuditArgs {
    /// TSV audit file(s) emitted by CLEAN_TRUST_BOUNDARY_AUDIT_PATH lanes.
    #[arg(long = "input", value_name = "TSV", required = true)]
    pub inputs: Vec<PathBuf>,
    /// Expected boundary-only test pattern file.
    #[arg(long, value_name = "PATTERNS", default_value = TRUST_BOUNDARY_EXPECTED_TESTS_PATH)]
    pub expected: PathBuf,
    /// Optional Markdown report path.
    #[arg(long, value_name = "REPORT")]
    pub output: Option<PathBuf>,
    /// Emit JSON instead of Markdown on stdout.
    #[arg(long)]
    pub json: bool,
}

/// Errors surfaced by `clean replacement`.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ReplacementError {
    /// Serializing the report failed.
    #[error("failed to serialize replacement JSON report: {0}")]
    Serialize(serde_json::Error),
    /// Reading a checked-in evidence artifact failed.
    #[error("failed to read replacement artifact {path}: {source}")]
    ReadArtifact {
        path: &'static str,
        #[source]
        source: io::Error,
    },
    /// Parsing a checked-in evidence artifact failed.
    #[error("failed to parse replacement artifact {path}: {source}")]
    ParseArtifact {
        path: &'static str,
        #[source]
        source: serde_json::Error,
    },
    /// A checked-in evidence artifact is readable but stale against its peer.
    #[error("stale replacement trust-core artifact: {message}")]
    StaleTrustCoreArtifact { message: String },
    /// The release issue hygiene gate is intentionally fail-closed when not ready.
    #[error("release issue hygiene gate is not ready: {message}")]
    ReleaseIssueHygieneNotReady { message: String },
    /// The launch gate ran and reported not-ready. Fail-closed means a nonzero
    /// exit: `clean replacement status && ...` must not proceed on a red gate.
    #[error("replacement launch gate is not ready: {message}")]
    LaunchNotReady { message: String },
    /// Reading a replacement evidence report failed.
    #[error("failed to read replacement report {path}: {source}")]
    ReadReport {
        path: String,
        #[source]
        source: io::Error,
    },
    /// Parsing a replacement evidence report failed.
    #[error("failed to parse replacement report {path}: {source}")]
    ParseReport {
        path: String,
        #[source]
        source: serde_json::Error,
    },
    /// A replacement evidence report failed its Rust validator.
    #[error("replacement report validation failed: {message}")]
    ReportValidation { message: String },
    /// Trust-boundary audit input was missing or malformed.
    #[error("trust-boundary audit input error: {message}")]
    TrustBoundaryAuditInput { message: String },
    /// Native-library replacement evidence failed.
    #[error(transparent)]
    NativeLibrary(#[from] NativeLibraryError),
    /// Writing output failed.
    #[error("failed to write replacement output: {0}")]
    Io(#[from] io::Error),
}
