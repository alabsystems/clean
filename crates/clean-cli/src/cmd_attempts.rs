// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean attempts` proof-attempt log commands.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_mathverse::attempt_log::{
    query_attempts_limited, read_artifact, validate_replay_binding, AttemptContext, AttemptFilter,
    AttemptProducer, AttemptQueryReport, AttemptQuerySummary, AttemptStatus, AttemptStatusFilter,
    AuthorityReceipt, AuthorityReceiptArtifact, ProducerKind, ProofAttempt,
    ReplayBindingValidationOptions,
};
use clean_mathverse::env_fingerprint::EnvFingerprint;
use clean_mathverse::evidence_query::{
    EvidenceQuery, EvidenceSupportRecord, MathverseEvidenceIndex,
};
use clean_mathverse::evidence_refresh::{
    plan_mathverse_evidence_refresh, RefreshPlan, RefreshPlanRequest,
};
use clean_mathverse::external_patch_attempt::{
    record_external_patch_attempt, ExternalPatchArtifact, ExternalPatchAttemptInput,
    ExternalPatchMetadata,
};
use clean_mathverse::types::TrustLevel;
use serde::Serialize;

pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["attempts", "list"],
        summary: "List and filter proof attempts from the Mathverse attempt log (Experimental)",
        description: "\
Experimental query surface over the append-only `.cake/attempts/*.jsonl` \
proof-attempt log (plus the legacy `.mathverse/attempts` directory). The \
command returns matching attempts in newest-first order \
and accepts filters for goal hash, status class, authority gate, stable failure \
mode, trust level, producer kind/provider/name, and external task id, plus an \
optional result `--limit`. `--json` emits the full `AttemptQueryReport` for \
release automation and evidence review.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts list --root .",
                what: "list the most recent proof attempts in the log",
            },
            Example {
                cmd: "clean attempts list --root . --authority-gate trust_audit --status accepted --limit 20 --json",
                what: "emit the 20 newest accepted trust-audit attempts as JSON",
            },
        ],
        see_also: &["attempts gates", "attempts query-evidence"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse attempt log",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["attempts", "refresh-plan"],
        summary: "Plan Mathverse authority-evidence refreshes (Experimental)",
        description: "\
Experimental JSON planning surface for Mathverse authority evidence regeneration. \
The command scans the project `.cake/attempts` log (plus the legacy \
`.mathverse/attempts` directory), compares required \
authority gates against the current environment fingerprint, and reports each \
gate as current, stale, or missing. Gate inputs may be repeated or comma \
delimited. Optional theorem and external task filters scope the plan to a \
specific proof target.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts refresh-plan --root . --gate trust_audit,statement_preservation --gate false_controls",
                what: "emit a JSON refresh plan for required gates",
            },
            Example {
                cmd: "clean attempts refresh-plan --root . --gate trust_audit --theorem-name Math.Target --task-id task-123",
                what: "emit a scoped refresh plan for one theorem and task",
            },
        ],
        see_also: &["attempts gates", "attempts list"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse evidence refresh",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["attempts", "gates"],
        summary: "Summarize authority-gate evidence from the Mathverse attempt log (Experimental)",
        description: "\
Experimental operator-visibility report for authority-gate evidence recorded in \
the append-only `.cake/attempts/*.jsonl` proof-attempt log (plus the legacy \
`.mathverse/attempts` directory). The command counts \
attempts by authority gate, failure mode, status kind, trust level, generic \
producer metadata, and external task id, including missing metadata. `--json` \
emits the deterministic summary for release automation and gate evidence review.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts gates --root .",
                what: "print a compact authority-gate evidence summary",
            },
            Example {
                cmd: "clean attempts gates --root . --json",
                what: "emit authority-gate evidence counts as JSON",
            },
        ],
        see_also: &[
            "attempts list",
            "attempts record-external-patch",
            "release readiness-smoke",
        ],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse attempt log",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["attempts", "query-evidence"],
        summary: "Query structured Mathverse evidence support records (Experimental)",
        description: "\
Experimental JSON evidence query over the structured Mathverse evidence index \
derived from `.cake/attempts/*.jsonl` and the legacy `.mathverse/attempts/*.jsonl`. \
Filters cover authority gate, theorem \
or declaration name, external task id, goal hash, and content-addressed artifact \
hash. The report includes a status, newest selected matching attempt, matching \
count, notes, and artifact/support details preserved by the existing evidence \
index.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts query-evidence --root . --authority-gate trust_audit --theorem-name Math.Target --task-id task-123 --json",
                what: "query evidence support for one theorem and external task",
            },
            Example {
                cmd: "clean attempts query-evidence --root . --goal-hash goal_hash --artifact-hash artifact_hash --json",
                what: "find evidence that references a specific goal and artifact",
            },
        ],
        see_also: &["attempts gates", "attempts list", "attempts refresh-plan"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse evidence query",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["attempts", "validate-replay-bindings"],
        summary: "Validate replay bindings for accepted Mathverse evidence (Experimental)",
        description: "\
Experimental release-gate check for accepted Mathverse proof attempts. The \
command verifies that accepted records carry reproducible environment metadata, \
content-addressed solver artifacts, command evidence, and authority policy \
metadata. Use `--latest-per-gate --gate ...` to validate the current required \
authority gates while retaining stricter full-history validation for audits.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts validate-replay-bindings --root . --json",
                what: "validate replay bindings for every accepted attempt",
            },
            Example {
                cmd: "clean attempts validate-replay-bindings --root . --latest-per-gate --gate trust_audit,statement_preservation,false_controls,trust_ledger --json",
                what: "validate the newest accepted evidence for required authority gates",
            },
        ],
        see_also: &["attempts query-evidence", "attempts refresh-plan", "attempts gates"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse replay binding validation",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["attempts", "record-external-patch"],
        summary: "Record a generic external patch attempt (Experimental)",
        description: "\
Records an externally produced patch attempt in the generic Mathverse attempt \
log without assigning product-specific semantics. Accepted attempts require \
`--patch`, a prompt digest or model response artifact, and replayable \
trust-audit, statement-preservation, and false-control artifact hashes. \
`--trust-ledger-hash` additionally binds recursive trust evidence when a \
downstream authority consumer requires it. They also require those accepted gate attempts to carry matching external patch \
task, prompt, or artifact context, and fail closed when `--root` is a dirty git worktree. Use `--allow-dirty \
--dirty-reason <reason>` only for reviewed dirty-root exceptions. Optional \
prompt and model response files are stored as content-addressed artifacts \
alongside generic producer and external run/task metadata. `--json` emits the \
recorded proof-attempt fields plus an `authority_receipt` derived from that \
attempt; for external patch attempts, the receipt artifact evidence is the \
recorded patch artifact.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean attempts record-external-patch --root . --goal-hash goal --status accepted --trust-audit-hash audit_artifact_hash --statement-preservation-hash drift_artifact_hash --false-controls-hash false_control_artifact_hash --trust-ledger-hash trust_ledger_artifact_hash --patch candidate.patch --prompt prompt.txt --producer-kind model --producer-provider provider --producer model-name --json",
                what: "record an accepted external patch attempt as JSON from a clean root",
            },
            Example {
                cmd: "clean attempts record-external-patch --root . --goal-hash goal --status accepted --trust-audit-hash audit_artifact_hash --statement-preservation-hash drift_artifact_hash --false-controls-hash false_control_artifact_hash --trust-ledger-hash trust_ledger_artifact_hash --patch candidate.patch --model-response response.json --producer-kind model --producer-provider provider --producer model-name --allow-dirty --dirty-reason reviewed-local-baseline --json",
                what: "record an accepted external patch from a reviewed dirty root",
            },
        ],
        see_also: &["attempts list", "attempts gates"],
        references: &[Reference {
            kind: RefKind::Crate,
            label: "clean-mathverse external patch attempts",
            target: "clean-mathverse",
        }],
        domain_root: Some("attempts"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// Proof-attempt log commands.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum AttemptCommands {
    /// List proof attempts from the Mathverse attempt log.
    List(AttemptListArgs),
    /// Plan authority-evidence refreshes for required gates.
    RefreshPlan(AttemptRefreshPlanArgs),
    /// Summarize authority-gate evidence recorded in the attempt log.
    Gates(AttemptGateArgs),
    /// Query structured evidence support records from the attempt log.
    QueryEvidence(AttemptQueryEvidenceArgs),
    /// Validate accepted replay-binding evidence.
    ValidateReplayBindings(AttemptValidateReplayBindingsArgs),
    /// Record a generic external patch attempt in the Mathverse attempt log.
    RecordExternalPatch(AttemptRecordExternalPatchArgs),
}

/// Arguments for `clean attempts list`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptListArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// Return attempts matching one goal hash.
    #[arg(long = "goal-hash")]
    pub(crate) goal_hash: Option<String>,
    /// Return attempts matching one status class.
    #[arg(long, value_parser = parse_attempt_status)]
    pub(crate) status: Option<AttemptStatusFilter>,
    /// Return attempts emitted by one authority gate.
    #[arg(long = "authority-gate")]
    pub(crate) authority_gate: Option<String>,
    /// Return attempts with one stable failure mode.
    #[arg(long = "failure-mode")]
    pub(crate) failure_mode: Option<String>,
    /// Return attempts with one trust level.
    #[arg(long = "trust-level", value_parser = parse_trust_level)]
    pub(crate) trust_level: Option<TrustLevel>,
    /// Return attempts with one producer kind.
    #[arg(long = "producer-kind", value_parser = parse_producer_kind)]
    pub(crate) producer_kind: Option<ProducerKind>,
    /// Return attempts from one producer provider.
    #[arg(long = "producer-provider")]
    pub(crate) producer_provider: Option<String>,
    /// Return attempts from one producer name.
    #[arg(long = "producer")]
    pub(crate) producer: Option<String>,
    /// Return attempts with one external task id.
    #[arg(long = "external-task-id")]
    pub(crate) external_task_id: Option<String>,
    /// Maximum number of matching attempts to return.
    #[arg(long)]
    pub(crate) limit: Option<usize>,
    /// Emit the full AttemptQueryReport JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Arguments for `clean attempts refresh-plan`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptRefreshPlanArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// Required authority gate. May be repeated or comma-delimited.
    #[arg(long = "gate", value_delimiter = ',', required = true)]
    pub(crate) gates: Vec<String>,
    /// Scope evidence to one theorem/declaration name.
    #[arg(long = "theorem-name")]
    pub(crate) theorem_name: Option<String>,
    /// Scope evidence to one external task id.
    #[arg(long = "task-id")]
    pub(crate) task_id: Option<String>,
}

/// Arguments for `clean attempts gates`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptGateArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// Emit the authority-gate evidence summary as JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Arguments for `clean attempts query-evidence`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptQueryEvidenceArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// Return evidence emitted by one authority gate.
    #[arg(long = "authority-gate")]
    pub(crate) authority_gate: Option<String>,
    /// Scope evidence to one theorem/declaration name.
    #[arg(long = "theorem-name")]
    pub(crate) theorem_name: Option<String>,
    /// Scope evidence to one external task id.
    #[arg(long = "task-id")]
    pub(crate) task_id: Option<String>,
    /// Return evidence for one goal hash.
    #[arg(long = "goal-hash")]
    pub(crate) goal_hash: Option<String>,
    /// Return evidence referencing one content-addressed artifact hash.
    #[arg(long = "artifact-hash")]
    pub(crate) artifact_hash: Option<String>,
    /// Emit JSON. This command's stable output is JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Arguments for `clean attempts validate-replay-bindings`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptValidateReplayBindingsArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// Validate accepted evidence for one authority gate.
    #[arg(long = "authority-gate")]
    pub(crate) authority_gate: Option<String>,
    /// Validate only the newest accepted record for each required gate.
    #[arg(long = "latest-per-gate", alias = "current-gates")]
    pub(crate) latest_per_gate: bool,
    /// Required authority gate for --latest-per-gate. May be repeated or comma-delimited.
    #[arg(long = "gate", value_delimiter = ',')]
    pub(crate) gates: Vec<String>,
    /// Do not require authority-gate/trust-level policy metadata on accepted evidence.
    #[arg(long = "no-policy-metadata")]
    pub(crate) no_policy_metadata: bool,
    /// Emit the replay-binding validation report as JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Arguments for `clean attempts record-external-patch`.
#[derive(Debug, Clone, Args)]
pub(crate) struct AttemptRecordExternalPatchArgs {
    /// Repository or project root containing the `.cake` (or legacy `.mathverse`) attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// BLAKE3 hash of the target goal, issue, theorem, or normalized objective.
    #[arg(long = "goal-hash")]
    pub(crate) goal_hash: String,
    /// Final external patch attempt status.
    #[arg(long, value_parser = parse_attempt_status)]
    pub(crate) status: AttemptStatusFilter,
    /// BLAKE3 hash of the primary gate/audit report.
    #[arg(long = "trust-audit-hash")]
    pub(crate) trust_audit_hash: String,
    /// BLAKE3 hash of the replayable statement-preservation/drift report artifact.
    #[arg(long = "statement-preservation-hash")]
    pub(crate) statement_preservation_hash: Option<String>,
    /// BLAKE3 hash of the replayable false-control report artifact.
    #[arg(long = "false-controls-hash")]
    pub(crate) false_controls_hash: Option<String>,
    /// BLAKE3 hash of the replayable trust-ledger audit artifact.
    #[arg(long = "trust-ledger-hash")]
    pub(crate) trust_ledger_hash: Option<String>,
    /// Patch file to store as the external patch artifact.
    #[arg(long)]
    pub(crate) patch: Option<PathBuf>,
    /// Optional prompt file to store in the external patch context artifact.
    #[arg(long)]
    pub(crate) prompt: Option<PathBuf>,
    /// Optional model/service response file to store in the external patch context artifact.
    #[arg(long = "model-response")]
    pub(crate) model_response: Option<PathBuf>,
    /// Generic producer kind.
    #[arg(long = "producer-kind", value_parser = parse_producer_kind)]
    pub(crate) producer_kind: ProducerKind,
    /// Producer provider or organization.
    #[arg(long = "producer-provider")]
    pub(crate) producer_provider: String,
    /// Producer name.
    #[arg(long = "producer")]
    pub(crate) producer: String,
    /// External run identifier assigned by the producer or orchestrator.
    #[arg(long = "external-run-id")]
    pub(crate) external_run_id: Option<String>,
    /// External task identifier assigned by the producer or orchestrator.
    #[arg(long = "external-task-id")]
    pub(crate) external_task_id: Option<String>,
    /// Stable failure-mode classification for rejected/timeout attempts.
    #[arg(long = "failure-mode")]
    pub(crate) failure_mode: Option<String>,
    /// Wall-clock duration in milliseconds.
    #[arg(long = "wall-time-ms", default_value_t = 0)]
    pub(crate) wall_time_ms: u64,
    /// Allow recording an accepted attempt from a dirty git worktree.
    #[arg(long = "allow-dirty")]
    pub(crate) allow_dirty: bool,
    /// Required explanation when --allow-dirty is used.
    #[arg(long = "dirty-reason")]
    pub(crate) dirty_reason: Option<String>,
    /// Emit the recorded ProofAttempt JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptGateReport {
    /// Number of attempts included in the report.
    pub(crate) total: usize,
    /// Deterministic count summary over all attempts.
    pub(crate) summary: AttemptQuerySummary,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptEvidenceQueryReport {
    pub(crate) status: AttemptEvidenceQueryStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) selected_attempt: Option<AttemptEvidenceSelected>,
    pub(crate) matching_count: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) notes: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) support: Option<EvidenceSupportRecord>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) artifacts: Vec<AttemptEvidenceArtifactInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum AttemptEvidenceQueryStatus {
    Found,
    NoMatch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptEvidenceSelected {
    pub(crate) attempt_id: String,
    pub(crate) attempt_status: AttemptStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) authority_gate: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) theorem_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) task_id: Option<String>,
    pub(crate) goal_hash: String,
    pub(crate) trust_audit_hash: String,
    pub(crate) created_at: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptEvidenceArtifactInfo {
    pub(crate) role: String,
    pub(crate) blake3: String,
    pub(crate) byte_len: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) kind: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) logical_name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptReplayBindingReport {
    pub(crate) root: PathBuf,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) authority_gate: Option<String>,
    pub(crate) scope: AttemptReplayBindingScope,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) required_gates: Vec<String>,
    pub(crate) total_accepted: usize,
    pub(crate) validated_entries: usize,
    pub(crate) valid: usize,
    pub(crate) missing: usize,
    pub(crate) stale: usize,
    pub(crate) entries: Vec<AttemptReplayBindingEntry>,
}

impl AttemptReplayBindingReport {
    fn is_valid(&self) -> bool {
        self.missing == 0 && self.stale == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct AttemptReplayBindingEntry {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) attempt_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) goal_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) authority_gate: Option<String>,
    pub(crate) status: AttemptReplayBindingStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) diagnostics: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum AttemptReplayBindingStatus {
    Valid,
    Missing,
    Stale,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum AttemptReplayBindingScope {
    AllAccepted,
    LatestPerGate,
}

pub(crate) fn handle_attempt_command(command: AttemptCommands) -> anyhow::Result<()> {
    match command {
        AttemptCommands::List(args) => list_attempts(args),
        AttemptCommands::RefreshPlan(args) => refresh_plan_attempts(args),
        AttemptCommands::Gates(args) => gates_attempts(args),
        AttemptCommands::QueryEvidence(args) => query_evidence_attempts(args),
        AttemptCommands::ValidateReplayBindings(args) => validate_replay_bindings(args),
        AttemptCommands::RecordExternalPatch(args) => record_external_patch(args),
    }
}

fn list_attempts(args: AttemptListArgs) -> anyhow::Result<()> {
    let report = query_attempts_for_list(&args)?;
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_human_report(&report);
    }
    Ok(())
}

fn refresh_plan_attempts(args: AttemptRefreshPlanArgs) -> anyhow::Result<()> {
    let plan = query_attempt_refresh_plan(&args)?;
    println!("{}", serde_json::to_string_pretty(&plan)?);
    Ok(())
}

fn gates_attempts(args: AttemptGateArgs) -> anyhow::Result<()> {
    let report = query_attempt_gates(&args)?;
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_gate_report(&report);
    }
    Ok(())
}

fn query_evidence_attempts(args: AttemptQueryEvidenceArgs) -> anyhow::Result<()> {
    let report = query_attempt_evidence(&args)?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

fn validate_replay_bindings(args: AttemptValidateReplayBindingsArgs) -> anyhow::Result<()> {
    let report = query_attempt_replay_bindings(&args)?;
    if args.json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        print_replay_binding_report(&report);
    }
    if !report.is_valid() {
        anyhow::bail!(
            "accepted replay-binding evidence is invalid: {} missing, {} stale",
            report.missing,
            report.stale
        );
    }
    Ok(())
}

fn record_external_patch(args: AttemptRecordExternalPatchArgs) -> anyhow::Result<()> {
    let attempt = record_external_patch_for_args(&args)?;
    if args.json {
        println!("{}", recorded_external_patch_json(&attempt)?);
    } else {
        print_recorded_attempt(&attempt);
    }
    Ok(())
}

pub(crate) fn query_attempts_for_list(
    args: &AttemptListArgs,
) -> anyhow::Result<AttemptQueryReport> {
    query_attempts_limited(&args.root, filter_from_args(args), args.limit).map_err(Into::into)
}

pub(crate) fn query_attempt_refresh_plan(
    args: &AttemptRefreshPlanArgs,
) -> anyhow::Result<RefreshPlan> {
    let gates = normalized_gate_args(&args.gates)?;
    let mut request = RefreshPlanRequest::new(&args.root, gates);
    if let Some(theorem_name) = args
        .theorem_name
        .as_deref()
        .map(str::trim)
        .filter(|value| !value.is_empty())
    {
        request = request.with_theorem_name(theorem_name);
    }
    if let Some(task_id) = args
        .task_id
        .as_deref()
        .map(str::trim)
        .filter(|value| !value.is_empty())
    {
        request = request.with_task_id(task_id);
    }
    plan_mathverse_evidence_refresh(request).map_err(Into::into)
}

pub(crate) fn record_external_patch_for_args(
    args: &AttemptRecordExternalPatchArgs,
) -> anyhow::Result<ProofAttempt> {
    let status = status_from_filter(args.status, args.wall_time_ms);
    if matches!(status, AttemptStatus::Accepted) && args.patch.is_none() {
        anyhow::bail!("accepted external patch attempt requires --patch");
    }
    if matches!(status, AttemptStatus::Accepted)
        && args.prompt.is_none()
        && args.model_response.is_none()
    {
        anyhow::bail!("accepted external patch attempt requires --prompt or --model-response");
    }

    let patch_bytes = read_optional_artifact_bytes(args.patch.as_deref(), "patch")?;
    let prompt_bytes = read_optional_artifact_bytes(args.prompt.as_deref(), "prompt")?;
    let model_response_bytes =
        read_optional_artifact_bytes(args.model_response.as_deref(), "model response")?;

    let patch = patch_bytes.as_ref().map(|bytes| {
        ExternalPatchArtifact::patch_bytes(bytes.as_slice(), logical_name(args.patch.as_deref()))
    });
    let prompt = prompt_bytes
        .as_ref()
        .map(|bytes| ExternalPatchArtifact::Bytes {
            bytes: bytes.as_slice(),
            kind: Some("external_patch/prompt"),
            logical_name: logical_name(args.prompt.as_deref()),
        });
    let model_response = model_response_bytes
        .as_ref()
        .map(|bytes| ExternalPatchArtifact::Bytes {
            bytes: bytes.as_slice(),
            kind: Some("external_patch/model_response"),
            logical_name: logical_name(args.model_response.as_deref()),
        });

    let mut metadata = ExternalPatchMetadata::default();
    if let Some(hash) = args.statement_preservation_hash.as_ref() {
        metadata
            .gate_hashes
            .insert("statement_preservation".to_owned(), hash.clone());
    }
    if let Some(hash) = args.false_controls_hash.as_ref() {
        metadata
            .gate_hashes
            .insert("false_controls".to_owned(), hash.clone());
    }
    if let Some(hash) = args.trust_ledger_hash.as_ref() {
        metadata
            .gate_hashes
            .insert("trust_ledger".to_owned(), hash.clone());
    }

    let input = ExternalPatchAttemptInput {
        patch,
        prompt,
        model_response,
        producer: Some(AttemptProducer {
            producer_kind: args.producer_kind,
            provider: args.producer_provider.clone(),
            name: args.producer.clone(),
            version: None,
            command_digest: None,
        }),
        context: AttemptContext {
            external_run_id: args.external_run_id.clone(),
            external_task_id: args.external_task_id.clone(),
            prompt_digest: prompt_bytes
                .as_ref()
                .map(|bytes| blake3::hash(bytes).to_hex().to_string()),
            patch_artifact: None,
        },
        failure_mode: args.failure_mode.clone(),
        wall_time_ms: args.wall_time_ms,
        metadata,
        allow_dirty_root_reason: dirty_root_reason_from_args(args)?,
        ..ExternalPatchAttemptInput::new(
            args.goal_hash.clone(),
            status,
            args.trust_audit_hash.clone(),
            EnvFingerprint::capture(&args.root)?,
        )
    };

    record_external_patch_attempt(&args.root, input).map_err(Into::into)
}

fn dirty_root_reason_from_args(
    args: &AttemptRecordExternalPatchArgs,
) -> anyhow::Result<Option<String>> {
    if !args.allow_dirty {
        if args.dirty_reason.is_some() {
            anyhow::bail!("--dirty-reason requires --allow-dirty");
        }
        return Ok(None);
    }

    let reason = args
        .dirty_reason
        .as_deref()
        .map(str::trim)
        .filter(|reason| !reason.is_empty())
        .ok_or_else(|| anyhow::anyhow!("--allow-dirty requires a non-empty --dirty-reason"))?;
    Ok(Some(reason.to_owned()))
}

pub(crate) fn query_attempt_gates(args: &AttemptGateArgs) -> anyhow::Result<AttemptGateReport> {
    let report = query_attempts_limited(&args.root, AttemptFilter::default(), None)?;
    Ok(AttemptGateReport {
        total: report.total,
        summary: report.summary,
    })
}

pub(crate) fn query_attempt_evidence(
    args: &AttemptQueryEvidenceArgs,
) -> anyhow::Result<AttemptEvidenceQueryReport> {
    let index = MathverseEvidenceIndex::scan(&args.root)?;
    let query = EvidenceQuery {
        theorem_name: trimmed_option(args.theorem_name.as_deref()),
        task_id: trimmed_option(args.task_id.as_deref()),
        authority_gate: trimmed_option(args.authority_gate.as_deref()),
        ..EvidenceQuery::default()
    };
    let mut matches = index.query(&query);
    if let Some(goal_hash) = trimmed_option(args.goal_hash.as_deref()) {
        matches.retain(|record| record.goal_hash == goal_hash);
    }
    if let Some(artifact_hash) = trimmed_option(args.artifact_hash.as_deref()) {
        matches.retain(|record| {
            record
                .artifact_hashes
                .iter()
                .any(|hash| hash == &artifact_hash)
        });
    }

    let selected = matches.iter().max_by(evidence_record_order).cloned();
    let matching_count = matches.len();
    let mut notes = Vec::new();
    if matching_count == 0 {
        notes.push("no evidence support records matched the query".to_owned());
    } else if matching_count > 1 {
        notes.push(
            "selected newest matching evidence record by created_at, then attempt_id".to_owned(),
        );
    }

    let artifacts = selected
        .as_ref()
        .map(evidence_artifact_infos)
        .unwrap_or_default();
    let selected_attempt = selected.as_ref().map(selected_attempt_summary);

    Ok(AttemptEvidenceQueryReport {
        status: if selected.is_some() {
            AttemptEvidenceQueryStatus::Found
        } else {
            AttemptEvidenceQueryStatus::NoMatch
        },
        selected_attempt,
        matching_count,
        notes,
        support: selected,
        artifacts,
    })
}

fn evidence_record_order(
    left: &&EvidenceSupportRecord,
    right: &&EvidenceSupportRecord,
) -> std::cmp::Ordering {
    left.created_at
        .cmp(&right.created_at)
        .then_with(|| left.attempt_id.cmp(&right.attempt_id))
}

fn selected_attempt_summary(record: &EvidenceSupportRecord) -> AttemptEvidenceSelected {
    AttemptEvidenceSelected {
        attempt_id: record.attempt_id.to_string(),
        attempt_status: record.status.clone(),
        authority_gate: record.authority_gate.clone(),
        theorem_name: record.theorem_name.clone(),
        task_id: record.task_id.clone(),
        goal_hash: record.goal_hash.clone(),
        trust_audit_hash: record.trust_audit_hash.clone(),
        created_at: record.created_at,
    }
}

fn evidence_artifact_infos(record: &EvidenceSupportRecord) -> Vec<AttemptEvidenceArtifactInfo> {
    record
        .artifacts
        .iter()
        .map(|artifact| AttemptEvidenceArtifactInfo {
            role: artifact.role.clone(),
            blake3: artifact.artifact.blake3.clone(),
            byte_len: artifact.artifact.byte_len,
            kind: artifact.artifact.kind.clone(),
            logical_name: artifact.artifact.logical_name.clone(),
        })
        .collect()
}

fn trimmed_option(value: Option<&str>) -> Option<String> {
    value
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
}

pub(crate) fn query_attempt_replay_bindings(
    args: &AttemptValidateReplayBindingsArgs,
) -> anyhow::Result<AttemptReplayBindingReport> {
    let current_env = EnvFingerprint::capture(&args.root)?;
    let required_gates = required_replay_binding_gates(args)?;
    let filter = AttemptFilter {
        status: Some(AttemptStatusFilter::Accepted),
        authority_gate: if args.latest_per_gate {
            None
        } else {
            args.authority_gate.clone()
        },
        ..AttemptFilter::default()
    };
    let attempts = query_attempts_limited(&args.root, filter, None)?.attempts;
    let total_accepted = attempts.len();
    let options = ReplayBindingValidationOptions {
        allow_non_accepted: false,
        require_policy_metadata: !args.no_policy_metadata,
    };

    let mut valid = 0;
    let mut missing = 0;
    let mut stale = 0;
    let mut entries = if args.latest_per_gate {
        Vec::with_capacity(required_gates.len())
    } else {
        Vec::with_capacity(attempts.len())
    };

    if args.latest_per_gate {
        let latest = latest_attempts_by_gate(attempts);
        for gate in &required_gates {
            let Some(attempt) = latest.get(gate) else {
                missing += 1;
                entries.push(AttemptReplayBindingEntry {
                    attempt_id: None,
                    goal_hash: None,
                    authority_gate: Some(gate.clone()),
                    status: AttemptReplayBindingStatus::Missing,
                    diagnostics: vec![format!(
                        "no accepted replay-binding evidence found for required authority gate `{gate}`"
                    )],
                });
                continue;
            };
            entries.push(classify_replay_binding_entry(
                attempt,
                &args.root,
                &current_env,
                options,
                &mut valid,
                &mut missing,
                &mut stale,
            ));
        }
    } else {
        for attempt in &attempts {
            entries.push(classify_replay_binding_entry(
                attempt,
                &args.root,
                &current_env,
                options,
                &mut valid,
                &mut missing,
                &mut stale,
            ));
        }
    }

    Ok(AttemptReplayBindingReport {
        root: args.root.clone(),
        authority_gate: args.authority_gate.clone(),
        scope: if args.latest_per_gate {
            AttemptReplayBindingScope::LatestPerGate
        } else {
            AttemptReplayBindingScope::AllAccepted
        },
        required_gates,
        total_accepted,
        validated_entries: entries.len(),
        valid,
        missing,
        stale,
        entries,
    })
}

fn required_replay_binding_gates(
    args: &AttemptValidateReplayBindingsArgs,
) -> anyhow::Result<Vec<String>> {
    if !args.latest_per_gate {
        if !args.gates.is_empty() {
            anyhow::bail!("--gate requires --latest-per-gate");
        }
        return Ok(Vec::new());
    }

    if args.authority_gate.is_some() && !args.gates.is_empty() {
        anyhow::bail!("use either --authority-gate or --gate with --latest-per-gate, not both");
    }

    let gates = if !args.gates.is_empty() {
        normalized_gate_args(&args.gates)?
    } else if let Some(gate) = args
        .authority_gate
        .as_deref()
        .map(str::trim)
        .filter(|gate| !gate.is_empty())
    {
        vec![gate.to_owned()]
    } else {
        anyhow::bail!("--latest-per-gate requires at least one --gate");
    };
    Ok(gates)
}

fn latest_attempts_by_gate(attempts: Vec<ProofAttempt>) -> BTreeMap<String, ProofAttempt> {
    let mut latest = BTreeMap::new();
    for attempt in attempts {
        let Some(gate) = attempt
            .authority_gate
            .as_deref()
            .map(str::trim)
            .filter(|gate| !gate.is_empty())
            .map(str::to_owned)
        else {
            continue;
        };

        latest
            .entry(gate)
            .and_modify(|existing: &mut ProofAttempt| {
                if replay_attempt_order(&attempt, existing).is_gt() {
                    *existing = attempt.clone();
                }
            })
            .or_insert(attempt);
    }
    latest
}

fn replay_attempt_order(left: &ProofAttempt, right: &ProofAttempt) -> std::cmp::Ordering {
    left.created_at
        .cmp(&right.created_at)
        .then_with(|| left.attempt_id.cmp(&right.attempt_id))
}

fn classify_replay_binding_entry(
    attempt: &ProofAttempt,
    root: &Path,
    current_env: &EnvFingerprint,
    options: ReplayBindingValidationOptions,
    valid: &mut usize,
    missing: &mut usize,
    stale: &mut usize,
) -> AttemptReplayBindingEntry {
    let mut diagnostics = Vec::new();
    if let Err(err) = validate_replay_binding(attempt, options) {
        diagnostics.push(err.to_string());
    }
    for artifact in attempt.artifact_refs() {
        if let Err(err) = read_artifact(root, artifact) {
            diagnostics.push(err.to_string());
        }
    }

    let status = if !diagnostics.is_empty() {
        *missing += 1;
        AttemptReplayBindingStatus::Missing
    } else if &attempt.env != current_env {
        *stale += 1;
        diagnostics.push(
            "accepted replay binding environment does not match current environment".to_owned(),
        );
        AttemptReplayBindingStatus::Stale
    } else {
        *valid += 1;
        AttemptReplayBindingStatus::Valid
    };

    AttemptReplayBindingEntry {
        attempt_id: Some(attempt.attempt_id.to_string()),
        goal_hash: Some(attempt.goal_hash.clone()),
        authority_gate: attempt.authority_gate.clone(),
        status,
        diagnostics,
    }
}

fn normalized_gate_args(gates: &[String]) -> anyhow::Result<Vec<String>> {
    let gates = gates
        .iter()
        .flat_map(|gate| gate.split(','))
        .map(str::trim)
        .filter(|gate| !gate.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if gates.is_empty() {
        anyhow::bail!("at least one non-empty --gate is required");
    }
    Ok(gates)
}

fn read_optional_artifact_bytes(
    path: Option<&Path>,
    label: &str,
) -> anyhow::Result<Option<Vec<u8>>> {
    path.map(|path| {
        std::fs::read(path).map_err(|err| {
            anyhow::anyhow!("failed to read {label} file `{}`: {err}", path.display())
        })
    })
    .transpose()
}

fn logical_name(path: Option<&Path>) -> Option<&str> {
    path.and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
}

fn recorded_external_patch_json(attempt: &ProofAttempt) -> anyhow::Result<String> {
    let mut value = serde_json::to_value(attempt)?;
    value["authority_receipt"] = serde_json::to_value(external_patch_authority_receipt(attempt))?;
    serde_json::to_string_pretty(&value).map_err(Into::into)
}

fn external_patch_authority_receipt(attempt: &ProofAttempt) -> AuthorityReceipt {
    let mut receipt = AuthorityReceipt::from_attempt(attempt);
    if receipt.solver_artifact.is_none() {
        receipt.solver_artifact = attempt
            .context
            .as_ref()
            .and_then(|context| context.patch_artifact.as_ref())
            .map(|artifact| AuthorityReceiptArtifact {
                blake3: artifact.blake3.clone(),
                byte_len: artifact.byte_len,
                kind: artifact.kind.clone(),
                logical_name: artifact.logical_name.clone(),
            });
    }
    receipt
}

fn status_from_filter(status: AttemptStatusFilter, wall_time_ms: u64) -> AttemptStatus {
    match status {
        AttemptStatusFilter::Accepted => AttemptStatus::Accepted,
        AttemptStatusFilter::Rejected => AttemptStatus::Rejected {
            reason: "external patch attempt rejected".to_owned(),
        },
        AttemptStatusFilter::Timeout => AttemptStatus::Timeout {
            after_ms: wall_time_ms,
        },
    }
}

fn filter_from_args(args: &AttemptListArgs) -> AttemptFilter {
    AttemptFilter {
        goal_hash: args.goal_hash.clone(),
        status: args.status,
        authority_gate: args.authority_gate.clone(),
        failure_mode: args.failure_mode.clone(),
        trust_level: args.trust_level,
        producer_kind: args.producer_kind,
        producer_provider: args.producer_provider.clone(),
        producer: args.producer.clone(),
        external_task_id: args.external_task_id.clone(),
        ..AttemptFilter::default()
    }
}

fn print_recorded_attempt(attempt: &ProofAttempt) {
    println!(
        "Recorded external patch attempt: {} {} goal={} producer={} external_task_id={}",
        attempt.attempt_id,
        attempt.status.kind(),
        attempt.goal_hash,
        attempt
            .producer
            .as_ref()
            .map(|producer| producer.name.as_str())
            .unwrap_or("none"),
        attempt
            .context
            .as_ref()
            .and_then(|context| context.external_task_id.as_deref())
            .unwrap_or("none")
    );
}

fn print_gate_report(report: &AttemptGateReport) {
    println!("Authority-gate evidence: {} attempts", report.total);
    print_counts(
        "authority_gate",
        &report.summary.by_authority_gate,
        report.summary.without_authority_gate,
    );
    print_counts(
        "failure_mode",
        &report.summary.by_failure_mode,
        report.summary.without_failure_mode,
    );
    print_counts("status", &report.summary.by_status, 0);
    print_counts(
        "trust_level",
        &report.summary.by_trust_level,
        report.summary.without_trust_level,
    );
    print_counts(
        "producer_kind",
        &report.summary.by_producer_kind,
        report.summary.without_producer,
    );
    print_counts(
        "producer",
        &report.summary.by_producer,
        report.summary.without_producer,
    );
    print_counts(
        "producer_provider",
        &report.summary.by_producer_provider,
        report.summary.without_producer,
    );
    print_counts(
        "external_task_id",
        &report.summary.by_external_task_id,
        report.summary.without_external_task_id,
    );
}

fn print_replay_binding_report(report: &AttemptReplayBindingReport) {
    println!(
        "Replay bindings: {:?}, {} accepted scanned, {} entries validated, {} valid, {} missing, {} stale",
        report.scope,
        report.total_accepted,
        report.validated_entries,
        report.valid,
        report.missing,
        report.stale
    );
    for entry in &report.entries {
        println!(
            "  {} {:?} goal={} gate={}",
            display_option(entry.attempt_id.as_deref()),
            entry.status,
            display_option(entry.goal_hash.as_deref()),
            display_option(entry.authority_gate.as_deref())
        );
        for diagnostic in &entry.diagnostics {
            println!("    {diagnostic}");
        }
    }
}

fn print_counts(label: &str, counts: &BTreeMap<String, usize>, missing: usize) {
    println!("{label}:");
    if counts.is_empty() && missing == 0 {
        println!("  none: 0");
        return;
    }
    for (value, count) in counts {
        println!("  {value}: {count}");
    }
    if missing > 0 {
        println!("  none: {missing}");
    }
}

fn print_human_report(report: &AttemptQueryReport) {
    println!(
        "Attempts: returned {} of {} matching",
        report.returned, report.total
    );
    for attempt in &report.attempts {
        println!(
            "  {} {} goal={} gate={} failure={} trust={} producer_kind={} producer_provider={} producer={} external_task_id={}",
            attempt.attempt_id,
            attempt.status.kind(),
            attempt.goal_hash,
            display_option(attempt.authority_gate.as_deref()),
            display_option(attempt.failure_mode.as_deref()),
            attempt
                .trust_level
                .map(display_trust_level)
                .unwrap_or("none"),
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.producer_kind.as_str())
                .unwrap_or("none"),
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.provider.as_str())
                .unwrap_or("none"),
            attempt
                .producer
                .as_ref()
                .map(|producer| producer.name.as_str())
                .unwrap_or("none"),
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref())
                .unwrap_or("none")
        );
    }
}

fn display_option(value: Option<&str>) -> &str {
    value.unwrap_or("none")
}

fn display_trust_level(level: TrustLevel) -> &'static str {
    match level {
        TrustLevel::KernelVerified => "KernelVerified",
        TrustLevel::AxiomDependent => "AxiomDependent",
        TrustLevel::CertificateReplayed => "CertificateReplayed",
        TrustLevel::PartiallyAxiomatized => "PartiallyAxiomatized",
        TrustLevel::TrustedOracle => "TrustedOracle",
        _ => "Unknown",
    }
}

fn parse_attempt_status(value: &str) -> Result<AttemptStatusFilter, String> {
    AttemptStatusFilter::from_str(value).map_err(|err| err.to_string())
}

fn parse_producer_kind(value: &str) -> Result<ProducerKind, String> {
    let normalized = value
        .trim()
        .chars()
        .filter(|ch| !matches!(ch, '_' | '-' | ' '))
        .flat_map(char::to_lowercase)
        .collect::<String>();

    match normalized.as_str() {
        "model" => Ok(ProducerKind::Model),
        "solver" => Ok(ProducerKind::Solver),
        "tactic" => Ok(ProducerKind::Tactic),
        "human" => Ok(ProducerKind::Human),
        "service" => Ok(ProducerKind::Service),
        "other" => Ok(ProducerKind::Other),
        "" => Err("producer kind filter must not be empty".to_owned()),
        other => Err(format!(
            "unknown producer kind `{other}`; expected model, solver, tactic, human, service, or other"
        )),
    }
}

fn parse_trust_level(value: &str) -> Result<TrustLevel, String> {
    let normalized = value
        .trim()
        .chars()
        .filter(|ch| !matches!(ch, '_' | '-' | ' '))
        .flat_map(char::to_lowercase)
        .collect::<String>();

    match normalized.as_str() {
        "kernelverified" => Ok(TrustLevel::KernelVerified),
        "axiomdependent" => Ok(TrustLevel::AxiomDependent),
        "certificatereplayed" => Ok(TrustLevel::CertificateReplayed),
        "partiallyaxiomatized" => Ok(TrustLevel::PartiallyAxiomatized),
        "trustedoracle" => Ok(TrustLevel::TrustedOracle),
        "" => Err("trust level filter must not be empty".to_owned()),
        other => Err(format!(
            "unknown trust level `{other}`; expected KernelVerified, AxiomDependent, CertificateReplayed, PartiallyAxiomatized, or TrustedOracle"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;
    use std::process::Command;

    use clean_mathverse::attempt_log::{
        append_to, put_artifact, read_artifact, AttemptContext, AttemptProducer, AttemptStatus,
        ProofAttempt,
    };
    use clean_mathverse::env_fingerprint::EnvFingerprint;

    const TEST_PATCH_BYTES: &[u8] = b"diff --git a/Foo.lean b/Foo.lean\n";

    fn attempt(root: &Path, goal_hash: &str, status: AttemptStatus) -> ProofAttempt {
        ProofAttempt::new(
            goal_hash.to_owned(),
            status,
            "test-audit-hash".to_owned(),
            EnvFingerprint::capture(root).expect("capture test env"),
        )
    }

    fn git_init(root: &Path) {
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .arg("init")
            .output()
            .expect("run git init");
        assert!(
            output.status.success(),
            "git init failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn accepted_authority_hashes(root: &Path) -> (String, String, String) {
        let trust_audit = record_test_authority_gate_attempt(
            root,
            "trust_audit",
            b"{\"gate\":\"trust_audit\",\"accepted\":true}",
            "external_patch/test_trust_audit",
            "trust-audit.json",
        );
        let statement_preservation = record_test_authority_gate_attempt(
            root,
            "statement_preservation",
            b"{\"gate\":\"statement_preservation\",\"accepted\":true}",
            "external_patch/test_statement_preservation",
            "statement-preservation.json",
        );
        let false_controls = record_test_authority_gate_attempt(
            root,
            "false_controls",
            b"{\"gate\":\"false_controls\",\"accepted\":true}",
            "external_patch/test_false_controls",
            "false-controls.json",
        );
        (
            trust_audit.trust_audit_hash,
            statement_preservation.trust_audit_hash,
            false_controls.trust_audit_hash,
        )
    }

    fn record_test_authority_gate_attempt(
        root: &Path,
        gate: &str,
        bytes: &[u8],
        kind: &str,
        logical_name: &str,
    ) -> ProofAttempt {
        let artifact = put_artifact(root, bytes, Some(kind), Some(logical_name))
            .expect("put authority gate artifact");
        let patch_artifact = put_artifact(
            root,
            TEST_PATCH_BYTES,
            Some("external_patch/patch"),
            Some("candidate.patch"),
        )
        .expect("put patch anchor artifact");
        let mut attempt = ProofAttempt::new(
            "goal-a".to_owned(),
            AttemptStatus::Accepted,
            artifact.blake3.clone(),
            EnvFingerprint::capture(root).expect("capture test env"),
        );
        attempt.solver_artifact = Some(artifact);
        attempt.authority_gate = Some(gate.to_owned());
        attempt.trust_level = Some(TrustLevel::KernelVerified);
        attempt.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "clean-ci".to_owned(),
            name: "native-replay".to_owned(),
            version: None,
            command_digest: Some(
                blake3::hash(format!("{gate}-command").as_bytes())
                    .to_hex()
                    .to_string(),
            ),
        });
        attempt.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            prompt_digest: Some(blake3::hash(b"prove Foo.bar").to_hex().to_string()),
            patch_artifact: Some(patch_artifact),
            ..AttemptContext::default()
        });
        append_to(root, &attempt).expect("record authority gate attempt");
        attempt
    }

    fn write_attempt_value(root: &Path, file_name: &str, value: serde_json::Value) {
        let dir = root.join(".mathverse").join("attempts");
        std::fs::create_dir_all(&dir).expect("create attempts dir");
        std::fs::write(
            dir.join(file_name),
            format!(
                "{}\n",
                serde_json::to_string(&value).expect("serialize attempt")
            ),
        )
        .expect("write attempt log");
    }

    #[test]
    fn list_query_applies_filters_and_limit() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let mut rejected = attempt(
            root,
            "goal-a",
            AttemptStatus::Rejected {
                reason: "trust audit failed".to_owned(),
            },
        );
        rejected.authority_gate = Some("trust_audit".to_owned());
        rejected.failure_mode = Some("trust_audit_rejected".to_owned());
        rejected.trust_level = Some(TrustLevel::TrustedOracle);
        rejected.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Model,
            provider: "provider-a".to_owned(),
            name: "producer-a".to_owned(),
            version: Some("v1".to_owned()),
            command_digest: Some("command-digest-a".to_owned()),
        });
        rejected.context = Some(AttemptContext {
            external_run_id: Some("run-a".to_owned()),
            external_task_id: Some("task-a".to_owned()),
            prompt_digest: Some("prompt-digest-a".to_owned()),
            patch_artifact: None,
        });
        append_to(root, &rejected).expect("append rejected attempt");

        let mut accepted = attempt(root, "goal-b", AttemptStatus::Accepted);
        accepted.authority_gate = Some("statement_preservation".to_owned());
        accepted.trust_level = Some(TrustLevel::KernelVerified);
        accepted.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "provider-b".to_owned(),
            name: "producer-b".to_owned(),
            version: None,
            command_digest: None,
        });
        accepted.context = Some(AttemptContext {
            external_run_id: Some("run-b".to_owned()),
            external_task_id: Some("task-b".to_owned()),
            prompt_digest: None,
            patch_artifact: None,
        });
        append_to(root, &accepted).expect("append accepted attempt");

        let args = AttemptListArgs {
            root: root.to_owned(),
            goal_hash: Some("goal-a".to_owned()),
            status: Some(AttemptStatusFilter::Rejected),
            authority_gate: Some("trust_audit".to_owned()),
            failure_mode: Some("trust_audit_rejected".to_owned()),
            trust_level: Some(TrustLevel::TrustedOracle),
            producer_kind: Some(ProducerKind::Model),
            producer_provider: Some("provider-a".to_owned()),
            producer: Some("producer-a".to_owned()),
            external_task_id: Some("task-a".to_owned()),
            limit: Some(1),
            json: true,
        };

        let report = query_attempts_for_list(&args).expect("query attempts");

        assert_eq!(report.total, 1);
        assert_eq!(report.returned, 1);
        assert_eq!(report.attempts[0].attempt_id, rejected.attempt_id);
        assert_eq!(report.filter.goal_hash.as_deref(), Some("goal-a"));
        assert_eq!(report.filter.status, Some(AttemptStatusFilter::Rejected));
        assert_eq!(report.filter.trust_level, Some(TrustLevel::TrustedOracle));
        assert_eq!(report.filter.producer_kind, Some(ProducerKind::Model));
        assert_eq!(
            report.filter.producer_provider.as_deref(),
            Some("provider-a")
        );
        assert_eq!(report.filter.producer.as_deref(), Some("producer-a"));
        assert_eq!(report.filter.external_task_id.as_deref(), Some("task-a"));
    }

    #[test]
    fn gate_query_summarizes_attempt_metadata() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let mut rejected = attempt(
            root,
            "goal-a",
            AttemptStatus::Rejected {
                reason: "trust audit failed".to_owned(),
            },
        );
        rejected.authority_gate = Some("trust_audit".to_owned());
        rejected.failure_mode = Some("trust_audit_rejected".to_owned());
        rejected.trust_level = Some(TrustLevel::TrustedOracle);
        rejected.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Model,
            provider: "provider-a".to_owned(),
            name: "producer-a".to_owned(),
            version: None,
            command_digest: None,
        });
        rejected.context = Some(AttemptContext {
            external_run_id: Some("run-a".to_owned()),
            external_task_id: Some("task-a".to_owned()),
            prompt_digest: None,
            patch_artifact: None,
        });
        append_to(root, &rejected).expect("append rejected attempt");

        let mut timed_out = attempt(root, "goal-b", AttemptStatus::Timeout { after_ms: 5000 });
        timed_out.authority_gate = Some("trust_audit".to_owned());
        timed_out.failure_mode = Some("gate_timeout".to_owned());
        timed_out.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Model,
            provider: "provider-a".to_owned(),
            name: "producer-a".to_owned(),
            version: None,
            command_digest: None,
        });
        timed_out.context = Some(AttemptContext {
            external_run_id: Some("run-b".to_owned()),
            external_task_id: Some("task-b".to_owned()),
            prompt_digest: None,
            patch_artifact: None,
        });
        append_to(root, &timed_out).expect("append timeout attempt");

        let accepted = attempt(root, "goal-c", AttemptStatus::Accepted);
        append_to(root, &accepted).expect("append accepted attempt");

        let args = AttemptGateArgs {
            root: root.to_owned(),
            json: false,
        };

        let report = query_attempt_gates(&args).expect("query gate report");

        assert_eq!(report.total, 3);
        assert_eq!(report.summary.by_authority_gate["trust_audit"], 2);
        assert_eq!(report.summary.without_authority_gate, 1);
        assert_eq!(report.summary.by_failure_mode["trust_audit_rejected"], 1);
        assert_eq!(report.summary.by_failure_mode["gate_timeout"], 1);
        assert_eq!(report.summary.without_failure_mode, 1);
        assert_eq!(report.summary.by_status["accepted"], 1);
        assert_eq!(report.summary.by_status["rejected"], 1);
        assert_eq!(report.summary.by_status["timeout"], 1);
        assert_eq!(report.summary.by_trust_level["TrustedOracle"], 1);
        assert_eq!(report.summary.without_trust_level, 2);
        assert_eq!(report.summary.by_producer_kind["model"], 2);
        assert_eq!(report.summary.by_producer["producer-a"], 2);
        assert_eq!(report.summary.by_producer_provider["provider-a"], 2);
        assert_eq!(report.summary.without_producer, 1);
        assert_eq!(report.summary.by_external_task_id["task-a"], 1);
        assert_eq!(report.summary.by_external_task_id["task-b"], 1);
        assert_eq!(report.summary.without_external_task_id, 1);
    }

    #[test]
    fn evidence_query_filters_support_records_and_selects_newest() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let artifact = put_artifact(
            root,
            b"solver evidence",
            Some("test/solver"),
            Some("solver.json"),
        )
        .expect("put solver artifact");

        let mut older = attempt(root, "goal-a", AttemptStatus::Accepted);
        older.authority_gate = Some("trust_audit".to_owned());
        older.solver_artifact = Some(artifact.clone());
        older.created_at = 10;
        older.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            ..AttemptContext::default()
        });
        let mut older_value = serde_json::to_value(older).expect("older attempt json");
        older_value["theorem_name"] = serde_json::Value::String("Math.Target".to_owned());
        write_attempt_value(root, "older.jsonl", older_value);

        let mut newest = attempt(root, "goal-a", AttemptStatus::Accepted);
        newest.authority_gate = Some("trust_audit".to_owned());
        newest.solver_artifact = Some(artifact.clone());
        newest.created_at = 20;
        newest.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            ..AttemptContext::default()
        });
        let newest_id = newest.attempt_id.to_string();
        let mut newest_value = serde_json::to_value(newest).expect("newest attempt json");
        newest_value["theorem_name"] = serde_json::Value::String("Math.Target".to_owned());
        write_attempt_value(root, "newest.jsonl", newest_value);

        let mut other_goal = attempt(root, "goal-b", AttemptStatus::Accepted);
        other_goal.authority_gate = Some("trust_audit".to_owned());
        other_goal.solver_artifact = Some(artifact.clone());
        other_goal.created_at = 30;
        other_goal.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            ..AttemptContext::default()
        });
        let mut other_value = serde_json::to_value(other_goal).expect("other attempt json");
        other_value["theorem_name"] = serde_json::Value::String("Math.Target".to_owned());
        write_attempt_value(root, "other.jsonl", other_value);

        let args = AttemptQueryEvidenceArgs {
            root: root.to_owned(),
            authority_gate: Some("trust_audit".to_owned()),
            theorem_name: Some("Math.Target".to_owned()),
            task_id: Some("task-a".to_owned()),
            goal_hash: Some("goal-a".to_owned()),
            artifact_hash: Some(artifact.blake3.clone()),
            json: true,
        };

        let report = query_attempt_evidence(&args).expect("query evidence");

        assert_eq!(report.status, AttemptEvidenceQueryStatus::Found);
        assert_eq!(report.matching_count, 2);
        assert_eq!(
            report
                .selected_attempt
                .as_ref()
                .map(|attempt| attempt.attempt_id.as_str()),
            Some(newest_id.as_str())
        );
        assert_eq!(report.artifacts.len(), 1);
        assert_eq!(report.artifacts[0].role, "solver_artifact");
        assert_eq!(report.artifacts[0].blake3, artifact.blake3);
        assert!(report
            .notes
            .iter()
            .any(|note| note.contains("selected newest")));
        assert_eq!(
            report
                .support
                .as_ref()
                .and_then(|support| support.theorem_name.as_deref()),
            Some("Math.Target")
        );
    }

    #[test]
    fn refresh_plan_query_reports_current_stale_and_missing_gates() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let mut current = attempt(root, "goal-a", AttemptStatus::Accepted);
        current.authority_gate = Some("trust_audit".to_owned());
        current.created_at = 10;
        current.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            ..AttemptContext::default()
        });
        let mut current_value = serde_json::to_value(current).expect("current attempt json");
        current_value["theorem_name"] = serde_json::Value::String("Math.Target".to_owned());
        write_attempt_value(root, "current.jsonl", current_value);

        let mut stale = ProofAttempt::new(
            "goal-b".to_owned(),
            AttemptStatus::Accepted,
            "test-audit-hash".to_owned(),
            EnvFingerprint::from_host_toolchain("old-toolchain", "old-clean"),
        );
        stale.authority_gate = Some("trust_ledger".to_owned());
        stale.created_at = 20;
        stale.context = Some(AttemptContext {
            external_task_id: Some("task-a".to_owned()),
            ..AttemptContext::default()
        });
        let mut stale_value = serde_json::to_value(stale).expect("stale attempt json");
        stale_value["theorem_name"] = serde_json::Value::String("Math.Target".to_owned());
        write_attempt_value(root, "stale.jsonl", stale_value);

        let args = AttemptRefreshPlanArgs {
            root: root.to_owned(),
            gates: vec![
                "trust_audit".to_owned(),
                "trust_ledger".to_owned(),
                "false_controls".to_owned(),
            ],
            theorem_name: Some("Math.Target".to_owned()),
            task_id: Some("task-a".to_owned()),
        };

        let plan = query_attempt_refresh_plan(&args).expect("refresh plan");

        assert_eq!(
            plan.gates
                .iter()
                .map(|gate| (gate.gate.as_str(), gate.status))
                .collect::<Vec<_>>(),
            vec![
                (
                    "trust_audit",
                    clean_mathverse::evidence_refresh::RefreshGateStatus::Current
                ),
                (
                    "trust_ledger",
                    clean_mathverse::evidence_refresh::RefreshGateStatus::Stale
                ),
                (
                    "false_controls",
                    clean_mathverse::evidence_refresh::RefreshGateStatus::Missing
                ),
            ]
        );
        assert!(plan.gates[0].current.is_some());
        assert_eq!(plan.gates[1].stale.len(), 1);
        assert_eq!(
            plan.gates[1].stale[0].reasons,
            vec![clean_mathverse::evidence_refresh::RefreshStaleReason::EnvMismatch]
        );
        assert!(plan.gates[2].records.is_empty());
    }

    #[test]
    fn replay_binding_query_reports_valid_stale_and_missing_accepted_evidence() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let current_artifact = put_artifact(
            root,
            b"checked current proof",
            Some("solver/lrat"),
            Some("current.lrat"),
        )
        .expect("put current artifact");
        let mut current = attempt(
            root,
            blake3::hash(b"current-goal").to_hex().as_ref(),
            AttemptStatus::Accepted,
        );
        current.trust_audit_hash = blake3::hash(b"current-audit").to_hex().to_string();
        current.solver_artifact = Some(current_artifact);
        current.authority_gate = Some("trust_audit".to_owned());
        current.trust_level = Some(TrustLevel::KernelVerified);
        current.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "clean-ci".to_owned(),
            name: "native-replay".to_owned(),
            version: None,
            command_digest: Some(blake3::hash(b"current-command").to_hex().to_string()),
        });
        append_to(root, &current).expect("append current attempt");

        let stale_artifact = put_artifact(
            root,
            b"checked stale proof",
            Some("solver/lrat"),
            Some("stale.lrat"),
        )
        .expect("put stale artifact");
        let mut stale = ProofAttempt::new(
            blake3::hash(b"stale-goal").to_hex().to_string(),
            AttemptStatus::Accepted,
            blake3::hash(b"stale-audit").to_hex().to_string(),
            EnvFingerprint::from_host_toolchain("old-toolchain", "old-clean"),
        );
        stale.solver_artifact = Some(stale_artifact);
        stale.authority_gate = Some("trust_audit".to_owned());
        stale.trust_level = Some(TrustLevel::KernelVerified);
        stale.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "clean-ci".to_owned(),
            name: "native-replay".to_owned(),
            version: None,
            command_digest: Some(blake3::hash(b"stale-command").to_hex().to_string()),
        });
        append_to(root, &stale).expect("append stale attempt");

        let mut missing = attempt(
            root,
            blake3::hash(b"missing-goal").to_hex().as_ref(),
            AttemptStatus::Accepted,
        );
        missing.trust_audit_hash = blake3::hash(b"missing-audit").to_hex().to_string();
        missing.authority_gate = Some("trust_audit".to_owned());
        append_to(root, &missing).expect("append missing attempt");

        let args = AttemptValidateReplayBindingsArgs {
            root: root.to_owned(),
            authority_gate: Some("trust_audit".to_owned()),
            latest_per_gate: false,
            gates: Vec::new(),
            no_policy_metadata: false,
            json: true,
        };
        let report = query_attempt_replay_bindings(&args).expect("validate replay bindings");

        assert_eq!(report.total_accepted, 3);
        assert_eq!(report.validated_entries, 3);
        assert_eq!(report.scope, AttemptReplayBindingScope::AllAccepted);
        assert_eq!(report.valid, 1);
        assert_eq!(report.stale, 1);
        assert_eq!(report.missing, 1);
        assert!(!report.is_valid());
        assert!(report.entries.iter().any(|entry| {
            entry.status == AttemptReplayBindingStatus::Missing
                && entry
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains("command digest"))
        }));
        assert!(report.entries.iter().any(|entry| {
            entry.status == AttemptReplayBindingStatus::Stale
                && entry
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.contains("environment"))
        }));
        let err = validate_replay_bindings(args)
            .expect_err("invalid accepted replay bindings should fail command");
        assert!(err
            .to_string()
            .contains("accepted replay-binding evidence is invalid"));
    }

    #[test]
    fn replay_binding_latest_per_gate_ignores_superseded_legacy_records() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();

        let mut legacy_missing = attempt(
            root,
            blake3::hash(b"legacy-goal").to_hex().as_ref(),
            AttemptStatus::Accepted,
        );
        legacy_missing.created_at = 10;
        legacy_missing.authority_gate = Some("trust_audit".to_owned());
        legacy_missing.trust_level = Some(TrustLevel::KernelVerified);
        append_to(root, &legacy_missing).expect("append legacy missing attempt");

        let trust_artifact = put_artifact(
            root,
            b"checked current trust audit",
            Some("solver/lrat"),
            Some("current-trust-audit.lrat"),
        )
        .expect("put trust artifact");
        let mut current_trust = attempt(
            root,
            blake3::hash(b"current-trust-goal").to_hex().as_ref(),
            AttemptStatus::Accepted,
        );
        current_trust.created_at = 20;
        current_trust.trust_audit_hash = blake3::hash(b"current-trust-audit").to_hex().to_string();
        current_trust.solver_artifact = Some(trust_artifact);
        current_trust.authority_gate = Some("trust_audit".to_owned());
        current_trust.trust_level = Some(TrustLevel::KernelVerified);
        current_trust.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "clean-ci".to_owned(),
            name: "native-replay".to_owned(),
            version: None,
            command_digest: Some(blake3::hash(b"current-trust-command").to_hex().to_string()),
        });
        append_to(root, &current_trust).expect("append current trust attempt");

        let false_artifact = put_artifact(
            root,
            b"checked current false controls",
            Some("solver/lrat"),
            Some("current-false-controls.lrat"),
        )
        .expect("put false-control artifact");
        let mut current_false = attempt(
            root,
            blake3::hash(b"current-false-goal").to_hex().as_ref(),
            AttemptStatus::Accepted,
        );
        current_false.created_at = 30;
        current_false.trust_audit_hash = blake3::hash(b"current-false-audit").to_hex().to_string();
        current_false.solver_artifact = Some(false_artifact);
        current_false.authority_gate = Some("false_controls".to_owned());
        current_false.trust_level = Some(TrustLevel::KernelVerified);
        current_false.producer = Some(AttemptProducer {
            producer_kind: ProducerKind::Solver,
            provider: "clean-ci".to_owned(),
            name: "native-replay".to_owned(),
            version: None,
            command_digest: Some(blake3::hash(b"current-false-command").to_hex().to_string()),
        });
        append_to(root, &current_false).expect("append current false-controls attempt");

        let all_history_args = AttemptValidateReplayBindingsArgs {
            root: root.to_owned(),
            authority_gate: Some("trust_audit".to_owned()),
            latest_per_gate: false,
            gates: Vec::new(),
            no_policy_metadata: false,
            json: true,
        };
        let all_history =
            query_attempt_replay_bindings(&all_history_args).expect("all-history replay bindings");
        assert_eq!(all_history.scope, AttemptReplayBindingScope::AllAccepted);
        assert_eq!(all_history.total_accepted, 2);
        assert_eq!(all_history.validated_entries, 2);
        assert_eq!(all_history.valid, 1);
        assert_eq!(all_history.missing, 1);
        assert!(!all_history.is_valid());

        let latest_args = AttemptValidateReplayBindingsArgs {
            root: root.to_owned(),
            authority_gate: None,
            latest_per_gate: true,
            gates: vec![
                "trust_audit".to_owned(),
                "false_controls".to_owned(),
                "trust_ledger".to_owned(),
            ],
            no_policy_metadata: false,
            json: true,
        };
        let latest = query_attempt_replay_bindings(&latest_args).expect("latest replay bindings");
        assert_eq!(latest.scope, AttemptReplayBindingScope::LatestPerGate);
        assert_eq!(latest.total_accepted, 3);
        assert_eq!(latest.validated_entries, 3);
        assert_eq!(latest.valid, 2);
        assert_eq!(latest.missing, 1);
        assert_eq!(latest.stale, 0);
        assert!(latest.entries.iter().any(|entry| {
            entry.status == AttemptReplayBindingStatus::Missing
                && entry.authority_gate.as_deref() == Some("trust_ledger")
        }));

        let latest_current_args = AttemptValidateReplayBindingsArgs {
            root: root.to_owned(),
            authority_gate: None,
            latest_per_gate: true,
            gates: vec!["trust_audit,false_controls".to_owned()],
            no_policy_metadata: false,
            json: true,
        };
        let latest_current = query_attempt_replay_bindings(&latest_current_args)
            .expect("current latest replay bindings");
        assert!(latest_current.is_valid());
        assert_eq!(latest_current.valid, 2);
        assert_eq!(
            latest_current.required_gates,
            vec!["trust_audit", "false_controls"]
        );

        validate_replay_bindings(latest_current_args)
            .expect("current latest gate validation should pass");
        let err = validate_replay_bindings(latest_args)
            .expect_err("missing latest gate should fail command");
        assert!(err
            .to_string()
            .contains("accepted replay-binding evidence is invalid"));
    }

    #[test]
    fn record_external_patch_records_accepted_attempt_with_artifacts() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let patch_path = root.join("candidate.patch");
        let prompt_path = root.join("prompt.txt");
        let model_response_path = root.join("response.json");
        std::fs::write(&patch_path, b"diff --git a/Foo.lean b/Foo.lean\n").expect("write patch");
        std::fs::write(&prompt_path, b"prove Foo.bar").expect("write prompt");
        std::fs::write(&model_response_path, br#"{"patch":"..."}"#).expect("write model response");
        let (trust_audit_hash, statement_preservation_hash, false_controls_hash) =
            accepted_authority_hashes(root);
        let trust_ledger = record_test_authority_gate_attempt(
            root,
            "trust_ledger",
            b"{\"gate\":\"trust_ledger\",\"accepted\":true}",
            "external_patch/test_trust_ledger",
            "trust-ledger.json",
        );

        let args = AttemptRecordExternalPatchArgs {
            root: root.to_owned(),
            goal_hash: "goal-a".to_owned(),
            status: AttemptStatusFilter::Accepted,
            trust_audit_hash,
            statement_preservation_hash: Some(statement_preservation_hash),
            false_controls_hash: Some(false_controls_hash),
            trust_ledger_hash: Some(trust_ledger.trust_audit_hash),
            patch: Some(patch_path),
            prompt: Some(prompt_path),
            model_response: Some(model_response_path),
            producer_kind: ProducerKind::Model,
            producer_provider: "provider-a".to_owned(),
            producer: "producer-a".to_owned(),
            external_run_id: Some("run-a".to_owned()),
            external_task_id: Some("task-a".to_owned()),
            failure_mode: None,
            wall_time_ms: 123,
            allow_dirty: false,
            dirty_reason: None,
            json: true,
        };

        let attempt = record_external_patch_for_args(&args).expect("record external patch");

        assert!(matches!(attempt.status, AttemptStatus::Accepted));
        assert_eq!(attempt.goal_hash, "goal-a");
        assert_eq!(attempt.trust_audit_hash.len(), 64);
        assert_eq!(attempt.wall_time_ms, 123);
        assert_eq!(
            attempt.producer.as_ref().map(|producer| (
                producer.producer_kind,
                producer.provider.as_str(),
                producer.name.as_str()
            )),
            Some((ProducerKind::Model, "provider-a", "producer-a"))
        );
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_run_id.as_deref()),
            Some("run-a")
        );
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.external_task_id.as_deref()),
            Some("task-a")
        );
        let expected_prompt_digest = blake3::hash(b"prove Foo.bar").to_hex().to_string();
        assert_eq!(
            attempt
                .context
                .as_ref()
                .and_then(|context| context.prompt_digest.as_deref()),
            Some(expected_prompt_digest.as_str())
        );

        let patch = attempt
            .context
            .as_ref()
            .and_then(|context| context.patch_artifact.as_ref())
            .expect("patch artifact");
        assert_eq!(
            read_artifact(root, patch).expect("read patch"),
            b"diff --git a/Foo.lean b/Foo.lean\n"
        );
        assert!(attempt.model_response.is_some());

        let json: serde_json::Value = serde_json::from_str(
            &recorded_external_patch_json(&attempt).expect("recorded attempt json"),
        )
        .expect("parse recorded attempt json");
        let receipt = &json["authority_receipt"];
        assert_eq!(receipt["authority_gate"], "external_patch");
        assert_eq!(receipt["status"], "accepted");
        assert_eq!(receipt["trust_audit_hash"], attempt.trust_audit_hash);
        assert_eq!(receipt["solver_artifact"]["blake3"], patch.blake3.as_str());
        assert_eq!(receipt["solver_artifact"]["byte_len"], patch.byte_len);
        assert_eq!(receipt["solver_artifact"]["kind"], "external_patch/patch");
        assert_eq!(
            receipt["solver_artifact"]["logical_name"],
            "candidate.patch"
        );
        let context_artifact = attempt.model_response.as_ref().expect("context artifact");
        let context_json: serde_json::Value =
            serde_json::from_slice(&read_artifact(root, context_artifact).expect("read context"))
                .expect("context json");
        assert_eq!(
            context_json["authority_gate_attempts"]["trust_ledger"]["authority_gate"],
            "trust_ledger"
        );
        assert_eq!(
            context_json["authority_gate_attempts"]["trust_ledger"]["status"],
            "accepted"
        );

        let report = query_attempts_limited(
            root,
            AttemptFilter {
                external_task_id: Some("task-a".to_owned()),
                producer: Some("producer-a".to_owned()),
                ..AttemptFilter::default()
            },
            None,
        )
        .expect("query attempts");
        assert_eq!(report.total, 1);
        assert_eq!(report.attempts[0].attempt_id, attempt.attempt_id);
    }

    #[test]
    fn record_external_patch_rejects_accepted_without_patch() {
        let temp = tempfile::tempdir().expect("tempdir");
        let args = AttemptRecordExternalPatchArgs {
            root: temp.path().to_owned(),
            goal_hash: "goal-a".to_owned(),
            status: AttemptStatusFilter::Accepted,
            trust_audit_hash: "audit-a".to_owned(),
            statement_preservation_hash: None,
            false_controls_hash: None,
            trust_ledger_hash: None,
            patch: None,
            prompt: None,
            model_response: None,
            producer_kind: ProducerKind::Model,
            producer_provider: "provider-a".to_owned(),
            producer: "producer-a".to_owned(),
            external_run_id: None,
            external_task_id: None,
            failure_mode: None,
            wall_time_ms: 0,
            allow_dirty: false,
            dirty_reason: None,
            json: false,
        };

        let err =
            record_external_patch_for_args(&args).expect_err("accepted without patch must fail");
        assert!(err
            .to_string()
            .contains("accepted external patch attempt requires --patch"));
    }

    #[test]
    fn record_external_patch_rejects_accepted_without_prompt_or_response() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let patch_path = root.join("candidate.patch");
        std::fs::write(&patch_path, b"diff --git a/Foo.lean b/Foo.lean\n").expect("write patch");
        let (trust_audit_hash, statement_preservation_hash, false_controls_hash) =
            accepted_authority_hashes(root);
        let args = AttemptRecordExternalPatchArgs {
            root: root.to_owned(),
            goal_hash: "goal-a".to_owned(),
            status: AttemptStatusFilter::Accepted,
            trust_audit_hash,
            statement_preservation_hash: Some(statement_preservation_hash),
            false_controls_hash: Some(false_controls_hash),
            trust_ledger_hash: None,
            patch: Some(patch_path),
            prompt: None,
            model_response: None,
            producer_kind: ProducerKind::Model,
            producer_provider: "provider-a".to_owned(),
            producer: "producer-a".to_owned(),
            external_run_id: None,
            external_task_id: None,
            failure_mode: None,
            wall_time_ms: 0,
            allow_dirty: false,
            dirty_reason: None,
            json: false,
        };

        let err = record_external_patch_for_args(&args)
            .expect_err("accepted without prompt/response evidence must fail");
        assert!(err
            .to_string()
            .contains("accepted external patch attempt requires --prompt or --model-response"));
    }

    #[test]
    fn record_external_patch_rejects_accepted_without_downstream_authority_hashes() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        let patch_path = root.join("candidate.patch");
        let prompt_path = root.join("prompt.txt");
        std::fs::write(&patch_path, b"diff --git a/Foo.lean b/Foo.lean\n").expect("write patch");
        std::fs::write(&prompt_path, b"prove Foo.bar").expect("write prompt");
        let (trust_audit_hash, _, _) = accepted_authority_hashes(root);
        let args = AttemptRecordExternalPatchArgs {
            root: root.to_owned(),
            goal_hash: "goal-a".to_owned(),
            status: AttemptStatusFilter::Accepted,
            trust_audit_hash,
            statement_preservation_hash: None,
            false_controls_hash: None,
            trust_ledger_hash: None,
            patch: Some(patch_path),
            prompt: Some(prompt_path),
            model_response: None,
            producer_kind: ProducerKind::Model,
            producer_provider: "provider-a".to_owned(),
            producer: "producer-a".to_owned(),
            external_run_id: None,
            external_task_id: None,
            failure_mode: None,
            wall_time_ms: 0,
            allow_dirty: false,
            dirty_reason: None,
            json: false,
        };

        let err = record_external_patch_for_args(&args)
            .expect_err("accepted without downstream authority evidence must fail");
        assert!(err
            .to_string()
            .contains("requires replayable statement_preservation evidence"));
    }

    #[test]
    fn record_external_patch_dirty_git_root_requires_explicit_reason() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path();
        git_init(root);
        let patch_path = root.join("candidate.patch");
        std::fs::write(&patch_path, b"diff --git a/Foo.lean b/Foo.lean\n").expect("write patch");
        let prompt_path = root.join("prompt.txt");
        std::fs::write(&prompt_path, b"prove Foo.bar").expect("write prompt");
        let (trust_audit_hash, statement_preservation_hash, false_controls_hash) =
            accepted_authority_hashes(root);
        let mut args = AttemptRecordExternalPatchArgs {
            root: root.to_owned(),
            goal_hash: "goal-a".to_owned(),
            status: AttemptStatusFilter::Accepted,
            trust_audit_hash,
            statement_preservation_hash: Some(statement_preservation_hash),
            false_controls_hash: Some(false_controls_hash),
            trust_ledger_hash: None,
            patch: Some(patch_path),
            prompt: Some(prompt_path),
            model_response: None,
            producer_kind: ProducerKind::Model,
            producer_provider: "provider-a".to_owned(),
            producer: "producer-a".to_owned(),
            external_run_id: None,
            external_task_id: None,
            failure_mode: None,
            wall_time_ms: 0,
            allow_dirty: false,
            dirty_reason: None,
            json: false,
        };

        let err = record_external_patch_for_args(&args)
            .expect_err("dirty accepted attempt must fail without override");
        assert!(err.to_string().contains("dirty git worktree"));

        args.allow_dirty = true;
        args.dirty_reason = Some("reviewed dirty fixture".to_owned());
        let attempt =
            record_external_patch_for_args(&args).expect("record dirty attempt with reason");
        let context = attempt.model_response.as_ref().expect("context artifact");
        let context_json: serde_json::Value =
            serde_json::from_slice(&read_artifact(root, context).expect("read context"))
                .expect("context json");

        assert_eq!(
            context_json["metadata"]["context"]["external_patch.dirty_root.policy"],
            "allowed"
        );
        assert_eq!(
            context_json["metadata"]["context"]["external_patch.dirty_root.reason"],
            "reviewed dirty fixture"
        );
    }

    #[test]
    fn parse_trust_level_accepts_cli_spellings() {
        assert_eq!(
            parse_trust_level("kernel-verified").expect("parse kernel trust"),
            TrustLevel::KernelVerified
        );
        assert_eq!(
            parse_trust_level("TrustedOracle").expect("parse oracle trust"),
            TrustLevel::TrustedOracle
        );
    }

    #[test]
    fn parse_producer_kind_accepts_cli_spellings() {
        assert_eq!(
            parse_producer_kind("model").expect("parse model producer kind"),
            ProducerKind::Model
        );
        assert_eq!(
            parse_producer_kind("service").expect("parse service producer kind"),
            ProducerKind::Service
        );
    }
}
