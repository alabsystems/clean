// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Statement-preservation drift snapshots and vocabulary.
//!
//! This is the report shape consumed by the statement-preservation authority
//! gate in [`crate::math_map::ingest`]: what kinds of declaration-surface drift
//! exist, and which of them block an untrusted patch from being accepted.
//!
//! The snapshot/diff engine in this module PRODUCES those reports. It compares
//! two kernel [`Environment`] values at the declaration surface available
//! today: constant names, declaration statement types, universe parameter
//! lists, Pi-hypothesis spines, and direct `Const` references inside each
//! statement. The kernel `Environment` does not expose Lake/module import
//! provenance, so [`DeclSnapshot::imports`] is intentionally a narrow adapter
//! over those direct statement references. If source-level import metadata
//! becomes available, the adapter should be replaced without changing the
//! public report shape.
//!
//! Full theorem subsumption is also intentionally conservative here. Without
//! retaining elaborator proof obligations or a source import graph, [`diff`]
//! classifies only common Pi-spine hypothesis drops/additions and otherwise
//! reports statement changes as [`StmtChangeKind::Incomparable`].

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};

use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::{BinderData, ConstantInfo, ConstantKind, Environment, Expr, ExprKind, Name};
use serde::{Deserialize, Serialize};

use crate::attempt_log::{
    put_artifact, record_authority_gate_attempt, ArtifactRef, AttemptStatus, AuthorityGateAttempt,
    ProofAttempt,
};
use crate::env_fingerprint::EnvFingerprint;
use crate::error::MathverseResult;
use crate::types::TrustLevel;

/// Stable authority-gate name for statement-preservation evidence.
pub const STATEMENT_PRESERVATION_AUTHORITY_GATE: &str = "statement_preservation";

/// Artifact kind for the persisted statement-preservation gate report.
pub const STATEMENT_PRESERVATION_REPORT_ARTIFACT_KIND: &str =
    "authority-gate/statement-preservation-report";

/// Logical filename for the persisted statement-preservation gate report.
pub const STATEMENT_PRESERVATION_REPORT_ARTIFACT_LOGICAL_NAME: &str =
    "statement-preservation-report.json";

/// Artifact kind for the replay/command evidence attached to an accepted gate.
const STATEMENT_PRESERVATION_COMMAND_EVIDENCE_ARTIFACT_KIND: &str =
    "authority-gate/statement-preservation-command-evidence";

/// Logical filename for the replay/command evidence attached to an accepted gate.
const STATEMENT_PRESERVATION_COMMAND_EVIDENCE_LOGICAL_NAME: &str =
    "statement-preservation-command-evidence.json";

/// BLAKE3 digest used for deterministic drift fingerprints.
pub type DriftHash = [u8; 32];

/// Errors while reading or writing drift snapshot JSON files.
#[derive(Debug, thiserror::Error)]
pub enum DriftSnapshotError {
    /// Filesystem failure.
    #[error("failed to {action} drift snapshot `{}`: {source}", path.display())]
    Io {
        /// What the snapshot layer was doing when the failure happened.
        action: &'static str,
        /// Path involved in the failure.
        path: PathBuf,
        /// Underlying I/O error.
        source: std::io::Error,
    },
    /// JSON encode/decode failure.
    #[error("failed to {action} drift snapshot JSON `{}`: {source}", path.display())]
    Json {
        /// What the snapshot layer was doing when the failure happened.
        action: &'static str,
        /// Path involved in the failure.
        path: PathBuf,
        /// Underlying `serde_json` error.
        source: serde_json::Error,
    },
    /// Snapshot file decoded, but failed structural validation.
    #[error("invalid drift snapshot `{}`: {message}", path.display())]
    Invalid {
        /// Path of the rejected snapshot file.
        path: PathBuf,
        /// Stable human-readable validation failure.
        message: String,
    },
}

/// A deterministic snapshot of the declaration surface in a kernel environment.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnvSnapshot {
    /// Declarations keyed by fully-qualified kernel name.
    pub declarations: BTreeMap<Name, DeclSnapshot>,
}

impl EnvSnapshot {
    /// Return the snapshot for a declaration name.
    #[must_use]
    pub fn get(&self, name: &Name) -> Option<&DeclSnapshot> {
        self.declarations.get(name)
    }

    /// Number of declarations captured in this snapshot.
    #[must_use]
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Whether this snapshot contains no declarations.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }

    /// Save this snapshot to a deterministic JSON file.
    pub fn save_json(&self, path: impl AsRef<Path>) -> Result<(), DriftSnapshotError> {
        save_snapshot_json(self, path)
    }

    /// Load a snapshot from a JSON file written by [`save_snapshot_json`].
    pub fn load_json(path: impl AsRef<Path>) -> Result<Self, DriftSnapshotError> {
        load_snapshot_json(path)
    }

    /// Return theorem statement hashes formatted for statement-preservation gate inputs.
    #[must_use]
    pub fn theorem_statement_hashes(&self) -> BTreeMap<String, String> {
        theorem_statement_hashes(self)
    }

    /// Return deterministic theorem comparison inputs for statement-preservation gates.
    #[must_use]
    pub fn theorem_statement_comparison_inputs(
        before: &Self,
        after: &Self,
    ) -> Vec<TheoremStatementComparisonInput> {
        theorem_statement_comparison_inputs(before, after)
    }
}

/// Snapshot of one kernel declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclSnapshot {
    /// Fully-qualified declaration name.
    pub name: Name,
    /// Kernel declaration kind.
    pub kind: ConstantKind,
    /// Hash of the full declared statement/type.
    pub statement_hash: DriftHash,
    /// Hash of the leading Pi-hypothesis list.
    pub hyp_list_hash: DriftHash,
    /// Leading Pi-hypothesis signature.
    pub hypotheses: Vec<HypothesisSig>,
    /// Hash of the body after stripping leading Pi hypotheses.
    pub conclusion_hash: DriftHash,
    /// Universe parameter signature.
    pub universe_sig: UniverseSig,
    /// Direct `Const`/projection names referenced by the statement.
    ///
    /// Fallback behavior: this is not a Lake import list. It is the only
    /// import-like dependency data currently exposed by `Environment`.
    pub imports: Vec<Name>,
    /// Hash of `imports`.
    pub imports_hash: DriftHash,
}

/// Deterministic theorem statement input for an authority-gate comparison.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TheoremStatementComparisonInput {
    /// Last theorem name component, useful for matching human-facing manifest target names.
    pub theorem: String,
    /// Fully namespace-qualified theorem name.
    pub qualified_name: String,
    /// Formatted statement hash before the patch, when the theorem existed before.
    pub before_statement_hash: Option<String>,
    /// Formatted statement hash after the patch, when the theorem exists after.
    pub after_statement_hash: Option<String>,
}

/// Signature for a leading Pi hypothesis.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HypothesisSig {
    /// Zero-based index in the leading Pi spine.
    pub index: usize,
    /// Binder metadata, including explicit/implicit/instance shape.
    pub binder: BinderData,
    /// Deterministic hash of the hypothesis domain type.
    pub type_hash: DriftHash,
}

/// Universe parameter signature for a declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct UniverseSig {
    /// Universe parameter names in declaration order.
    pub params: Vec<Name>,
    /// Deterministic hash of `params`.
    pub hash: DriftHash,
}

/// Fine-grained hypothesis drift for one declaration.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct HypDiff {
    /// Hypotheses before the change.
    pub before: Vec<HypothesisSig>,
    /// Hypotheses after the change.
    pub after: Vec<HypothesisSig>,
    /// Hypotheses present before but not after.
    pub removed: Vec<HypothesisSig>,
    /// Hypotheses present after but not before.
    pub added: Vec<HypothesisSig>,
}

impl HypDiff {
    /// Whether the hypothesis signature changed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.removed.is_empty() && self.added.is_empty()
    }
}

/// How a declaration's statement changed relative to its baseline.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StmtChangeKind {
    /// The after-statement dropped one or more leading Pi hypotheses while
    /// preserving the conclusion hash.
    Weaker,
    /// The after-statement added one or more leading Pi hypotheses while
    /// preserving the conclusion hash.
    Stronger,
    /// The snapshots changed, but no subsumption relationship is provable from
    /// the exposed declaration data. The authority gate treats this as blocking
    /// until a kernel-backed comparison proves the statement was preserved.
    Incomparable,
    /// Reserved for callers that pair dropped/added names as a rename.
    Renamed,
}

/// Stable failure-mode classification for a blocking statement-preservation report.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum StatementPreservationFailureMode {
    /// Declaration existed after but not before, so there is no preserved baseline.
    Missing,
    /// Declaration existed before but not after.
    Dropped,
    /// Statement changed through a paired rename report.
    Renamed,
    /// The after-statement dropped hypotheses.
    Weaker,
    /// The after-statement added hypotheses.
    Stronger,
    /// The statement changed without a proven subsumption relationship.
    Incomparable,
    /// Universe parameters changed.
    Universe,
    /// Leading hypotheses changed.
    Hypothesis,
    /// Direct statement-reference import proxy changed.
    Import,
}

impl StatementPreservationFailureMode {
    /// Stable lowercase attempt-log spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Missing => "statement_preservation_missing",
            Self::Dropped => "statement_preservation_dropped",
            Self::Renamed => "statement_preservation_renamed",
            Self::Weaker => "statement_preservation_weaker",
            Self::Stronger => "statement_preservation_stronger",
            Self::Incomparable => "statement_preservation_incomparable",
            Self::Universe => "statement_preservation_universe",
            Self::Hypothesis => "statement_preservation_hypothesis",
            Self::Import => "statement_preservation_import",
        }
    }
}

/// Statement preservation drift report.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DriftReport {
    /// Declaration name existed before but not after.
    NameDropped(Name),
    /// Declaration name exists after but not before.
    NameAdded(Name),
    /// Statement/type hash changed for a declaration present in both snapshots.
    StatementChanged {
        /// Declaration name.
        name: Name,
        /// Statement hash before the patch.
        before: DriftHash,
        /// Statement hash after the patch.
        after: DriftHash,
        /// How the statement changed.
        kind: StmtChangeKind,
    },
    /// Universe parameter signature changed.
    UniverseChanged {
        /// Declaration name.
        name: Name,
        /// Universe signature before the patch.
        before_sig: UniverseSig,
        /// Universe signature after the patch.
        after_sig: UniverseSig,
    },
    /// Direct statement-reference import proxy changed.
    ImportsChanged {
        /// Declaration name.
        name: Name,
        /// References added by the patch.
        added: Vec<Name>,
        /// References removed by the patch.
        removed: Vec<Name>,
    },
    /// Leading Pi-hypothesis signature changed.
    HypothesesChanged {
        /// Declaration name.
        name: Name,
        /// Hypothesis-level diff.
        diff: HypDiff,
    },
}

impl DriftReport {
    /// Whether this report should block a statement-preservation authority gate.
    ///
    /// Fail-closed by construction: every variant except a purely additive new
    /// name blocks. A new declaration cannot weaken an existing statement, so
    /// [`DriftReport::NameAdded`] is the single non-blocking case.
    #[must_use]
    pub fn is_authority_gate_blocking(&self) -> bool {
        self.statement_preservation_failure_mode().is_some()
    }

    /// Stable statement-preservation failure mode for blocking reports.
    #[must_use]
    pub fn statement_preservation_failure_mode(&self) -> Option<StatementPreservationFailureMode> {
        match self {
            Self::NameDropped(_) => Some(StatementPreservationFailureMode::Dropped),
            // SOUNDNESS: an ADDED name is blocking for statement preservation. There is no
            // before-statement to compare against, so nothing has been shown to be preserved —
            // the authority gate must not treat "no baseline" as "no drift". This mirrors the
            // pre-consolidation semantics exactly and is what makes
            // `StatementPreservationFailureMode::Missing` constructible. Note this predicate is
            // deliberately STRICTER than `rejected_statement_drift` in math_map/ingest.rs, which
            // returns None for NameAdded: that one gates bundle ingest, where a new declaration is
            // an expected outcome; this one gates statement PRESERVATION, where it is not.
            Self::NameAdded(_) => Some(StatementPreservationFailureMode::Missing),
            Self::StatementChanged { kind, .. } => Some(match kind {
                StmtChangeKind::Weaker => StatementPreservationFailureMode::Weaker,
                StmtChangeKind::Stronger => StatementPreservationFailureMode::Stronger,
                StmtChangeKind::Incomparable => StatementPreservationFailureMode::Incomparable,
                StmtChangeKind::Renamed => StatementPreservationFailureMode::Renamed,
            }),
            Self::UniverseChanged { .. } => Some(StatementPreservationFailureMode::Universe),
            Self::ImportsChanged { .. } => Some(StatementPreservationFailureMode::Import),
            Self::HypothesesChanged { .. } => Some(StatementPreservationFailureMode::Hypothesis),
        }
    }
}

/// Accepted/rejected status for the statement-preservation authority gate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum StatementPreservationGateStatus {
    /// No statement-preservation blocking drift was found.
    Accepted,
    /// One or more blocking reports rejected the gate.
    Rejected {
        /// Stable human-readable rejection reason.
        reason: String,
    },
}

/// One drift report that blocks the statement-preservation authority gate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatementPreservationBlockingReport {
    /// Stable failure-mode classification for the blocking report.
    pub failure_mode: StatementPreservationFailureMode,
    /// The underlying drift report.
    pub report: DriftReport,
}

/// First-class statement-preservation authority-gate report.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StatementPreservationGateReport {
    /// Stable gate name.
    pub gate: String,
    /// Deterministic hash of the baseline snapshot when the report was built from snapshots.
    pub before_snapshot_hash: Option<String>,
    /// Deterministic hash of the candidate snapshot when the report was built from snapshots.
    pub after_snapshot_hash: Option<String>,
    /// True only when the gate accepted.
    pub accepted: bool,
    /// Accepted/rejected gate status.
    pub status: StatementPreservationGateStatus,
    /// Aggregate drift summary.
    pub summary: DriftSummary,
    /// All drift reports considered by the gate.
    pub reports: Vec<DriftReport>,
    /// Blocking drift reports with stable failure modes.
    pub blocking_reports: Vec<StatementPreservationBlockingReport>,
}

impl StatementPreservationGateReport {
    /// Return the attempt-log status matching this gate result.
    #[must_use]
    pub fn attempt_status(&self) -> AttemptStatus {
        match &self.status {
            StatementPreservationGateStatus::Accepted => AttemptStatus::Accepted,
            StatementPreservationGateStatus::Rejected { reason } => AttemptStatus::Rejected {
                reason: reason.clone(),
            },
        }
    }

    /// Stable failure mode for attempt metadata.
    #[must_use]
    pub fn attempt_failure_mode(&self) -> Option<String> {
        if self.accepted {
            return None;
        }

        let modes: BTreeSet<_> = self
            .blocking_reports
            .iter()
            .map(|report| report.failure_mode)
            .collect();
        if modes.len() == 1 {
            modes
                .into_iter()
                .next()
                .map(|mode| mode.as_str().to_owned())
        } else {
            Some("statement_preservation_blocking_drift".to_owned())
        }
    }
}

/// Counts by drift report category.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DriftSummary {
    /// Total number of emitted drift reports.
    pub total_reports: usize,
    /// Declarations present before but absent after.
    pub names_dropped: usize,
    /// Declarations absent before but present after.
    pub names_added: usize,
    /// Declarations whose statement/type changed.
    pub statements_changed: usize,
    /// Statement changes classified as weaker.
    pub weaker_statements: usize,
    /// Statement changes classified as stronger.
    pub stronger_statements: usize,
    /// Statement changes without a proven subsumption relationship.
    pub incomparable_statements: usize,
    /// Statement changes classified as renames.
    pub renamed_statements: usize,
    /// Universe signature changes.
    pub universes_changed: usize,
    /// Direct statement-reference import proxy changes.
    pub imports_changed: usize,
    /// Leading Pi-hypothesis signature changes.
    pub hypotheses_changed: usize,
}

impl DriftSummary {
    /// Count report categories in `reports`.
    #[must_use]
    pub fn from_reports(reports: &[DriftReport]) -> Self {
        let mut summary = Self {
            total_reports: reports.len(),
            ..Self::default()
        };

        for report in reports {
            match report {
                DriftReport::NameDropped(_) => summary.names_dropped += 1,
                DriftReport::NameAdded(_) => summary.names_added += 1,
                DriftReport::StatementChanged { kind, .. } => {
                    summary.statements_changed += 1;
                    match kind {
                        StmtChangeKind::Weaker => summary.weaker_statements += 1,
                        StmtChangeKind::Stronger => summary.stronger_statements += 1,
                        StmtChangeKind::Incomparable => summary.incomparable_statements += 1,
                        StmtChangeKind::Renamed => summary.renamed_statements += 1,
                    }
                }
                DriftReport::UniverseChanged { .. } => summary.universes_changed += 1,
                DriftReport::ImportsChanged { .. } => summary.imports_changed += 1,
                DriftReport::HypothesesChanged { .. } => summary.hypotheses_changed += 1,
            }
        }

        summary
    }

    /// Whether the diff emitted no reports.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.total_reports == 0
    }

    /// Whether any statement drift was classified as weaker.
    #[must_use]
    pub fn has_weaker_drift(&self) -> bool {
        self.weaker_statements > 0
    }
}

/// Take a deterministic snapshot of the declaration surface in `env`.
#[must_use]
pub fn snapshot(env: &Environment) -> EnvSnapshot {
    let declarations = env
        .constants()
        .map(snapshot_decl)
        .map(|decl| (decl.name.clone(), decl))
        .collect();

    EnvSnapshot { declarations }
}

/// Compare two snapshots and return deterministic drift reports.
#[must_use]
pub fn diff(before: &EnvSnapshot, after: &EnvSnapshot) -> Vec<DriftReport> {
    let mut reports = Vec::new();
    let names: BTreeSet<Name> = before
        .declarations
        .keys()
        .chain(after.declarations.keys())
        .cloned()
        .collect();

    for name in names {
        match (
            before.declarations.get(&name),
            after.declarations.get(&name),
        ) {
            (Some(_), None) => reports.push(DriftReport::NameDropped(name)),
            (None, Some(_)) => reports.push(DriftReport::NameAdded(name)),
            (Some(before_decl), Some(after_decl)) => {
                if before_decl.statement_hash != after_decl.statement_hash {
                    reports.push(DriftReport::StatementChanged {
                        name: name.clone(),
                        before: before_decl.statement_hash,
                        after: after_decl.statement_hash,
                        kind: classify_statement_change(before_decl, after_decl),
                    });
                }

                if before_decl.universe_sig.hash != after_decl.universe_sig.hash {
                    reports.push(DriftReport::UniverseChanged {
                        name: name.clone(),
                        before_sig: before_decl.universe_sig.clone(),
                        after_sig: after_decl.universe_sig.clone(),
                    });
                }

                if before_decl.imports_hash != after_decl.imports_hash {
                    let before_imports: BTreeSet<_> = before_decl.imports.iter().cloned().collect();
                    let after_imports: BTreeSet<_> = after_decl.imports.iter().cloned().collect();
                    reports.push(DriftReport::ImportsChanged {
                        name: name.clone(),
                        added: after_imports.difference(&before_imports).cloned().collect(),
                        removed: before_imports.difference(&after_imports).cloned().collect(),
                    });
                }

                if before_decl.hyp_list_hash != after_decl.hyp_list_hash {
                    reports.push(DriftReport::HypothesesChanged {
                        name,
                        diff: hyp_diff(&before_decl.hypotheses, &after_decl.hypotheses),
                    });
                }
            }
            (None, None) => unreachable!("name came from one of the two snapshots"),
        }
    }

    reports
}

/// Save an environment snapshot to a deterministic JSON file.
pub fn save_snapshot_json(
    snapshot: &EnvSnapshot,
    path: impl AsRef<Path>,
) -> Result<(), DriftSnapshotError> {
    let path = path.as_ref();
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|source| DriftSnapshotError::Io {
            action: "create parent directory for",
            path: parent.to_path_buf(),
            source,
        })?;
    }

    let file = File::create(path).map_err(|source| DriftSnapshotError::Io {
        action: "create",
        path: path.to_path_buf(),
        source,
    })?;
    let mut writer = BufWriter::new(file);
    let file_snapshot = EnvSnapshotFile::from(snapshot);
    serde_json::to_writer_pretty(&mut writer, &file_snapshot).map_err(|source| {
        DriftSnapshotError::Json {
            action: "write",
            path: path.to_path_buf(),
            source,
        }
    })?;
    writer
        .write_all(b"\n")
        .and_then(|()| writer.flush())
        .map_err(|source| DriftSnapshotError::Io {
            action: "flush",
            path: path.to_path_buf(),
            source,
        })
}

/// Load an environment snapshot from a JSON file written by [`save_snapshot_json`].
pub fn load_snapshot_json(path: impl AsRef<Path>) -> Result<EnvSnapshot, DriftSnapshotError> {
    let path = path.as_ref();
    let file = File::open(path).map_err(|source| DriftSnapshotError::Io {
        action: "open",
        path: path.to_path_buf(),
        source,
    })?;
    let file_snapshot: EnvSnapshotFile =
        serde_json::from_reader(BufReader::new(file)).map_err(|source| {
            DriftSnapshotError::Json {
                action: "read",
                path: path.to_path_buf(),
                source,
            }
        })?;
    file_snapshot.into_snapshot(path)
}

/// Summarize drift report categories.
#[must_use]
pub fn summarize_reports(reports: &[DriftReport]) -> DriftSummary {
    DriftSummary::from_reports(reports)
}

/// Convert drift reports into a first-class statement-preservation authority-gate report.
#[must_use]
pub fn statement_preservation_gate_report(
    reports: &[DriftReport],
) -> StatementPreservationGateReport {
    let blocking_reports: Vec<_> = reports
        .iter()
        .filter_map(|report| {
            report
                .statement_preservation_failure_mode()
                .map(|failure_mode| StatementPreservationBlockingReport {
                    failure_mode,
                    report: report.clone(),
                })
        })
        .collect();
    let accepted = blocking_reports.is_empty();
    let status = if accepted {
        StatementPreservationGateStatus::Accepted
    } else {
        StatementPreservationGateStatus::Rejected {
            reason: statement_preservation_rejection_reason(&blocking_reports),
        }
    };

    StatementPreservationGateReport {
        gate: STATEMENT_PRESERVATION_AUTHORITY_GATE.to_owned(),
        before_snapshot_hash: None,
        after_snapshot_hash: None,
        accepted,
        status,
        summary: DriftSummary::from_reports(reports),
        reports: reports.to_vec(),
        blocking_reports,
    }
}

/// Compare two snapshots and produce statement-preservation authority-gate evidence.
#[must_use]
pub fn statement_preservation_gate_report_for_snapshots(
    before: &EnvSnapshot,
    after: &EnvSnapshot,
) -> StatementPreservationGateReport {
    let reports = diff(before, after);
    let mut report = statement_preservation_gate_report(&reports);
    report.before_snapshot_hash = Some(snapshot_digest(before));
    report.after_snapshot_hash = Some(snapshot_digest(after));
    report
}

/// Record a statement-preservation report as append-only Mathverse authority-gate evidence.
pub fn record_statement_preservation_authority_gate_attempt(
    root: impl AsRef<Path>,
    report: &StatementPreservationGateReport,
    wall_time_ms: u64,
) -> MathverseResult<ProofAttempt> {
    let root = root.as_ref();
    let env = EnvFingerprint::capture(root)?;
    let report_json = serde_json::to_vec_pretty(report)?;
    let report_artifact = put_artifact(
        root,
        &report_json,
        Some(STATEMENT_PRESERVATION_REPORT_ARTIFACT_KIND),
        Some(STATEMENT_PRESERVATION_REPORT_ARTIFACT_LOGICAL_NAME),
    )?;

    let mut attempt = AuthorityGateAttempt::new(
        STATEMENT_PRESERVATION_AUTHORITY_GATE,
        statement_preservation_goal_hash(report),
        report.attempt_status(),
        blake3_hex(&report_json),
        env,
    );
    attempt.wall_time_ms = wall_time_ms;
    attempt.failure_mode = report.attempt_failure_mode();
    attempt.solver_artifact = Some(report_artifact);
    if report.accepted {
        attempt.trust_level = Some(TrustLevel::KernelVerified);
        attempt.command_evidence = Some(statement_preservation_command_evidence(
            root,
            report,
            &attempt.goal_hash,
            &attempt.trust_audit_hash,
        )?);
    }
    record_authority_gate_attempt(root, attempt)
}

fn statement_preservation_command_evidence(
    root: &Path,
    report: &StatementPreservationGateReport,
    goal_hash: &str,
    trust_audit_hash: &str,
) -> MathverseResult<ArtifactRef> {
    let evidence = serde_json::json!({
        "schema_version": "clean.statement-preservation-command-evidence.v1",
        "authority_gate": STATEMENT_PRESERVATION_AUTHORITY_GATE,
        "replay": {
            "kind": "in_process_snapshot_diff",
            "function": "statement_preservation_gate_report_for_snapshots",
            "before_snapshot_hash": report.before_snapshot_hash,
            "after_snapshot_hash": report.after_snapshot_hash,
        },
        "goal_hash": goal_hash,
        "report_hash": trust_audit_hash,
    });
    let bytes = serde_json::to_vec_pretty(&evidence)?;
    put_artifact(
        root,
        &bytes,
        Some(STATEMENT_PRESERVATION_COMMAND_EVIDENCE_ARTIFACT_KIND),
        Some(STATEMENT_PRESERVATION_COMMAND_EVIDENCE_LOGICAL_NAME),
    )
}

/// Extract theorem statement hashes as `blake3:<hex>` strings keyed by declaration name.
#[must_use]
pub fn theorem_statement_hashes(snapshot: &EnvSnapshot) -> BTreeMap<String, String> {
    snapshot
        .declarations
        .values()
        .filter(|decl| decl.kind == ConstantKind::Theorem)
        .map(|decl| {
            (
                decl.name.to_string(),
                format_drift_hash(decl.statement_hash),
            )
        })
        .collect()
}

/// Build deterministic theorem statement comparison inputs keyed by qualified name.
#[must_use]
pub fn theorem_statement_comparison_inputs(
    before: &EnvSnapshot,
    after: &EnvSnapshot,
) -> Vec<TheoremStatementComparisonInput> {
    let names: BTreeSet<Name> = before
        .declarations
        .iter()
        .chain(after.declarations.iter())
        .filter(|(_, decl)| decl.kind == ConstantKind::Theorem)
        .map(|(name, _)| name.clone())
        .collect();

    names
        .into_iter()
        .map(|name| {
            let before_statement_hash = before
                .declarations
                .get(&name)
                .filter(|decl| decl.kind == ConstantKind::Theorem)
                .map(|decl| format_drift_hash(decl.statement_hash));
            let after_statement_hash = after
                .declarations
                .get(&name)
                .filter(|decl| decl.kind == ConstantKind::Theorem)
                .map(|decl| format_drift_hash(decl.statement_hash));

            TheoremStatementComparisonInput {
                theorem: name.last_component().unwrap_or_else(|| name.to_string()),
                qualified_name: name.to_string(),
                before_statement_hash,
                after_statement_hash,
            }
        })
        .collect()
}

/// Format a drift hash as the digest string accepted by statement-preservation gates.
#[must_use]
pub fn format_drift_hash(hash: DriftHash) -> String {
    format!("blake3:{}", blake3::Hash::from_bytes(hash).to_hex())
}

/// Deterministic goal hash binding a gate report to the snapshots it compared.
#[must_use]
pub fn statement_preservation_goal_hash(report: &StatementPreservationGateReport) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STATEMENT_PRESERVATION_AUTHORITY_GATE.as_bytes());
    hasher.update(&[0]);
    if let Some(before_snapshot_hash) = &report.before_snapshot_hash {
        hasher.update(b"before-snapshot");
        hasher.update(&[0]);
        hasher.update(before_snapshot_hash.as_bytes());
        hasher.update(&[0]);
    }
    if let Some(after_snapshot_hash) = &report.after_snapshot_hash {
        hasher.update(b"after-snapshot");
        hasher.update(&[0]);
        hasher.update(after_snapshot_hash.as_bytes());
        hasher.update(&[0]);
    }
    for input in statement_preservation_goal_inputs(&report.reports) {
        hasher.update(input.as_bytes());
        hasher.update(&[0]);
    }
    hasher.finalize().to_hex().to_string()
}

fn statement_preservation_goal_inputs(reports: &[DriftReport]) -> Vec<String> {
    let mut inputs = reports
        .iter()
        .map(|report| match report {
            DriftReport::NameDropped(name) => format!("dropped:{name}"),
            DriftReport::NameAdded(name) => format!("missing:{name}"),
            DriftReport::StatementChanged {
                name,
                before,
                after,
                kind,
            } => format!(
                "statement:{name}:{kind:?}:{}:{}",
                format_drift_hash(*before),
                format_drift_hash(*after)
            ),
            DriftReport::UniverseChanged { name, .. } => format!("universe:{name}"),
            DriftReport::ImportsChanged { name, .. } => format!("import:{name}"),
            DriftReport::HypothesesChanged { name, .. } => format!("hypothesis:{name}"),
        })
        .collect::<Vec<_>>();
    inputs.sort();
    inputs
}

fn statement_preservation_rejection_reason(
    blocking_reports: &[StatementPreservationBlockingReport],
) -> String {
    let mut by_mode = BTreeMap::<StatementPreservationFailureMode, usize>::new();
    for report in blocking_reports {
        *by_mode.entry(report.failure_mode).or_insert(0) += 1;
    }
    let counts = by_mode
        .into_iter()
        .map(|(mode, count)| format!("{}={count}", mode.as_str()))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "statement preservation rejected {} blocking report(s): {counts}",
        blocking_reports.len()
    )
}

fn blake3_hex(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

fn snapshot_digest(snapshot: &EnvSnapshot) -> String {
    let bytes = serde_json::to_vec(&EnvSnapshotFile::from(snapshot))
        .expect("EnvSnapshotFile serialization should be deterministic and infallible");
    format!("blake3:{}", blake3_hex(&bytes))
}

/// On-disk snapshot shape: a name-ordered declaration list, so the JSON is
/// deterministic and does not depend on map key encoding.
#[derive(Deserialize, Serialize)]
struct EnvSnapshotFile {
    declarations: Vec<DeclSnapshot>,
}

impl From<&EnvSnapshot> for EnvSnapshotFile {
    fn from(snapshot: &EnvSnapshot) -> Self {
        Self {
            declarations: snapshot.declarations.values().cloned().collect(),
        }
    }
}

impl EnvSnapshotFile {
    fn into_snapshot(self, path: &Path) -> Result<EnvSnapshot, DriftSnapshotError> {
        let mut declarations = BTreeMap::new();
        for decl in self.declarations {
            let name = decl.name.clone();
            if declarations.insert(name.clone(), decl).is_some() {
                return Err(DriftSnapshotError::Invalid {
                    path: path.to_path_buf(),
                    message: format!("duplicate declaration `{name}`"),
                });
            }
        }

        Ok(EnvSnapshot { declarations })
    }
}

fn snapshot_decl(info: &ConstantInfo) -> DeclSnapshot {
    let (hypotheses, conclusion) = pi_spine(&info.type_);
    let imports = direct_statement_imports(&info.type_);

    DeclSnapshot {
        name: info.name.clone(),
        kind: info.kind,
        statement_hash: stable_hash("clean-mathverse.drift.statement.v1", &info.type_),
        hyp_list_hash: stable_hash("clean-mathverse.drift.hypotheses.v1", &hypotheses),
        hypotheses,
        conclusion_hash: stable_hash("clean-mathverse.drift.conclusion.v1", conclusion),
        universe_sig: UniverseSig {
            params: info.level_params.clone(),
            hash: stable_hash("clean-mathverse.drift.universes.v1", &info.level_params),
        },
        imports_hash: stable_hash("clean-mathverse.drift.imports.v1", &imports),
        imports,
    }
}

fn classify_statement_change(before: &DeclSnapshot, after: &DeclSnapshot) -> StmtChangeKind {
    if hypothesis_spine_dropped(before, after) {
        StmtChangeKind::Weaker
    } else if hypothesis_spine_dropped(after, before) {
        StmtChangeKind::Stronger
    } else {
        StmtChangeKind::Incomparable
    }
}

fn hypothesis_spine_dropped(before: &DeclSnapshot, after: &DeclSnapshot) -> bool {
    before.conclusion_hash == after.conclusion_hash
        && before.hypotheses.len() > after.hypotheses.len()
        && is_ordered_subsequence(&after.hypotheses, &before.hypotheses)
}

fn is_ordered_subsequence(needle: &[HypothesisSig], haystack: &[HypothesisSig]) -> bool {
    let mut next = 0;
    for hyp in haystack {
        if needle
            .get(next)
            .is_some_and(|candidate| same_hyp_shape(candidate, hyp))
        {
            next += 1;
            if next == needle.len() {
                return true;
            }
        }
    }
    needle.is_empty()
}

fn hyp_diff(before: &[HypothesisSig], after: &[HypothesisSig]) -> HypDiff {
    let mut after_used = vec![false; after.len()];
    let mut removed = Vec::new();

    for before_hyp in before {
        if let Some(idx) = after
            .iter()
            .enumerate()
            .position(|(idx, after_hyp)| !after_used[idx] && same_hyp_shape(before_hyp, after_hyp))
        {
            after_used[idx] = true;
        } else {
            removed.push(before_hyp.clone());
        }
    }

    let added = after
        .iter()
        .enumerate()
        .filter(|(idx, _)| !after_used[*idx])
        .map(|(_, hyp)| hyp.clone())
        .collect();

    HypDiff {
        before: before.to_vec(),
        after: after.to_vec(),
        removed,
        added,
    }
}

fn same_hyp_shape(left: &HypothesisSig, right: &HypothesisSig) -> bool {
    left.binder == right.binder && left.type_hash == right.type_hash
}

fn pi_spine(expr: &Expr) -> (Vec<HypothesisSig>, &Expr) {
    let mut hypotheses = Vec::new();
    let mut current = expr;

    while let ExprKind::Pi(binder, domain, body) = current.kind() {
        hypotheses.push(HypothesisSig {
            index: hypotheses.len(),
            binder: *binder,
            type_hash: stable_hash("clean-mathverse.drift.hyp-domain.v1", domain.as_ref()),
        });
        current = body;
    }

    (hypotheses, current)
}

fn direct_statement_imports(expr: &Expr) -> Vec<Name> {
    let mut names = BTreeSet::new();
    let mut stack = vec![expr];

    while let Some(current) = stack.pop() {
        match current.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => {}
            ExprKind::Const(name, _) => {
                names.insert(name.clone());
            }
            ExprKind::App(func, arg) => {
                stack.push(arg);
                stack.push(func);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(body);
                stack.push(ty);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                stack.push(body);
                stack.push(value);
                stack.push(ty);
            }
            ExprKind::Proj(struct_name, _, inner) => {
                names.insert(struct_name.clone());
                stack.push(inner);
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                stack.push(inner);
            }
            ExprKind::CubicalPath { ty, left, right } => {
                stack.push(right);
                stack.push(left);
                stack.push(ty);
            }
            ExprKind::CubicalPathLam { body } => {
                stack.push(body);
            }
            ExprKind::CubicalPathApp { path, arg } => {
                stack.push(arg);
                stack.push(path);
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                stack.push(base);
                stack.push(u);
                stack.push(phi);
                stack.push(ty);
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                stack.push(base);
                stack.push(phi);
                stack.push(ty);
            }
            // All four `coe` children are non-binder subterms that can mention
            // constants, so every one is traversed — the same shape used by
            // `trust::project_audit::collect_expr_constant_refs`.
            ExprKind::CubicalCoe { ty, r, s, base } => {
                stack.push(base);
                stack.push(s);
                stack.push(r);
                stack.push(ty);
            }
            ExprKind::ZFCSet(set_expr) => push_zfc_set_expr(set_expr, &mut stack),
            ExprKind::ZFCMem { element, set } => {
                stack.push(set);
                stack.push(element);
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                stack.push(pred);
                stack.push(domain);
            }
        }
    }

    names.into_iter().collect()
}

fn push_zfc_set_expr<'a>(set_expr: &'a ZFCSetExpr, stack: &mut Vec<&'a Expr>) {
    match set_expr {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => stack.push(expr),
        ZFCSetExpr::Pair(left, right)
        | ZFCSetExpr::Separation {
            set: left,
            pred: right,
        }
        | ZFCSetExpr::Replacement {
            set: left,
            func: right,
        } => {
            stack.push(right);
            stack.push(left);
        }
    }
}

fn stable_hash<T: Serialize>(tag: &'static str, value: &T) -> DriftHash {
    let payload = bincode::serde::encode_to_vec(value, bincode::config::standard())
        .expect("drift snapshot hashing only serializes in-memory kernel values");
    let mut hasher = blake3::Hasher::new();
    hasher.update(tag.as_bytes());
    hasher.update(&[0]);
    hasher.update(&payload);
    *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Declaration};

    #[test]
    fn test_every_drift_report_is_authority_gate_blocking() {
        let name = Name::from_string("Foo.bar");

        // An ADDED name is blocking: there is no before-statement, so nothing has been
        // shown to be preserved. Fail-closed — "no baseline" is not "no drift".
        assert!(DriftReport::NameAdded(name.clone()).is_authority_gate_blocking());
        assert_eq!(
            DriftReport::NameAdded(name.clone()).statement_preservation_failure_mode(),
            Some(StatementPreservationFailureMode::Missing),
        );
        assert!(DriftReport::NameDropped(name.clone()).is_authority_gate_blocking());
        assert!(DriftReport::StatementChanged {
            name: name.clone(),
            before: [0; 32],
            after: [1; 32],
            kind: StmtChangeKind::Incomparable,
        }
        .is_authority_gate_blocking());
        assert!(DriftReport::UniverseChanged {
            name: name.clone(),
            before_sig: UniverseSig {
                params: Vec::new(),
                hash: [0; 32]
            },
            after_sig: UniverseSig {
                params: vec![Name::from_string("u")],
                hash: [1; 32]
            },
        }
        .is_authority_gate_blocking());
        assert!(DriftReport::ImportsChanged {
            name: name.clone(),
            added: vec![Name::from_string("Mathlib.Tactic")],
            removed: Vec::new(),
        }
        .is_authority_gate_blocking());
        assert!(DriftReport::HypothesesChanged {
            name,
            diff: HypDiff::default(),
        }
        .is_authority_gate_blocking());
    }

    #[test]
    fn test_statement_change_kind_maps_to_stable_failure_mode() {
        let name = Name::from_string("Foo.bar");
        let mode = DriftReport::StatementChanged {
            name,
            before: [0; 32],
            after: [1; 32],
            kind: StmtChangeKind::Weaker,
        }
        .statement_preservation_failure_mode()
        .expect("weaker statements block the gate");

        assert_eq!(mode.as_str(), "statement_preservation_weaker");
    }

    #[test]
    fn detects_dropped_theorem_hypothesis_as_weaker() {
        let theorem_name = Name::from_string("Drift.synthetic.theorem");

        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P", "Drift.R"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem(
            &mut after,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let reports = diff(&snapshot(&before), &snapshot(&after));

        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::StatementChanged {
                    name,
                    kind: StmtChangeKind::Weaker,
                    ..
                } if name == &theorem_name
            )
        }));

        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::HypothesesChanged {
                    name,
                    diff: HypDiff { removed, added, .. },
                } if name == &theorem_name && removed.len() == 1 && added.is_empty()
            )
        }));
    }

    #[test]
    fn detects_added_theorem_hypothesis_as_stronger() {
        let theorem_name = Name::from_string("Drift.synthetic.stronger_theorem");

        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem(
            &mut after,
            theorem_name.clone(),
            theorem_type(&["Drift.P", "Drift.P"], "Drift.Q"),
        );

        let reports = diff(&snapshot(&before), &snapshot(&after));

        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::StatementChanged {
                    name,
                    kind: StmtChangeKind::Stronger,
                    ..
                } if name == &theorem_name
            )
        }));

        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::HypothesesChanged {
                    name,
                    diff: HypDiff { removed, added, .. },
                } if name == &theorem_name && removed.is_empty() && added.len() == 1
            )
        }));
    }

    #[test]
    fn detects_dropped_theorem_name() {
        let theorem_name = Name::from_string("Drift.synthetic.dropped_theorem");

        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );
        let after = Environment::new();

        let before_snapshot = snapshot(&before);
        let after_snapshot = snapshot(&after);
        let reports = diff(&before_snapshot, &after_snapshot);

        assert!(before_snapshot.get(&theorem_name).is_some());
        assert!(after_snapshot.get(&theorem_name).is_none());
        assert!(reports.iter().any(
            |report| matches!(report, DriftReport::NameDropped(name) if name == &theorem_name)
        ));
    }

    #[test]
    fn detects_changed_theorem_statement_hash_as_incomparable() {
        let theorem_name = Name::from_string("Drift.synthetic.hyp_type_changed");

        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem(
            &mut after,
            theorem_name.clone(),
            theorem_type(&["Drift.R"], "Drift.Q"),
        );

        let before_snapshot = snapshot(&before);
        let after_snapshot = snapshot(&after);
        let before_hash = before_snapshot
            .get(&theorem_name)
            .expect("before theorem snapshot present")
            .statement_hash;
        let after_hash = after_snapshot
            .get(&theorem_name)
            .expect("after theorem snapshot present")
            .statement_hash;
        let reports = diff(&before_snapshot, &after_snapshot);

        assert_ne!(before_hash, after_hash);
        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::StatementChanged {
                    name,
                    before,
                    after,
                    kind: StmtChangeKind::Incomparable,
                } if name == &theorem_name && *before == before_hash && *after == after_hash
            )
        }));
        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::HypothesesChanged {
                    name,
                    diff: HypDiff { removed, added, .. },
                } if name == &theorem_name && removed.len() == 1 && added.len() == 1
            )
        }));
    }

    #[test]
    fn authority_gate_blocking_reports_are_classified_deterministically() {
        let name = Name::from_string("Drift.synthetic.blocking");
        let hash_before = stable_hash("test.before", &"before");
        let hash_after = stable_hash("test.after", &"after");
        let universe_before = UniverseSig {
            params: vec![Name::from_string("u")],
            hash: hash_before,
        };
        let universe_after = UniverseSig {
            params: vec![Name::from_string("v")],
            hash: hash_after,
        };
        let diff = HypDiff {
            before: Vec::new(),
            after: Vec::new(),
            removed: Vec::new(),
            added: Vec::new(),
        };

        let blocking_reports = [
            DriftReport::NameDropped(name.clone()),
            DriftReport::NameAdded(name.clone()),
            DriftReport::StatementChanged {
                name: name.clone(),
                before: hash_before,
                after: hash_after,
                kind: StmtChangeKind::Incomparable,
            },
            DriftReport::UniverseChanged {
                name: name.clone(),
                before_sig: universe_before,
                after_sig: universe_after,
            },
            DriftReport::HypothesesChanged {
                name: name.clone(),
                diff,
            },
            DriftReport::ImportsChanged {
                name: name.clone(),
                added: vec![Name::from_string("Drift.synthetic.added_import")],
                removed: vec![Name::from_string("Drift.synthetic.removed_import")],
            },
        ];

        for report in blocking_reports {
            assert!(
                report.is_authority_gate_blocking(),
                "expected blocking report: {report:?}"
            );
        }
    }

    #[test]
    fn statement_preservation_gate_accepts_exact_match() {
        let theorem_name = Name::from_string("Drift.synthetic.exact_match");
        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem(
            &mut after,
            theorem_name,
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let report =
            statement_preservation_gate_report_for_snapshots(&snapshot(&before), &snapshot(&after));

        assert!(report.accepted);
        assert_eq!(report.gate, STATEMENT_PRESERVATION_AUTHORITY_GATE);
        assert!(report.before_snapshot_hash.is_some());
        assert_eq!(report.before_snapshot_hash, report.after_snapshot_hash);
        assert_eq!(report.status, StatementPreservationGateStatus::Accepted);
        assert!(report.blocking_reports.is_empty());
        assert!(matches!(report.attempt_status(), AttemptStatus::Accepted));
        assert_eq!(report.attempt_failure_mode(), None);
    }

    #[test]
    fn statement_preservation_goal_hash_is_bound_to_snapshot_identity() {
        let empty = EnvSnapshot::default();
        let empty_report = statement_preservation_gate_report_for_snapshots(&empty, &empty);

        let mut theorem_env = Environment::new();
        add_synthetic_theorem(
            &mut theorem_env,
            Name::from_string("Drift.synthetic.hash_bound"),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );
        let theorem_snapshot = snapshot(&theorem_env);
        let theorem_report =
            statement_preservation_gate_report_for_snapshots(&theorem_snapshot, &theorem_snapshot);

        assert!(empty_report.accepted);
        assert!(theorem_report.accepted);
        assert!(empty_report.reports.is_empty());
        assert!(theorem_report.reports.is_empty());
        assert_ne!(
            empty_report.before_snapshot_hash,
            theorem_report.before_snapshot_hash
        );
        assert_ne!(
            statement_preservation_goal_hash(&empty_report),
            statement_preservation_goal_hash(&theorem_report)
        );
    }

    #[test]
    fn statement_preservation_gate_rejects_dropped_theorem() {
        let theorem_name = Name::from_string("Drift.synthetic.dropped_gate_theorem");
        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );
        let after = Environment::new();

        let report =
            statement_preservation_gate_report_for_snapshots(&snapshot(&before), &snapshot(&after));

        assert!(!report.accepted);
        assert!(matches!(
            report.status,
            StatementPreservationGateStatus::Rejected { .. }
        ));
        assert!(report.blocking_reports.iter().any(|blocking| {
            blocking.failure_mode == StatementPreservationFailureMode::Dropped
                && matches!(&blocking.report, DriftReport::NameDropped(name) if name == &theorem_name)
        }));
        assert_eq!(
            report.attempt_failure_mode().as_deref(),
            Some("statement_preservation_dropped")
        );
    }

    #[test]
    fn statement_preservation_gate_rejects_weaker_and_changed_statement() {
        let weaker_name = Name::from_string("Drift.synthetic.weaker_gate_theorem");
        let mut before_weaker = Environment::new();
        add_synthetic_theorem(
            &mut before_weaker,
            weaker_name.clone(),
            theorem_type(&["Drift.P", "Drift.R"], "Drift.Q"),
        );
        let mut after_weaker = Environment::new();
        add_synthetic_theorem(
            &mut after_weaker,
            weaker_name,
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let weaker_report = statement_preservation_gate_report_for_snapshots(
            &snapshot(&before_weaker),
            &snapshot(&after_weaker),
        );

        assert!(!weaker_report.accepted);
        assert!(weaker_report
            .blocking_reports
            .iter()
            .any(|blocking| blocking.failure_mode == StatementPreservationFailureMode::Weaker));

        let changed_name = Name::from_string("Drift.synthetic.changed_gate_theorem");
        let mut before_changed = Environment::new();
        add_synthetic_theorem(
            &mut before_changed,
            changed_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );
        let mut after_changed = Environment::new();
        add_synthetic_theorem(
            &mut after_changed,
            changed_name,
            theorem_type(&["Drift.R"], "Drift.Q"),
        );

        let changed_report = statement_preservation_gate_report_for_snapshots(
            &snapshot(&before_changed),
            &snapshot(&after_changed),
        );

        assert!(!changed_report.accepted);
        assert!(changed_report.blocking_reports.iter().any(|blocking| {
            blocking.failure_mode == StatementPreservationFailureMode::Incomparable
        }));
    }

    #[test]
    fn statement_preservation_attempt_metadata_is_recorded() {
        let theorem_name = Name::from_string("Drift.synthetic.attempt_metadata");
        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name,
            theorem_type(&["Drift.P"], "Drift.Q"),
        );
        let after = Environment::new();
        let report =
            statement_preservation_gate_report_for_snapshots(&snapshot(&before), &snapshot(&after));

        let temp = tempfile::tempdir().expect("temp dir");
        let root = temp.path();
        let attempt = record_statement_preservation_authority_gate_attempt(root, &report, 37)
            .expect("record statement-preservation gate attempt");
        let attempts: Vec<_> = crate::attempt_log::iter_from(
            root,
            crate::attempt_log::AttemptFilter {
                authority_gate: Some(STATEMENT_PRESERVATION_AUTHORITY_GATE.to_owned()),
                ..crate::attempt_log::AttemptFilter::default()
            },
        )
        .expect("query attempts")
        .collect();

        assert_eq!(attempts, vec![attempt.clone()]);
        assert_eq!(
            attempt.authority_gate.as_deref(),
            Some(STATEMENT_PRESERVATION_AUTHORITY_GATE)
        );
        assert!(matches!(attempt.status, AttemptStatus::Rejected { .. }));
        assert_eq!(attempt.wall_time_ms, 37);
        assert_eq!(
            attempt.failure_mode.as_deref(),
            Some("statement_preservation_dropped")
        );
        assert_eq!(
            attempt
                .solver_artifact
                .as_ref()
                .and_then(|artifact| artifact.kind.as_deref()),
            Some("authority-gate/statement-preservation-report")
        );
    }

    #[test]
    fn accepted_statement_preservation_attempt_records_command_evidence() {
        let snapshot = EnvSnapshot::default();
        let report = statement_preservation_gate_report_for_snapshots(&snapshot, &snapshot);

        let temp = tempfile::tempdir().expect("temp dir");
        let root = temp.path();
        let attempt = record_statement_preservation_authority_gate_attempt(root, &report, 11)
            .expect("record accepted statement-preservation gate attempt");
        let receipt = crate::attempt_log::AuthorityReceipt::from_attempt(&attempt);

        assert!(matches!(attempt.status, AttemptStatus::Accepted));
        assert_eq!(receipt.status, "accepted");
        assert!(attempt.trust_level.is_some());
        assert_eq!(
            receipt
                .command_evidence
                .as_ref()
                .and_then(|artifact| artifact.kind.as_deref()),
            Some(STATEMENT_PRESERVATION_COMMAND_EVIDENCE_ARTIFACT_KIND)
        );
        assert_eq!(
            attempt
                .command_evidence
                .as_ref()
                .and_then(|artifact| artifact.logical_name.as_deref()),
            Some(STATEMENT_PRESERVATION_COMMAND_EVIDENCE_LOGICAL_NAME)
        );
    }

    #[test]
    fn detects_universe_drift_as_authority_gate_blocking() {
        let theorem_name = Name::from_string("Drift.synthetic.universe_changed");

        let mut before = Environment::new();
        add_synthetic_theorem_with_level_params(
            &mut before,
            theorem_name.clone(),
            vec![Name::from_string("u")],
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem_with_level_params(
            &mut after,
            theorem_name.clone(),
            vec![Name::from_string("v")],
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let reports = diff(&snapshot(&before), &snapshot(&after));

        assert!(reports.iter().any(|report| {
            matches!(
                report,
                DriftReport::UniverseChanged {
                    name,
                    before_sig,
                    after_sig,
                } if name == &theorem_name
                    && before_sig.params == vec![Name::from_string("u")]
                    && after_sig.params == vec![Name::from_string("v")]
                    && report.is_authority_gate_blocking()
            )
        }));
    }

    #[test]
    fn save_load_snapshot_json_roundtrips() {
        let theorem_name = Name::from_string("Drift.synthetic.persisted");
        let mut env = Environment::new();
        add_synthetic_theorem(
            &mut env,
            theorem_name.clone(),
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let captured = snapshot(&env);
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("nested").join("snapshot.json");

        save_snapshot_json(&captured, &path).expect("save snapshot");
        let loaded = load_snapshot_json(&path).expect("load snapshot");

        assert_eq!(loaded, captured);
        assert_eq!(
            loaded.get(&theorem_name).map(|decl| &decl.name),
            Some(&theorem_name)
        );
    }

    #[test]
    fn summary_counts_weaker_statement_drift() {
        let theorem_name = Name::from_string("Drift.synthetic.summary");

        let mut before = Environment::new();
        add_synthetic_theorem(
            &mut before,
            theorem_name.clone(),
            theorem_type(&["Drift.P", "Drift.R"], "Drift.Q"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem(
            &mut after,
            theorem_name,
            theorem_type(&["Drift.P"], "Drift.Q"),
        );

        let reports = diff(&snapshot(&before), &snapshot(&after));
        let summary = summarize_reports(&reports);

        assert_eq!(summary.total_reports, 3);
        assert_eq!(summary.statements_changed, 1);
        assert_eq!(summary.weaker_statements, 1);
        assert_eq!(summary.imports_changed, 1);
        assert_eq!(summary.hypotheses_changed, 1);
        assert_eq!(summary.stronger_statements, 0);
        assert_eq!(summary.incomparable_statements, 0);
        assert!(summary.has_weaker_drift());
        assert!(!summary.is_empty());
    }

    #[test]
    fn theorem_statement_hashes_are_gate_ready_and_ignore_proof_terms() {
        let theorem_name = Name::from_string("Drift.synthetic.gate_target");
        let definition_name = Name::from_string("Drift.synthetic.helper_def");
        let statement = theorem_type(&["Drift.P"], "Drift.Q");

        let mut before = Environment::new();
        add_synthetic_theorem_with_proof(
            &mut before,
            theorem_name.clone(),
            statement.clone(),
            Expr::const_str("Drift.synthetic.proof_before"),
        );
        add_synthetic_definition(
            &mut before,
            definition_name.clone(),
            Expr::const_str("Drift.P"),
        );

        let mut after = Environment::new();
        add_synthetic_theorem_with_proof(
            &mut after,
            theorem_name.clone(),
            statement,
            Expr::const_str("Drift.synthetic.proof_after"),
        );

        let before_snapshot = snapshot(&before);
        let after_snapshot = snapshot(&after);
        let before_hashes = before_snapshot.theorem_statement_hashes();
        let after_hashes = theorem_statement_hashes(&after_snapshot);

        assert_eq!(before_hashes, after_hashes);
        assert_eq!(before_hashes.len(), 1);
        assert!(!before_hashes.contains_key(&definition_name.to_string()));

        let digest = before_hashes
            .get(&theorem_name.to_string())
            .expect("theorem hash present");
        let hex = digest
            .strip_prefix("blake3:")
            .expect("gate digest prefix present");
        assert_eq!(hex.len(), 64);
        assert!(hex.chars().all(|ch| ch.is_ascii_hexdigit()));
        assert_eq!(
            digest,
            &format_drift_hash(
                before_snapshot
                    .get(&theorem_name)
                    .expect("theorem snapshot present")
                    .statement_hash
            )
        );
    }

    #[test]
    fn theorem_statement_comparison_inputs_preserve_namespace_qualified_names() {
        let theorem_name = Name::from_string("Mathlib.MeasureTheory.Foo.bar");
        let statement_before = theorem_type(&["Drift.P"], "Drift.Q");
        let statement_after = theorem_type(&["Drift.P", "Drift.R"], "Drift.Q");

        let mut before = Environment::new();
        add_synthetic_theorem(&mut before, theorem_name.clone(), statement_before);

        let mut after = Environment::new();
        add_synthetic_theorem(&mut after, theorem_name.clone(), statement_after);

        let before_snapshot = snapshot(&before);
        let after_snapshot = snapshot(&after);
        let inputs = theorem_statement_comparison_inputs(&before_snapshot, &after_snapshot);

        assert_eq!(inputs.len(), 1);
        assert_eq!(
            inputs[0],
            TheoremStatementComparisonInput {
                theorem: "bar".to_owned(),
                qualified_name: "Mathlib.MeasureTheory.Foo.bar".to_owned(),
                before_statement_hash: Some(format_drift_hash(
                    before_snapshot
                        .get(&theorem_name)
                        .expect("before theorem snapshot present")
                        .statement_hash,
                )),
                after_statement_hash: Some(format_drift_hash(
                    after_snapshot
                        .get(&theorem_name)
                        .expect("after theorem snapshot present")
                        .statement_hash,
                )),
            }
        );
        assert_ne!(
            inputs[0].before_statement_hash,
            inputs[0].after_statement_hash
        );
    }

    #[test]
    fn theorem_statement_comparison_inputs_do_not_collapse_namespace_drift() {
        let before_name = Name::from_string("Mathlib.MeasureTheory.Foo.bar");
        let after_name = Name::from_string("Mathlib.MeasureTheory.Bar.bar");
        let statement = theorem_type(&["Drift.P"], "Drift.Q");

        let mut before = Environment::new();
        add_synthetic_theorem(&mut before, before_name.clone(), statement.clone());

        let mut after = Environment::new();
        add_synthetic_theorem(&mut after, after_name.clone(), statement);

        let before_snapshot = snapshot(&before);
        let after_snapshot = snapshot(&after);
        let inputs =
            EnvSnapshot::theorem_statement_comparison_inputs(&before_snapshot, &after_snapshot);

        assert_eq!(inputs.len(), 2);
        assert_eq!(inputs[0].theorem, "bar");
        assert_eq!(inputs[0].qualified_name, "Mathlib.MeasureTheory.Bar.bar");
        assert_eq!(inputs[0].before_statement_hash, None);
        assert!(inputs[0].after_statement_hash.is_some());
        assert_eq!(inputs[1].theorem, "bar");
        assert_eq!(inputs[1].qualified_name, "Mathlib.MeasureTheory.Foo.bar");
        assert!(inputs[1].before_statement_hash.is_some());
        assert_eq!(inputs[1].after_statement_hash, None);
    }

    fn theorem_type(hypotheses: &[&str], conclusion: &str) -> Expr {
        hypotheses
            .iter()
            .rev()
            .fold(Expr::const_str(conclusion), |body, hyp| {
                Expr::pi(BinderInfo::Default, Expr::const_str(hyp), body)
            })
    }

    fn add_synthetic_theorem(env: &mut Environment, name: Name, type_: Expr) {
        add_synthetic_theorem_with_proof(
            env,
            name,
            type_,
            Expr::const_str("Drift.synthetic.proof"),
        );
    }

    fn add_synthetic_theorem_with_level_params(
        env: &mut Environment,
        name: Name,
        level_params: Vec<Name>,
        type_: Expr,
    ) {
        // SOUNDNESS: test-only fixture. `add_decl_structural` skips kernel type
        // checking, which is exactly what these drift fixtures need — the
        // synthetic statements reference undeclared constants (`Drift.P`,
        // `Drift.Q`) on purpose, because the snapshot/diff engine hashes the
        // declaration SURFACE and never depends on the declarations being
        // well-typed. Nothing here mints a trust verdict or leaves the test
        // environment, so this is not a production bypass and is excluded from
        // data/unchecked_decl_ratchet.json's production-site counts.
        env.add_decl_structural(Declaration::Theorem {
            name,
            level_params,
            type_,
            value: Expr::const_str("Drift.synthetic.proof"),
        })
        .expect("synthetic theorem should pass structural validation");
    }

    fn add_synthetic_theorem_with_proof(
        env: &mut Environment,
        name: Name,
        type_: Expr,
        value: Expr,
    ) {
        // SOUNDNESS: test-only fixture; see the note on
        // `add_synthetic_theorem_with_level_params`.
        env.add_decl_structural(Declaration::Theorem {
            name,
            level_params: Vec::new(),
            type_,
            value,
        })
        .expect("synthetic theorem should pass structural validation");
    }

    fn add_synthetic_definition(env: &mut Environment, name: Name, type_: Expr) {
        // SOUNDNESS: test-only fixture; see the note on
        // `add_synthetic_theorem_with_level_params`.
        env.add_decl_structural(Declaration::Definition {
            name,
            level_params: Vec::new(),
            type_,
            value: Expr::const_str("Drift.synthetic.value"),
            is_reducible: true,
        })
        .expect("synthetic definition should pass structural validation");
    }
}
