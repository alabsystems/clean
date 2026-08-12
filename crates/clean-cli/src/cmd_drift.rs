// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean drift` environment-snapshot and statement-preservation commands.
//!
//! The user-facing entry point for the drift snapshot/diff engine that lives
//! in `clean_mathverse::drift`. `drift snapshot` freezes the declaration
//! surface of a kernel environment into a deterministic JSON file; `drift diff`
//! compares two such files and runs the statement-preservation authority gate
//! over the resulting reports.
//!
//! Fail-closed by construction: `drift diff` exits NON-ZERO whenever the gate
//! is blocked (a dropped, weakened, or otherwise non-preserving statement).
//! `--allow-weaker` and `--allow-authority-gate-blocking` are the only escape
//! hatches, and both are explicit operator decisions rather than defaults, so a
//! caller that checks only the status code can never read blocking drift as a
//! clean comparison.

use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::{bail, Context};
use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::Environment;
use clean_mathverse::attempt_log::AuthorityReceipt;
use clean_mathverse::drift::{
    self, load_snapshot_json, record_statement_preservation_authority_gate_attempt,
    save_snapshot_json, DriftReport, DriftSummary, EnvSnapshot, StatementPreservationGateReport,
};
use serde::Serialize;

use crate::authority_source_guard::AuthoritySourceGuard;

/// The `clean-mathverse` crate owns the snapshot/diff engine this surface
/// drives. `RefKind::Crate` (not `Doc`) because the authoritative description
/// of the contract is the module documentation on `clean_mathverse::drift`,
/// not a standalone markdown page.
const DRIFT_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-mathverse (drift snapshot/diff engine)",
    target: "clean-mathverse",
};

pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["drift", "snapshot"],
        summary: "Write an environment statement snapshot",
        description: "\
Serializes a kernel environment's declaration surface into a deterministic \
statement-preservation snapshot: per-declaration statement, hypothesis, \
conclusion, universe, and reference-proxy hashes. With `--project` the \
snapshot is taken over a Lake workspace's reconstructed source environment \
(optionally narrowed with repeated `--module`); without it the Clean prelude \
environment is used. The resulting JSON is the input to `clean drift diff`, \
which detects dropped, renamed, weakened, or otherwise changed declarations.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean drift snapshot --output before.json --json",
                what: "write a JSON drift snapshot of the prelude environment",
            },
            Example {
                cmd: "clean drift snapshot --output after.json --project . --module Test.Main",
                what: "snapshot one module of a Lake project's source environment",
            },
        ],
        see_also: &["drift diff", "audit trust-ledger"],
        references: &[DRIFT_CRATE_REF],
        domain_root: Some("drift"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["drift", "diff"],
        summary: "Compare statement snapshots for authority-gate drift",
        description: "\
Compares two drift snapshots and fails closed when a change would block the \
statement-preservation authority gate. Blocking drift exits non-zero: \
`--allow-weaker` and `--allow-authority-gate-blocking` are explicit escape \
hatches for reviewed changes, never defaults. `--record-attempt --root \
<project>` appends the exact snapshot-bound gate result to the Mathverse \
attempt log under `.mathverse/attempts` and refuses to record from a dirty \
git worktree. `--json` emits the full gate report, drift summary, and \
authority receipt for release automation.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[
            Example {
                cmd: "clean drift diff before.json after.json --json",
                what: "compare two snapshots and fail closed on blocking drift",
            },
            Example {
                cmd: "clean drift diff before.json after.json --record-attempt --root . --json",
                what: "compare two snapshots and record the authority-gate result",
            },
        ],
        see_also: &["drift snapshot", "attempts list"],
        references: &[DRIFT_CRATE_REF],
        domain_root: Some("drift"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// Drift snapshot and statement-preservation subcommands.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum DriftCommands {
    /// Write the current kernel environment declaration snapshot as JSON.
    Snapshot {
        /// Output JSON snapshot path.
        #[arg(short, long)]
        output: PathBuf,
        /// Lake project root to snapshot. When omitted, snapshots the loaded
        /// environment supplied by the parent command or the Clean prelude.
        #[arg(long, value_name = "PROJECT")]
        project: Option<PathBuf>,
        /// Restrict a project snapshot to one module. May be repeated.
        #[arg(long = "module", value_name = "MODULE")]
        modules: Vec<String>,
        /// Emit a JSON command report.
        #[arg(long)]
        json: bool,
    },
    /// Compare two JSON snapshot files.
    Diff {
        /// Baseline snapshot JSON path.
        before: PathBuf,
        /// Candidate snapshot JSON path.
        after: PathBuf,
        /// Allow statement changes classified as weaker.
        #[arg(long)]
        allow_weaker: bool,
        /// Allow drift that would block statement-preservation authority gates.
        #[arg(long)]
        allow_authority_gate_blocking: bool,
        /// Append the statement-preservation gate result as a Mathverse proof attempt.
        #[arg(long)]
        record_attempt: bool,
        /// Repository or project root containing the `.mathverse` attempt log.
        #[arg(long, default_value = ".")]
        root: PathBuf,
        /// Emit a JSON command report.
        #[arg(long)]
        json: bool,
    },
}

/// Command report for `clean drift snapshot`.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DriftSnapshotCommandReport {
    pub ok: bool,
    pub output: String,
    pub declarations: usize,
}

/// Command report for `clean drift diff`.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DriftDiffCommandReport {
    pub ok: bool,
    pub authority_gate_accepted: bool,
    pub before: String,
    pub after: String,
    pub allow_weaker: bool,
    pub allow_authority_gate_blocking: bool,
    pub authority_gate_blocking_reports: usize,
    pub has_authority_gate_blocking: bool,
    pub statement_preservation: StatementPreservationGateReport,
    pub summary: DriftSummary,
    pub reports: Vec<DriftReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authority_receipt: Option<AuthorityReceipt>,
}

/// Dispatch entry point for `clean drift`.
///
/// `env` is an already-loaded environment supplied by a parent command; when
/// it is `None` and no `--project` is given, the Clean prelude environment is
/// snapshotted instead.
pub(crate) fn handle_drift_command(
    command: DriftCommands,
    env: Option<&Environment>,
) -> anyhow::Result<()> {
    match command {
        DriftCommands::Snapshot {
            output,
            project,
            modules,
            json,
        } => {
            let project_env;
            let prelude_env;
            let env = if let Some(project) = project {
                project_env =
                    crate::cmd_audit::load_lake_project_source_environment(&project, &modules)?;
                &project_env
            } else if !modules.is_empty() {
                bail!("clean drift snapshot --module requires --project");
            } else if let Some(env) = env {
                env
            } else {
                prelude_env =
                    Environment::try_with_prelude().unwrap_or_else(|_| Environment::new());
                &prelude_env
            };
            let report = snapshot(env, &output)?;
            print_snapshot_report(&report, json)
        }
        DriftCommands::Diff {
            before,
            after,
            allow_weaker,
            allow_authority_gate_blocking,
            record_attempt,
            root,
            json,
        } => {
            let started = Instant::now();
            let source_guard = if record_attempt {
                Some(AuthoritySourceGuard::capture_clean(
                    &root,
                    "clean drift diff --record-attempt",
                )?)
            } else {
                None
            };
            let mut report =
                diff_report(&before, &after, allow_weaker, allow_authority_gate_blocking)?;
            if record_attempt {
                if let Some(source_guard) = source_guard.as_ref() {
                    source_guard.ensure_unchanged("authority evidence write")?;
                }
                let wall_time_ms = elapsed_millis_saturating(started);
                let attempt = record_statement_preservation_authority_gate_attempt(
                    &root,
                    &report.statement_preservation,
                    wall_time_ms,
                )
                .with_context(|| {
                    format!(
                        "failed to record statement-preservation authority-gate attempt under {}",
                        root.display()
                    )
                })?;
                report.authority_receipt = Some(AuthorityReceipt::from_attempt(&attempt));
            }
            print_diff_report(&report, json)?;
            // Report first, then fail: the operator sees the evidence even when
            // the gate blocks and the process exits non-zero.
            fail_on_disallowed_drift(&report)
        }
    }
}

/// Write `env` to `output` as a drift JSON snapshot.
fn snapshot(
    env: &Environment,
    output: impl AsRef<Path>,
) -> anyhow::Result<DriftSnapshotCommandReport> {
    let output = output.as_ref();
    let snapshot = drift::snapshot(env);
    save_snapshot_json(&snapshot, output)
        .with_context(|| format!("failed to write drift snapshot {}", output.display()))?;

    Ok(DriftSnapshotCommandReport {
        ok: true,
        output: display_path(output),
        declarations: snapshot.len(),
    })
}

fn elapsed_millis_saturating(started: Instant) -> u64 {
    started.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

fn diff_report(
    before: impl AsRef<Path>,
    after: impl AsRef<Path>,
    allow_weaker: bool,
    allow_authority_gate_blocking: bool,
) -> anyhow::Result<DriftDiffCommandReport> {
    let before = before.as_ref();
    let after = after.as_ref();
    let before_snapshot = read_snapshot(before)?;
    let after_snapshot = read_snapshot(after)?;
    let reports = drift::diff(&before_snapshot, &after_snapshot);
    let statement_preservation =
        drift::statement_preservation_gate_report_for_snapshots(&before_snapshot, &after_snapshot);
    let summary = DriftSummary::from_reports(&reports);
    let authority_gate_blocking_reports = statement_preservation.blocking_reports.len();
    let has_authority_gate_blocking = authority_gate_blocking_reports > 0;
    let ok = (allow_weaker || !summary.has_weaker_drift())
        && (allow_authority_gate_blocking || !has_authority_gate_blocking);

    Ok(DriftDiffCommandReport {
        ok,
        authority_gate_accepted: statement_preservation.accepted,
        before: display_path(before),
        after: display_path(after),
        allow_weaker,
        allow_authority_gate_blocking,
        authority_gate_blocking_reports,
        has_authority_gate_blocking,
        statement_preservation,
        summary,
        reports,
        authority_receipt: None,
    })
}

fn read_snapshot(path: &Path) -> anyhow::Result<EnvSnapshot> {
    load_snapshot_json(path)
        .with_context(|| format!("failed to read drift snapshot {}", path.display()))
}

/// Fail-closed exit-code path for `clean drift diff`.
///
/// Blocking statement-preservation drift and weaker statements each produce a
/// non-zero exit unless the operator opted in explicitly. Never relax this: the
/// whole point of the gate is that a caller inspecting only the status code
/// cannot mistake a broken statement-preservation comparison for a clean one.
fn fail_on_disallowed_drift(report: &DriftDiffCommandReport) -> anyhow::Result<()> {
    if report.has_authority_gate_blocking && !report.allow_authority_gate_blocking {
        bail!(
            "authority-gate blocking drift detected in {} report(s); pass --allow-authority-gate-blocking to accept",
            report.authority_gate_blocking_reports
        );
    }

    if report.summary.has_weaker_drift() && !report.allow_weaker {
        bail!(
            "weaker drift detected in {} statement(s); pass --allow-weaker to accept",
            report.summary.weaker_statements
        );
    }
    Ok(())
}

fn print_snapshot_report(report: &DriftSnapshotCommandReport, json: bool) -> anyhow::Result<()> {
    if json {
        print_json(report)
    } else {
        println!("Wrote drift snapshot: {}", report.output);
        println!("  declarations: {}", report.declarations);
        Ok(())
    }
}

fn print_diff_report(report: &DriftDiffCommandReport, json: bool) -> anyhow::Result<()> {
    if json {
        print_json(report)
    } else {
        print_human_diff_report(report);
        Ok(())
    }
}

fn print_json(report: &impl Serialize) -> anyhow::Result<()> {
    println!("{}", serde_json::to_string_pretty(report)?);
    Ok(())
}

fn print_human_diff_report(report: &DriftDiffCommandReport) {
    let summary = report.summary;
    println!("Drift diff: {} report(s)", summary.total_reports);
    println!("  names dropped: {}", summary.names_dropped);
    println!("  names added: {}", summary.names_added);
    println!(
        "  statement_preservation: {:?} (blocking: {})",
        report.statement_preservation.status, report.authority_gate_blocking_reports
    );
    if let Some(receipt) = &report.authority_receipt {
        println!("  attempt_id: {}", receipt.attempt_id);
        if let Some(artifact) = &receipt.solver_artifact {
            println!("  solver_artifact: {}", artifact.blake3);
        }
    }
    println!(
        "  statements changed: {} (weaker: {}, stronger: {}, incomparable: {}, renamed: {})",
        summary.statements_changed,
        summary.weaker_statements,
        summary.stronger_statements,
        summary.incomparable_statements,
        summary.renamed_statements
    );
    println!("  universes changed: {}", summary.universes_changed);
    println!("  imports changed: {}", summary.imports_changed);
    println!("  hypotheses changed: {}", summary.hypotheses_changed);

    for report in &report.reports {
        print_human_drift_report(report);
    }
}

fn print_human_drift_report(report: &DriftReport) {
    match report {
        DriftReport::NameDropped(name) => println!("  dropped: {name}"),
        DriftReport::NameAdded(name) => println!("  added: {name}"),
        DriftReport::StatementChanged { name, kind, .. } => {
            println!("  statement changed: {name} ({kind:?})");
        }
        DriftReport::UniverseChanged { name, .. } => {
            println!("  universes changed: {name}");
        }
        DriftReport::ImportsChanged {
            name,
            added,
            removed,
        } => {
            println!(
                "  imports changed: {name} (+{}, -{})",
                added.len(),
                removed.len()
            );
        }
        DriftReport::HypothesesChanged { name, diff } => {
            println!(
                "  hypotheses changed: {name} (+{}, -{})",
                diff.added.len(),
                diff.removed.len()
            );
        }
    }
}

fn display_path(path: &Path) -> String {
    path.display().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{ConstantKind, Name};
    use clean_mathverse::drift::{
        DeclSnapshot, UniverseSig, STATEMENT_PRESERVATION_AUTHORITY_GATE,
    };
    use std::collections::BTreeMap;

    #[test]
    fn diff_report_exposes_authority_gate_blocking_drift() {
        let dir = tempfile::tempdir().expect("temp dir");
        let before = dir.path().join("before.json");
        let after = dir.path().join("after.json");
        write_snapshot(&before, snapshot_with_decl("Drift.blocking"));
        write_snapshot(&after, EnvSnapshot::default());

        let report = diff_report(&before, &after, false, false).expect("diff report");

        assert!(!report.ok);
        assert!(!report.authority_gate_accepted);
        assert_eq!(report.authority_gate_blocking_reports, 1);
        assert!(report.has_authority_gate_blocking);
        assert!(!report.statement_preservation.accepted);
        assert_eq!(report.summary.names_dropped, 1);
    }

    #[test]
    fn blocking_drift_requires_explicit_authority_gate_allow_flag() {
        let dir = tempfile::tempdir().expect("temp dir");
        let before = dir.path().join("before.json");
        let after = dir.path().join("after.json");
        write_snapshot(&before, snapshot_with_decl("Drift.blocking"));
        write_snapshot(&after, EnvSnapshot::default());

        let denied = diff_report(&before, &after, true, false).expect("denied report");
        let err = fail_on_disallowed_drift(&denied).expect_err("blocking drift is denied");
        assert!(
            err.to_string().contains("authority-gate blocking drift"),
            "unexpected error: {err:#}"
        );

        let allowed = diff_report(&before, &after, true, true).expect("allowed report");
        assert!(allowed.ok);
        assert!(!allowed.authority_gate_accepted);
        fail_on_disallowed_drift(&allowed).expect("blocking drift allowed");
    }

    #[test]
    fn exact_match_stays_allowed_without_authority_gate_flag() {
        let dir = tempfile::tempdir().expect("temp dir");
        let before = dir.path().join("before.json");
        let after = dir.path().join("after.json");
        let snapshot = snapshot_with_decl("Drift.same");
        write_snapshot(&before, snapshot.clone());
        write_snapshot(&after, snapshot);

        let report = diff_report(&before, &after, false, false).expect("diff report");

        assert!(report.ok);
        assert!(report.authority_gate_accepted);
        assert_eq!(report.authority_gate_blocking_reports, 0);
        assert!(!report.has_authority_gate_blocking);
        assert!(report.statement_preservation.accepted);
        assert_eq!(report.summary.total_reports, 0);
        fail_on_disallowed_drift(&report).expect("exact match allowed");
    }

    #[test]
    fn recorded_drift_attempt_serializes_authority_receipt_shape() {
        let dir = tempfile::tempdir().expect("temp dir");
        let before = dir.path().join("before.json");
        let after = dir.path().join("after.json");
        let snapshot = snapshot_with_decl("Drift.same");
        write_snapshot(&before, snapshot.clone());
        write_snapshot(&after, snapshot);
        let report = diff_report(&before, &after, false, false).expect("diff report");

        let attempt = record_statement_preservation_authority_gate_attempt(
            dir.path(),
            &report.statement_preservation,
            37,
        )
        .expect("record statement-preservation authority gate");
        let receipt = AuthorityReceipt::from_attempt(&attempt);
        let json = serde_json::to_value(&receipt).expect("receipt serializes");

        assert!(json["attempt_id"].as_str().is_some());
        assert_eq!(
            json["authority_gate"],
            STATEMENT_PRESERVATION_AUTHORITY_GATE
        );
        assert_eq!(json["status"], "accepted");
        assert!(json["goal_hash"].as_str().is_some());
        assert!(json["trust_audit_hash"].as_str().is_some());
        assert_eq!(json["solver_artifact"]["blake3"], json["trust_audit_hash"]);
    }

    #[test]
    fn snapshot_rejects_module_filter_without_project() {
        let dir = tempfile::tempdir().expect("temp dir");
        let err = handle_drift_command(
            DriftCommands::Snapshot {
                output: dir.path().join("snapshot.json"),
                project: None,
                modules: vec!["A".to_string()],
                json: false,
            },
            None,
        )
        .expect_err("module filters require a project root");

        assert!(
            err.to_string()
                .contains("clean drift snapshot --module requires --project"),
            "unexpected error: {err:#}"
        );
    }

    fn write_snapshot(path: &Path, snapshot: EnvSnapshot) {
        save_snapshot_json(&snapshot, path).expect("save snapshot");
    }

    fn snapshot_with_decl(name: &str) -> EnvSnapshot {
        let name = Name::from_string(name);
        let decl = DeclSnapshot {
            name: name.clone(),
            kind: ConstantKind::Theorem,
            statement_hash: hash(1),
            hyp_list_hash: hash(2),
            hypotheses: Vec::new(),
            conclusion_hash: hash(3),
            universe_sig: UniverseSig {
                params: Vec::new(),
                hash: hash(4),
            },
            imports: Vec::new(),
            imports_hash: hash(5),
        };

        EnvSnapshot {
            declarations: BTreeMap::from([(name, decl)]),
        }
    }

    fn hash(byte: u8) -> [u8; 32] {
        [byte; 32]
    }
}
