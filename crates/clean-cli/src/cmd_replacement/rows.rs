// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-first tooling status, Python migration rows, and replacement rows.

use super::*;
use std::sync::OnceLock;

/// Where the scorecard's human-readable prose lives — `data/`, not this crate.
///
/// Every non-test `.rs` file under `crates/clean-cli/src/cmd_replacement/` is
/// hashed by [`sha256_repo_module_tree`] into
/// `reports/kernel-soundness-launch-evidence.json`, and
/// `validate_trust_core_module_tree_sha` rejects that artifact the moment the
/// digest moves. Measured by substitution over HEAD content on 2026-08-26:
/// correcting the single stale phrase `while remaining blockers fail closed`
/// inside one row's `blocker` sentence moved the digest
/// `2a091c02…` → `5d83d13a…`. So the repo answered a *prose* fix with an amber
/// `kernel-differential` row and a re-mint needing a HEAD-built binary plus the
/// cargo lanes — which is precisely why this surface's prose rotted while its
/// logic stayed maintained.
///
/// The fix is deliberately **not** to teach the digest to skip anything. It
/// still hashes every byte of every non-test `.rs` file here, so any real logic
/// change still stales the evidence. The prose merely moved to `data/`, which
/// the code digest never covered in the first place — the same argument that
/// already excludes `tests/` ("cannot change what the gate does at runtime").
///
/// **Only fields no predicate reads may live here.** Audited 2026-08-26, the
/// decision-bearing fields are `ReplacementRow::{status, required_for_launch,
/// gate_command, evidence_artifact}` (read by `is_wrapper_proof_surface`,
/// `evidence_state_of`, `is_self_reported_gate_command`) and
/// `PythonToolMigrationRow::{command, status, replacement_critical,
/// planned_rust_surface}` (read by `is_python_wrapper_command` and a
/// `starts_with("clean ")`). `blocker` and `removal_condition` reach nothing but
/// `Serialize` derives and `writeln!`. `tests/part_16.rs` re-proves that by
/// mutation rather than asserting it, so a future predicate on either field
/// turns red instead of silently widening this boundary.
pub(crate) const REPLACEMENT_ROW_PROSE_PATH: &str = "data/replacement_row_prose.json";

pub(crate) const REPLACEMENT_ROW_PROSE_SCHEMA_VERSION: &str = "clean-replacement-row-prose-v1";

/// What a row shows when its prose entry is absent. Self-announcing on purpose:
/// an explanation that silently renders empty is how a scorecard row stops
/// meaning anything without anyone noticing.
pub(crate) const MISSING_ROW_PROSE: &str =
    "MISSING PROSE: this row has no entry in data/replacement_row_prose.json. The scorecard is \
     reporting a row whose explanation was never written; `cargo test --locked -p clean-cli \
     --lib row_prose` names every such row.";

#[derive(Debug, Deserialize)]
struct RowProseFile {
    schema_version: String,
    replacement_rows: BTreeMap<String, String>,
    python_tool_rows: BTreeMap<String, PythonToolRowProseEntry>,
}

#[derive(Debug, Deserialize)]
struct PythonToolRowProseEntry {
    removal_condition: String,
    blocker: String,
}

/// The loaded prose, resolved to `'static` once per process.
#[derive(Debug, Default)]
pub(crate) struct RowProse {
    replacement_rows: BTreeMap<&'static str, &'static str>,
    python_tool_rows: BTreeMap<&'static str, (&'static str, &'static str)>,
}

impl RowProse {
    #[cfg(test)]
    pub(crate) fn replacement_row_ids(&self) -> Vec<&'static str> {
        self.replacement_rows.keys().copied().collect()
    }

    #[cfg(test)]
    pub(crate) fn python_tool_row_ids(&self) -> Vec<&'static str> {
        self.python_tool_rows.keys().copied().collect()
    }
}

/// Leak once, at first read, so loaded prose can satisfy the `&'static str` row
/// fields without threading a lifetime through every `Serialize` struct in this
/// module. Bounded by the file: one allocation per entry, once per process.
fn leak_prose(text: String) -> &'static str {
    Box::leak(text.into_boxed_str())
}

pub(crate) fn row_prose() -> &'static RowProse {
    static ROW_PROSE: OnceLock<RowProse> = OnceLock::new();
    ROW_PROSE.get_or_init(|| {
        // Deliberately does not fail closed. This is the *status report*, and
        // refusing to print it because a sentence is missing would trade a
        // documented gap for a dead command. A missing entry surfaces as
        // MISSING_ROW_PROSE on the row itself, and the gate that refuses that
        // is `tests/part_16.rs`, which fails the build instead.
        let Ok(Some(source)) = read_optional_repo_artifact(REPLACEMENT_ROW_PROSE_PATH) else {
            return RowProse::default();
        };
        let Ok(file) = serde_json::from_str::<RowProseFile>(&source) else {
            return RowProse::default();
        };
        if file.schema_version != REPLACEMENT_ROW_PROSE_SCHEMA_VERSION {
            return RowProse::default();
        }
        RowProse {
            replacement_rows: file
                .replacement_rows
                .into_iter()
                .map(|(id, text)| (leak_prose(id), leak_prose(text)))
                .collect(),
            python_tool_rows: file
                .python_tool_rows
                .into_iter()
                .map(|(id, entry)| {
                    (
                        leak_prose(id),
                        (
                            leak_prose(entry.removal_condition),
                            leak_prose(entry.blocker),
                        ),
                    )
                })
                .collect(),
        }
    })
}

/// The `blocker` sentence for a scorecard row.
pub(crate) fn replacement_row_blocker(id: &str) -> &'static str {
    row_prose()
        .replacement_rows
        .get(id)
        .copied()
        .unwrap_or(MISSING_ROW_PROSE)
}

/// The `(removal_condition, blocker)` prose for a Python-migration row.
pub(crate) fn python_tool_row_prose(id: &str) -> (&'static str, &'static str) {
    row_prose()
        .python_tool_rows
        .get(id)
        .copied()
        .unwrap_or((MISSING_ROW_PROSE, MISSING_ROW_PROSE))
}

pub(crate) fn rust_first_tooling_status() -> RustFirstToolingStatus {
    let commands = python_tool_migration_rows();
    let launch_ready = commands.iter().all(|row| {
        row.status == ToolMigrationStatus::RustOwned || row.status == ToolMigrationStatus::Demoted
    });
    let overall_status = if launch_ready {
        ToolMigrationStatus::RustOwned
    } else if commands
        .iter()
        .any(|row| row.status == ToolMigrationStatus::MissingOwner)
    {
        ToolMigrationStatus::MissingOwner
    } else {
        ToolMigrationStatus::Transitional
    };

    RustFirstToolingStatus {
        schema_version: "clean-rust-first-tooling-migration-v1",
        issue: IssueRef::new(
            3706,
            "Migrate replacement-critical Python tests and tooling into unified Rust harness",
        ),
        owner_slot: "Slot 6",
        launch_ready,
        overall_status,
        counts: count_tool_migration_status(&commands),
        commands,
    }
}

pub(crate) fn python_tool_migration_rows() -> Vec<PythonToolMigrationRow> {
    vec![
        python_tool_row_with_status_and_criticality(
            "docs-metrics-sync",
            "python3 scripts/sync_readme_metrics.py --check",
            "docs/SOURCE_INVENTORY.md",
            "non-launch diagnostic only; no replacement launch surface required",
            ToolMigrationStatus::Demoted,
            false,
        ),
        python_tool_row_with_status(
            "system-health-release-json",
            "python3 scripts/system_health_check.py --json-output /tmp/clean-system-health-python-fallback.json",
            "docs/RELEASE_READINESS.md",
            "clean factory status --json",
            ToolMigrationStatus::RustOwned,
        ),
        python_tool_row_with_status(
            "trust-boundary-audit-report",
            "python3 scripts/trust_boundary_audit.py",
            "docs/RELEASE_READINESS.md; scripts/trust_boundary_expected_tests.txt",
            "clean replacement trust-boundary-audit --input <TSV> --expected scripts/trust_boundary_expected_tests.txt --json",
            ToolMigrationStatus::RustOwned,
        ),
        python_tool_row_with_status_and_criticality(
            "benchmark-publication-check",
            "python3 scripts/check_benchmark_publication.py --check",
            "docs/plans/LEAN4_REPLACEMENT_PLAN.md; docs/RELEASE_READINESS.md",
            "non-launch diagnostic only; launch benchmark claims remain tracked by benchmark-publication-launch",
            ToolMigrationStatus::Demoted,
            false,
        ),
        python_tool_row_with_status_and_criticality(
            "benchmark-publication-launch",
            "python3 scripts/check_benchmark_publication.py --check --launch",
            "docs/RELEASE_READINESS.md; reports/benchmarks/publication/current.json; scripts/check_benchmark_publication.py",
            "clean bench publication-check --launch --json (accepted benchmark lane; non-launch diagnostic for Lean4 replacement readiness)",
            ToolMigrationStatus::Demoted,
            false,
        ),
        python_tool_row_with_status_and_criticality(
            "release-issue-hygiene",
            "python3 scripts/release_issue_hygiene.py --fetch",
            "docs/RELEASE_READINESS.md; scripts/release_issue_hygiene.py",
            "clean replacement release-issue-hygiene --fetch --json or --input <snapshot> --json (Rust-owned read-only live gh issue list fetch and offline snapshot parser; replacement status JSON alone is not sufficient)",
            ToolMigrationStatus::RustOwned,
            true,
        ),
        python_tool_row_with_status_and_criticality(
            "mathverse-download-pytest",
            "retired: tests/test_download_mathverse_library.py (never tracked)",
            "docs/RELEASE_READINESS.md",
            "clean mathverse download --version <version> --output-dir <dir> --json verified launch gate with exact mathverse-library-v<version>.tar.zst asset selection, temp extraction failure reporting, manifest checksum verification, zero-shard/manifest drift rejection, and stale-shard cleanup",
            ToolMigrationStatus::RustOwned,
            true,
        ),
    ]
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) fn python_tool_row(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
) -> PythonToolMigrationRow {
    python_tool_row_with_status(
        id,
        command,
        source_artifact,
        planned_rust_surface,
        ToolMigrationStatus::Transitional,
    )
}

pub(crate) fn python_tool_row_with_status(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
    status: ToolMigrationStatus,
) -> PythonToolMigrationRow {
    python_tool_row_with_status_and_criticality(
        id,
        command,
        source_artifact,
        planned_rust_surface,
        status,
        true,
    )
}

pub(crate) fn python_tool_row_with_status_and_criticality(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
    status: ToolMigrationStatus,
    replacement_critical: bool,
) -> PythonToolMigrationRow {
    // Prose is data, not code — see REPLACEMENT_ROW_PROSE_PATH.
    let (removal_condition, blocker) = python_tool_row_prose(id);
    PythonToolMigrationRow {
        id,
        command,
        source_artifact,
        replacement_critical,
        owner_slot: "Slot 6",
        issue: IssueRef::new(
            3706,
            "Migrate replacement-critical Python tests and tooling into unified Rust harness",
        ),
        status,
        planned_rust_surface,
        removal_condition,
        blocker,
    }
}

pub(crate) fn replacement_rows() -> Vec<ReplacementRow> {
    vec![
        row(
            "scorecard",
            "Replacement scorecard",
            "Slot 6",
            IssueRef::new(3704, "Rust-first testing/tooling, scorecards, merge queue, and evidence dashboards"),
            ReplacementStatus::InProgress,
            // NOT `clean replacement status --json`: that command PRINTS this
            // row, so citing it made the row its own evidence. The scorecard's
            // invariants are checked by an independent harness instead.
            "cargo test --locked -p clean-cli --lib cmd_replacement",
            "clean-replacement-status-v1",
            replacement_row_blocker("scorecard"),
        ),
        row(
            "proof-system-certification",
            "Proof-system certification",
            "Slot 1",
            IssueRef::new(3697, "clean proof system: zero-trust kernel, Mathverse, and replay certification"),
            ReplacementStatus::InProgress,
            "clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json --json && clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json --json && clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            TRUST_CORE_EVIDENCE_SCHEMA_VERSION,
            replacement_row_blocker("proof-system-certification"),
        ),
        row(
            "fallback-denial",
            "Trusted fallback denial",
            "Slot 1",
            IssueRef::new(3705, "Zero-trust gate forbids sorryAx and trusted fallback constructors"),
            ReplacementStatus::Green,
            "clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            "reports/deny-sorry-launch-evidence.json",
            replacement_row_blocker("fallback-denial"),
        ),
        row(
            "frontend-parity",
            "Lean4 surface and elaboration parity",
            "Slot 2",
            IssueRef::new(3700, "Lean4 surface language, elaboration, macros, and diagnostics parity"),
            ReplacementStatus::InProgress,
            "clean replacement validate-report --report tests/lean4_compat/frontend_replacement_scorecard.json --kind frontend-parity --json && cargo test --locked -p clean-elab --test integration lean4_frontend_replacement_scorecard -- --nocapture",
            "tests/lean4_compat/frontend_replacement_scorecard.json",
            replacement_row_blocker("frontend-parity"),
        ),
        row(
            "kernel-differential",
            "Kernel differential parity",
            "Slot 1",
            IssueRef::new(3699, "Proof-system replacement certification and zero-trust gates"),
            ReplacementStatus::Green,
            "clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            "reports/kernel-soundness-launch-evidence.json",
            replacement_row_blocker("kernel-differential"),
        ),
        row(
            "tactic-parity",
            "Lean4 tactic parity and automation",
            "Slot 3",
            IssueRef::new(3711, "Lean4 tactic parity matrix and corpus gates"),
            ReplacementStatus::Green,
            "clean replacement tactic-parity --json",
            "reports/tactic-parity-counts.json",
            replacement_row_blocker("tactic-parity"),
        ),
        row(
            "strict-reconstruction",
            "Solver and automation reconstruction",
            "Slot 3",
            IssueRef::new(3712, "Strict solver-fragment reconstruction dashboard"),
            ReplacementStatus::Green,
            "clean replacement tactic-parity --json",
            "reports/strict-solver-fragment-dashboard.json",
            replacement_row_blocker("strict-reconstruction"),
        ),
        row(
            "native-libraries",
            "Native Init, Std, and core Mathlib replacement",
            "Slot 4",
            IssueRef::new(3713, "Native Init, Std, and core Mathlib replacement scorecards"),
            ReplacementStatus::InProgress,
            "clean replacement validate-report --report reports/native-library-replacement.json --kind native-library --json && clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json && clean replacement native-library api-slice --slice nat-arithmetic --json && clean replacement native-library api-slice --slice nat-bitwise --json && clean replacement native-library api-slice --slice bool-nat-ext --json && clean replacement native-library api-slice --slice string-ext --json && clean replacement native-library api-slice --slice string-core --json && clean replacement native-library api-slice --slice string-transform --json && clean replacement native-library api-slice --slice string-hash --json && clean replacement native-library api-slice --slice name-core --json && clean replacement native-library api-slice --slice decidable-core --json && clean replacement native-library api-slice --slice decidable-eq-aliases --json && clean replacement native-library api-slice --slice int-order-decidable --json && clean replacement native-library api-slice --slice signed-decidable-eq-aliases --json && clean replacement native-library api-slice --slice hetero-ops --json && clean replacement native-library api-slice --slice beq-shortcircuit --json && clean replacement native-library api-slice --slice decidable-combinators --json && clean replacement native-library api-slice --slice nat-order-decidable --json && clean replacement native-library api-slice --slice char-core --json && clean replacement native-library api-slice --slice uint-of-nat --json && clean replacement native-library api-slice --slice fin-val --json && clean replacement native-library api-slice --slice uint-narrowing --json && clean replacement native-library api-slice --slice uint-widening --json && clean replacement native-library api-slice --slice bitvec-core --json && clean replacement native-library api-slice --slice uint-bitvec --json && clean replacement native-library api-slice --slice signed-bitvec --json && clean replacement native-library api-slice --slice uint8-core --json && clean replacement native-library api-slice --slice uint16-core --json && clean replacement native-library api-slice --slice uint32-core --json && clean replacement native-library api-slice --slice uint64-core --json && clean replacement native-library api-slice --slice usize-core --json && clean replacement native-library api-slice --slice uint8-bitwise --json && clean replacement native-library api-slice --slice uint16-bitwise --json && clean replacement native-library api-slice --slice uint32-bitwise --json && clean replacement native-library api-slice --slice uint64-bitwise --json && clean replacement native-library api-slice --slice usize-bitwise --json && clean replacement native-library api-slice --slice platform-core --json && clean replacement native-library api-slice --slice float-core --json && clean replacement native-library api-slice --slice float-classification --json && clean replacement native-library api-slice --slice float-functions --json && clean replacement native-library api-slice --slice float-input-conversions --json && clean replacement native-library api-slice --slice float-formatting --json && clean replacement native-library api-slice --slice float-output-conversions --json && clean replacement native-library api-slice --slice int-core --json && clean replacement native-library api-slice --slice int8-core --json && clean replacement native-library api-slice --slice int16-core --json && clean replacement native-library api-slice --slice int32-core --json && clean replacement native-library api-slice --slice int64-core --json && clean replacement native-library api-slice --slice isize-core --json && clean replacement native-library mathlib-api --expect-blocked --json && cargo test --locked -p clean-kernel native_reducers --lib",
            "reports/native-library-replacement.json",
            replacement_row_blocker("native-libraries"),
        ),
        row(
            "mathverse-replay",
            "Mathverse search-to-verify-to-apply replay",
            "Slot 4",
            IssueRef::new(3714, "Mathverse search-to-verify-to-apply replay acceptance gate"),
            ReplacementStatus::InProgress,
            "clean mathverse replay-corpus --production --json --output reports/mathverse-replay-production-corpus.json && clean mathverse validate-replay-report --report reports/mathverse-replay-replacement.json --corpus reports/mathverse-replay-production-corpus.json && CARGO_TARGET_DIR=/tmp/clean-mathverse-native-gate-target cargo test --locked -p clean-mathverse --test native_gate_integration && cargo test --locked -p clean-elab --lib --features mathverse-library native_replay_gate -- --nocapture",
            "reports/mathverse-replay-replacement.json",
            replacement_row_blocker("mathverse-replay"),
        ),
        row(
            "lake-workflow",
            "clean-owned Lake workflow",
            "Slot 5",
            IssueRef::new(3707, "Lake replacement mode removes Lean4 process delegation"),
            ReplacementStatus::InProgress,
            "clean lake smoke --report reports/lake-replacement-smoke.json",
            "reports/lake-replacement-smoke.json",
            replacement_row_blocker("lake-workflow"),
        ),
        row(
            "compile-runtime",
            "Compiler/runtime/eval closure",
            "Slot 5",
            IssueRef::new(3708, "Restore clean compile file-to-executable pipeline"),
            // Measured 2026-09-25 (P0_EXEC): this row was Green on an emit-C
            // smoke that links, runs and compares nothing, while `clean run`
            // printed wrong answers at exit 0 (`(7 : Int) / 2` gave `0`, both
            // arms of a non-final `if` ran). It is now backed by the byte-exact
            // differential battery against pinned Lean, whose gate is
            // FAIL-CLOSEDNESS -- every program byte-identical or refused by
            // name -- not parity, so the row is InProgress until parity is
            // what the battery measures.
            ReplacementStatus::InProgress,
            "cargo test --locked -p clean --test native_exec_battery",
            "reports/native-exec-battery.json",
            replacement_row_blocker("compile-runtime"),
        ),
        row(
            "lsp-infoview",
            "LSP and infoview parity",
            "Slot 5",
            IssueRef::new(3709, "clean LSP infoview parity from clean elaboration state"),
            ReplacementStatus::PendingEvidence,
            "cargo test --locked -p clean-lsp --lib",
            "reports/lsp-infoview-parity.json",
            replacement_row_blocker("lsp-infoview"),
        ),
        row(
            "rust-first-tooling",
            "Rust-first replacement gates",
            "Slot 6",
            IssueRef::new(3706, "Migrate replacement-critical Python tests and tooling into unified Rust harness"),
            // Measured 2026-08-26, not assumed: every one of the seven
            // migration lanes is RustOwned or Demoted, so
            // `rust_first_tooling_status()` computes launch_ready=true,
            // overall_status=rust_owned, counts {demoted:3, rust_owned:4} and
            // launch_blocking_python_wrapper_count=0. `Blocked` with "while
            // remaining blockers fail closed" contradicted every one of those.
            // What is genuinely outstanding is evidence, not work: the artifact
            // was minted at 1f1075c9d, not at HEAD.
            ReplacementStatus::PendingEvidence,
            // Taken from the const the emitter itself writes into the artifact,
            // so the row and reports/rust-first-tooling.json cannot drift apart.
            RUST_FIRST_TOOLING_GATE_COMMAND,
            RUST_FIRST_TOOLING_EVIDENCE_PATH,
            replacement_row_blocker("rust-first-tooling"),
        ),
        row(
            "launch-docs",
            "Public launch and docs claim gate",
            "Slot 6",
            IssueRef::new(3698, "clean full Lean4 ecosystem replacement"),
            ReplacementStatus::Blocked,
            "clean release readiness-smoke --clean-clone-lite --launch --evidence /tmp/clean-release.json",
            "docs/RELEASE_READINESS.md; reports/benchmarks/publication/current.json",
            replacement_row_blocker("launch-docs"),
        ),
    ]
}
