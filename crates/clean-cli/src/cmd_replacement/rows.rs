// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-first tooling status, Python migration rows, and replacement rows.

use super::*;

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
            "README.md; docs/DESIGN.md; docs/VERIFICATION_METRICS.md",
            "non-launch diagnostic only; no replacement launch surface required",
            ToolMigrationStatus::Demoted,
            false,
            "Demoted out of replacement launch evidence because README/design/verification metric freshness is not Lean4 replacement-critical.",
            "scripts/sync_readme_metrics.py remains a non-launch diagnostic for public metric freshness and cannot satisfy or block Lean4 replacement readiness.",
        ),
        python_tool_row_with_status(
            "system-health-release-json",
            "python3 scripts/system_health_check.py --json-output /tmp/clean-system-health-python-fallback.json",
            "docs/RELEASE_READINESS.md",
            "clean factory status --json",
            ToolMigrationStatus::RustOwned,
            "The Rust factory status command owns release health JSON, tracked Cargo.lock presence, stale git gc-log detection, local Rust toolchain availability, sibling ay path reachability, and fail-closed ay update freshness.",
            "Primary release health JSON uses clean factory status --json; scripts/system_health_check.py is no longer launch evidence for system health and remains only as a legacy diagnostic.",
        ),
        python_tool_row_with_status(
            "trust-boundary-audit-report",
            "python3 scripts/trust_boundary_audit.py",
            "docs/RELEASE_READINESS.md; scripts/trust_boundary_expected_tests.txt",
            "clean replacement trust-boundary-audit --input <TSV> --expected scripts/trust_boundary_expected_tests.txt --json",
            ToolMigrationStatus::RustOwned,
            "Rust-owned trust-boundary audit summarization parses CLEAN_TRUST_BOUNDARY_AUDIT_PATH TSV records, validates expected-test patterns, groups hits deterministically, reports expected versus unexpected hits, and emits JSON or Markdown without the Python wrapper.",
            "No Python wrapper is required for trust-boundary audit release summarization; scripts/trust_boundary_audit.py remains a legacy diagnostic only.",
        ),
        python_tool_row_with_status_and_criticality(
            "benchmark-publication-check",
            "python3 scripts/check_benchmark_publication.py --check",
            "docs/plans/LEAN4_REPLACEMENT_PLAN.md; docs/RELEASE_READINESS.md",
            "non-launch diagnostic only; launch benchmark claims remain tracked by benchmark-publication-launch",
            ToolMigrationStatus::Demoted,
            false,
            "Demoted out of replacement launch evidence because the ordinary benchmark publication --check lane accepts pending-publication development metadata; launch-critical public performance claims remain tracked by benchmark-publication-launch.",
            "scripts/check_benchmark_publication.py --check remains a non-launch diagnostic for benchmark contract freshness and cannot satisfy or block Lean4 replacement readiness; use benchmark-publication-launch for public performance replacement launch evidence.",
        ),
        python_tool_row_with_status_and_criticality(
            "benchmark-publication-launch",
            "python3 scripts/check_benchmark_publication.py --check --launch",
            "docs/RELEASE_READINESS.md; reports/benchmarks/publication/current.json; scripts/check_benchmark_publication.py",
            "clean bench publication-check --launch --json (accepted benchmark lane; non-launch diagnostic for Lean4 replacement readiness)",
            ToolMigrationStatus::Demoted,
            false,
            "Demoted out of replacement launch evidence because benchmark publication evidence is accepted for this replacement pass; the Rust clean bench publication-check --launch --json surface remains useful audit evidence for published-status, freshness, reachable commits, current-run committed evidence, canonical command/input/artifact coverage, dirty-evidence rejection, required-artifact rejection, and publication_commit artifact hash rejection, but it is not a Lean4 replacement launch blocker.",
            "Accepted benchmark lane: scripts/check_benchmark_publication.py --check --launch and clean bench publication-check --launch --json remain non-launch diagnostic audit checks for benchmark contract freshness and publication parity; they cannot satisfy or block Lean4 replacement readiness in this pass.",
        ),
        python_tool_row_with_status_and_criticality(
            "release-issue-hygiene",
            "python3 scripts/release_issue_hygiene.py --fetch",
            "docs/RELEASE_READINESS.md; scripts/release_issue_hygiene.py",
            "clean replacement release-issue-hygiene --fetch --json or --input <snapshot> --json (Rust-owned read-only live gh issue list fetch and offline snapshot parser; replacement status JSON alone is not sufficient)",
            ToolMigrationStatus::RustOwned,
            true,
            "Rust-owned launch gate: clean replacement release-issue-hygiene --fetch --json runs read-only `gh issue list --state open --limit <N> --json number,title,url,labels,assignees,body,comments`; --input validates offline snapshots with the same comments, watched urgent/P1/blocked/local-maximum labels, owner evidence from assignees or Wn/Rn/Mn/provN labels, body/comment Release decision: evidence, non_ready_issues missing_fields, suggested_actions JSON, and fail-closed malformed-snapshot semantics. clean replacement status --json alone is not sufficient.",
            "No Python wrapper is required for release issue hygiene launch evidence; use the Rust --fetch lane for live evidence and --input for reproducible snapshot review. The gate remains fail-closed on gh failures, malformed snapshots, missing owner evidence, or missing Release decision: notes.",
        ),
        python_tool_row_with_status_and_criticality(
            "mathverse-download-pytest",
            "PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 python3 -m pytest tests/test_download_mathverse_library.py",
            "docs/RELEASE_READINESS.md",
            "clean mathverse download --version <version> --output-dir <dir> --json verified launch gate with exact mathverse-library-v<version>.tar.zst asset selection, temp extraction failure reporting, manifest checksum verification, zero-shard/manifest drift rejection, and stale-shard cleanup",
            ToolMigrationStatus::RustOwned,
            true,
            "Rust-owned Mathverse download verification gate covers the scripts/download_mathverse_library.sh launch contract: rejects missing or wrong-version mathverse-library-v*.tar.zst assets, invalid or zero-shard archives, manifest checksum/aggregate/path mismatches, temp-extract failures, and stale output shards before publishing.",
            "Primary launch evidence is clean mathverse download --version <version> --output-dir <dir> --json plus cmd_mathverse Rust unit coverage; tests/test_download_mathverse_library.py remains a legacy shell-script regression lane, not the replacement launch blocker.",
        ),
    ]
}

pub(crate) fn python_tool_row(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
    removal_condition: &'static str,
    blocker: &'static str,
) -> PythonToolMigrationRow {
    python_tool_row_with_status(
        id,
        command,
        source_artifact,
        planned_rust_surface,
        ToolMigrationStatus::Transitional,
        removal_condition,
        blocker,
    )
}

pub(crate) fn python_tool_row_with_status(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
    status: ToolMigrationStatus,
    removal_condition: &'static str,
    blocker: &'static str,
) -> PythonToolMigrationRow {
    python_tool_row_with_status_and_criticality(
        id,
        command,
        source_artifact,
        planned_rust_surface,
        status,
        true,
        removal_condition,
        blocker,
    )
}

pub(crate) fn python_tool_row_with_status_and_criticality(
    id: &'static str,
    command: &'static str,
    source_artifact: &'static str,
    planned_rust_surface: &'static str,
    status: ToolMigrationStatus,
    replacement_critical: bool,
    removal_condition: &'static str,
    blocker: &'static str,
) -> PythonToolMigrationRow {
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
            "clean replacement status --json",
            "clean-replacement-status-v1",
            "Initial Rust-owned scorecard exists; downstream rows still need generated gate artifacts.",
        ),
        row(
            "proof-system-certification",
            "Proof-system certification",
            "Slot 1",
            IssueRef::new(3697, "clean proof system: zero-trust kernel, Mathverse, and replay certification"),
            ReplacementStatus::InProgress,
            "clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json --json && clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json --json && clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            TRUST_CORE_EVIDENCE_SCHEMA_VERSION,
            "Zero-trust kernel, DENY_SORRY, axiom-audit, and strict reconstruction gates are passed; proof-system certification remains in progress on #464 plus tactic-parity and mathverse-replay blockers in reports/2026-04-27-proof-system-certification-blockers.md.",
        ),
        row(
            "fallback-denial",
            "Trusted fallback denial",
            "Slot 1",
            IssueRef::new(3705, "Zero-trust gate forbids sorryAx and trusted fallback constructors"),
            ReplacementStatus::Green,
            "clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            "reports/deny-sorry-launch-evidence.json",
            "Fresh DENY_SORRY launch evidence passed with the structural/unchecked fallback ratchet at zero; trust-core evidence keeps the checked artifact validated.",
        ),
        row(
            "frontend-parity",
            "Lean4 surface and elaboration parity",
            "Slot 2",
            IssueRef::new(3700, "Lean4 surface language, elaboration, macros, and diagnostics parity"),
            ReplacementStatus::InProgress,
            "clean replacement validate-report --report tests/lean4_compat/frontend_replacement_scorecard.json --kind frontend-parity --json && cargo test --locked -p clean-elab --test integration lean4_frontend_replacement_scorecard -- --nocapture",
            "tests/lean4_compat/frontend_replacement_scorecard.json",
            "Rust-owned frontend scorecard validation now gates stable/canary corpus parse, elab, bounded kernel, trust, diagnostic, and failure classification evidence; full parity remains blocked by missing cross-check artifacts and tactic/macro/import/typeclass/structure coverage.",
        ),
        row(
            "kernel-differential",
            "Kernel differential parity",
            "Slot 1",
            IssueRef::new(3699, "Proof-system replacement certification and zero-trust gates"),
            ReplacementStatus::Green,
            "clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json --json && clean replacement trust-core-evidence --json",
            "reports/kernel-soundness-launch-evidence.json",
            "Fresh kernel soundness launch evidence records differential preflight, Lean4 parity, and file-level soundness passing for this row.",
        ),
        row(
            "tactic-parity",
            "Lean4 tactic parity and automation",
            "Slot 3",
            IssueRef::new(3711, "Lean4 tactic parity matrix and corpus gates"),
            ReplacementStatus::Green,
            "clean replacement tactic-parity --json",
            "reports/tactic-parity-counts.json",
            "Rust-owned tactic matrix and generated Lean4-vs-clean count artifact pass with AESOP, grind, and strict reconstruction representative coverage complete.",
        ),
        row(
            "strict-reconstruction",
            "Solver and automation reconstruction",
            "Slot 3",
            IssueRef::new(3712, "Strict solver-fragment reconstruction dashboard"),
            ReplacementStatus::Green,
            "clean replacement tactic-parity --json",
            "reports/strict-solver-fragment-dashboard.json",
            "Generated strict solver-fragment dashboard gate passes row-count, supported zero-trust, recovery, and residual-trust count checks for the strict reconstruction scope.",
        ),
        row(
            "native-libraries",
            "Native Init, Std, and core Mathlib replacement",
            "Slot 4",
            IssueRef::new(3713, "Native Init, Std, and core Mathlib replacement scorecards"),
            ReplacementStatus::InProgress,
            "clean replacement validate-report --report reports/native-library-replacement.json --kind native-library --json && clean replacement native-library coverage-matrix --check-report reports/native-library-replacement.json --json && clean replacement native-library api-slice --slice nat-arithmetic --json && clean replacement native-library api-slice --slice nat-bitwise --json && clean replacement native-library api-slice --slice bool-nat-ext --json && clean replacement native-library api-slice --slice string-ext --json && clean replacement native-library api-slice --slice string-core --json && clean replacement native-library api-slice --slice string-transform --json && clean replacement native-library api-slice --slice string-hash --json && clean replacement native-library api-slice --slice name-core --json && clean replacement native-library api-slice --slice decidable-core --json && clean replacement native-library api-slice --slice decidable-eq-aliases --json && clean replacement native-library api-slice --slice int-order-decidable --json && clean replacement native-library api-slice --slice signed-decidable-eq-aliases --json && clean replacement native-library api-slice --slice hetero-ops --json && clean replacement native-library api-slice --slice beq-shortcircuit --json && clean replacement native-library api-slice --slice decidable-combinators --json && clean replacement native-library api-slice --slice nat-order-decidable --json && clean replacement native-library api-slice --slice char-core --json && clean replacement native-library api-slice --slice uint-of-nat --json && clean replacement native-library api-slice --slice fin-val --json && clean replacement native-library api-slice --slice uint-narrowing --json && clean replacement native-library api-slice --slice uint-widening --json && clean replacement native-library api-slice --slice bitvec-core --json && clean replacement native-library api-slice --slice uint-bitvec --json && clean replacement native-library api-slice --slice signed-bitvec --json && clean replacement native-library api-slice --slice uint8-core --json && clean replacement native-library api-slice --slice uint16-core --json && clean replacement native-library api-slice --slice uint32-core --json && clean replacement native-library api-slice --slice uint64-core --json && clean replacement native-library api-slice --slice usize-core --json && clean replacement native-library api-slice --slice uint8-bitwise --json && clean replacement native-library api-slice --slice uint16-bitwise --json && clean replacement native-library api-slice --slice uint32-bitwise --json && clean replacement native-library api-slice --slice uint64-bitwise --json && clean replacement native-library api-slice --slice usize-bitwise --json && clean replacement native-library api-slice --slice platform-core --json && clean replacement native-library api-slice --slice float-core --json && clean replacement native-library api-slice --slice float-classification --json && clean replacement native-library api-slice --slice float-functions --json && clean replacement native-library api-slice --slice float-input-conversions --json && clean replacement native-library api-slice --slice float-formatting --json && clean replacement native-library api-slice --slice float-output-conversions --json && clean replacement native-library api-slice --slice int-core --json && clean replacement native-library api-slice --slice int8-core --json && clean replacement native-library api-slice --slice int16-core --json && clean replacement native-library api-slice --slice int32-core --json && clean replacement native-library api-slice --slice int64-core --json && clean replacement native-library api-slice --slice isize-core --json && clean replacement native-library mathlib-api --expect-blocked --json && cargo test --locked -p clean-kernel native_reducers --lib",
            "reports/native-library-replacement.json",
            "Partial native Init/Std reducer, Rust-owned API-slice, and native-shard gate evidence is recorded; Mathlib evidence is compatibility-only and full native Mathlib replacement remains blocked.",
        ),
        row(
            "mathverse-replay",
            "Mathverse search-to-verify-to-apply replay",
            "Slot 4",
            IssueRef::new(3714, "Mathverse search-to-verify-to-apply replay acceptance gate"),
            ReplacementStatus::InProgress,
            "clean mathverse replay-corpus --production --json --output reports/mathverse-replay-production-corpus.json && clean mathverse validate-replay-report --report reports/mathverse-replay-replacement.json --corpus reports/mathverse-replay-production-corpus.json && CARGO_TARGET_DIR=/tmp/clean-mathverse-native-gate-target cargo test --locked -p clean-mathverse --test native_gate_integration && cargo test --locked -p clean-elab --lib --features mathverse-library native_replay_gate -- --nocapture",
            "reports/mathverse-replay-replacement.json",
            "Focused native shard replay, strict search-to-mathverse_use application gate evidence, and generated production-corpus accounting are recorded; 202 corpus obligations are found, but only 3 bounded native-gate verified witnesses, 0 strict mathverse_use applied, 6 rejected, and 193 unsupported.",
        ),
        row(
            "lake-workflow",
            "clean-owned Lake workflow",
            "Slot 5",
            IssueRef::new(3707, "Lake replacement mode removes Lean4 process delegation"),
            ReplacementStatus::InProgress,
            "clean lake init replacement-smoke && clean lake build && clean lake test",
            "reports/lake-replacement-smoke.json",
            "Generated Lake init/build/test smoke passes without Lean4 delegation; full Lake-compatible workflows still must not delegate project semantics to Lean4 and remain limited to bounded native smoke evidence.",
        ),
        row(
            "compile-runtime",
            "Compiler/runtime/eval closure",
            "Slot 5",
            IssueRef::new(3708, "Restore clean compile file-to-executable pipeline"),
            ReplacementStatus::Green,
            "clean compile demos/public/kernel_check_success.lean --decl main --emit c",
            "reports/compile-runtime-smoke.json",
            "Public demo compile smoke emits C for `main` through the clean compiler/runtime path.",
        ),
        row(
            "lsp-infoview",
            "LSP and infoview parity",
            "Slot 5",
            IssueRef::new(3709, "clean LSP infoview parity from clean elaboration state"),
            ReplacementStatus::PendingEvidence,
            "cargo test --locked -p clean-lsp --lib",
            "reports/lsp-infoview-parity.json",
            "Goal state, expected type, diagnostics, hover, completion, goto, references, rename, and code actions need parity evidence.",
        ),
        row(
            "rust-first-tooling",
            "Rust-first replacement gates",
            "Slot 6",
            IssueRef::new(3706, "Migrate replacement-critical Python tests and tooling into unified Rust harness"),
            ReplacementStatus::Blocked,
            "clean replacement status --json",
            "reports/rust-first-tooling.json",
            "Replacement-critical Python and shell gates referenced by launch/replacement evidence are inventoried; release readiness smoke, release issue hygiene, trust-boundary audit, system health, and mathverse download have Rust-owned surfaces while remaining blockers fail closed.",
        ),
        row(
            "launch-docs",
            "Public launch and docs claim gate",
            "Slot 6",
            IssueRef::new(3698, "clean full Lean4 ecosystem replacement"),
            ReplacementStatus::Blocked,
            "clean release readiness-smoke --clean-clone-lite --launch --evidence /tmp/clean-release.json",
            "docs/RELEASE_READINESS.md; reports/benchmarks/publication/current.json",
            "HN launch copy must remain blocked until every required scorecard row is green; refreshed benchmark publication evidence counts only after reports/benchmarks/publication/current.json and the current run artifacts are committed and the launch smoke passes from that release commit.",
        ),
    ]
}
