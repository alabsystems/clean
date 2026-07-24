// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for every `clean olean <verb>` subcommand.
//!
//! The top-level binary registers these via
//! `v.extend(clean_olean::cli::FEATURES)` in `clean-cli`'s `registry.rs`.
//! Keep the path segments in sync with the clap tree defined in
//! [`super::OleanCommands`]; the drift tests in
//! `crates/clean-cli/tests/feature_coverage.rs` enforce this contract.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const UNIFIED_CLI_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ORPHAN_INVENTORY_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "CLI orphan inventory — .olean binary absorption",
    target: "designs/2026-04-18-cli-orphan-inventory.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3441: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb verify_olean_batch into clean olean verify-batch",
    target: "#3441",
};

const ISSUE_3442: Reference = Reference {
    kind: RefKind::Issue,
    label: "Absorb generate_namespace_overlay into `clean olean generate-overlay`",
    target: "#3442",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-olean",
    target: "clean-olean",
};

const GENERATE_OVERLAY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "generate-overlay"],
    summary: "Generate namespace overlay payload modules for `clean-kernel`",
    description:
        "Snapshots declaration payloads (`ConstantInfo`) from a source environment, \
         filters by namespace prefix, and emits deterministic Rust modules under the \
         requested `--output-dir` (typically `crates/clean-kernel/src/env/generated/`). \
         The source environment can be built from stdlib `.olean` modules \
         (`--module Init.Core --module Std.Data.List`) and/or seeded with the kernel's \
         `Topology.Manifold` / `Topology.LieGroup` helpers via `--seed-topology-env`. \
         Each namespace produces a `<module>.rs` alongside a bincode `<module>.payload.bin`; \
         a top-level `mod.rs` lists every emitted module. Absorbs the deprecated \
         `generate_namespace_overlay` standalone binary (#3442, Epic #3436).",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean generate-overlay --output-dir crates/clean-kernel/src/env/generated --namespace Topology.Manifold --seed-topology-env",
            what: "Seed Topology.Manifold from kernel init paths and emit the overlay module.",
        },
        Example {
            cmd: "clean olean generate-overlay --output-dir out --namespace Mathlib.Algebra --module Mathlib.Algebra.Basic --search-path /lean/lib",
            what: "Snapshot a Mathlib namespace from an explicit `.olean` search path.",
        },
    ],
    see_also: &[],
    references: &[
        UNIFIED_CLI_REF,
        ORPHAN_INVENTORY_REF,
        ISSUE_3436,
        ISSUE_3442,
        CRATE_REF,
    ],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const VERIFY_BATCH_DESCRIPTION: &str = "\
Type-check every `.olean` module in a directory using a shared cumulative \
kernel environment.

Walks the directory recursively, extracts import declarations from each \
`.olean`, topologically sorts the modules, and loads them one-by-one into a \
single `Environment`. Each module's newly-added constants are type-checked \
before the next module is loaded. Pass `--isolated` to fall back to the legacy \
per-module verification path (useful for bisecting missing dependencies). Pass \
`--parallel N` to type-check each module's new constants with N threads.

The `--cache-file` option enables incremental verification: modules whose file \
content hash matches the cache are skipped during type-checking (the load step \
still runs because subsequent modules depend on their declarations). The cache \
is updated and saved on exit.

Pass `--json` to emit a structured `ExtendedBatchSummary` JSON report to \
stdout. `--json-report <FILE>` additionally writes a comprehensive \
`VerificationReport` to disk, suitable for automation artifact collection.

Part of Epic #3436 (unified `clean` CLI feature index). Absorbs the legacy \
standalone `verify_olean_batch` binary.
";

const VERIFY_BATCH_EXAMPLES: &[Example] = &[
    Example {
        cmd: "clean olean verify-batch /path/to/olean/dir",
        what: "cumulative type-check every module in the directory",
    },
    Example {
        cmd: "clean olean verify-batch /tmp/oleans --parallel 8 --json-report report.json",
        what: "parallel type-check with 8 threads and write a structured JSON report",
    },
    Example {
        cmd: "clean olean verify-batch /tmp/oleans --cache-file verify.cache --load-only",
        what: "load-only pass with incremental cache (no type-checking)",
    },
];

const VERIFY_BATCH_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "verify-batch"],
    summary: "Batch type-check every `.olean` module in a directory",
    description: VERIFY_BATCH_DESCRIPTION,
    category: Category::Verification,
    stability: Stability::Usable,
    examples: VERIFY_BATCH_EXAMPLES,
    see_also: &[],
    references: &[
        ORPHAN_INVENTORY_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3441,
        CRATE_REF,
    ],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

const IMPORT_REVERIFY_METRIC_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["olean", "import-reverify-metric"],
    summary: "Measure + ratchet the fraction of imported constants the kernel re-verifies",
    description: "Loads the requested bootstrap module closure (`--module Init`, \
         optionally `--module Std`; transitive imports load automatically), runs \
         the kernel's `add_decl`-equivalent re-check over exactly those imported \
         constants, and writes `{total_imported, reverified, fraction, ...}` to a \
         JSON metric file (default `data/import_reverification_metric.json`). \
         The write RATCHETS: a measurement whose fraction regresses below the \
         recorded baseline for the same `--lane` is refused, turning the \
         import-trust residual into a measured, monotonically-rising number. \
         Deterministic by default; `--timestamp` stamps the run time. \
         `--max-heartbeats` is a pure resource limit, never a soundness gate.",
    category: Category::Verification,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean olean import-reverify-metric --module Init",
            what: "measure the Init lane and ratchet data/import_reverification_metric.json",
        },
        Example {
            cmd: "clean olean import-reverify-metric --module Init --module Std --lane Init+Std --out target/metric.json",
            what: "measure a wider lane into an explicit metric file",
        },
    ],
    see_also: &["olean verify-batch"],
    references: &[UNIFIED_CLI_REF, ISSUE_3436, CRATE_REF],
    domain_root: Some("olean"),
    alternative_forms: &[],
    feature_gate: None,
};

/// Static feature descriptor array registered by the top-level `clean` CLI.
///
/// Add new verbs here when extending `OleanCommands`; the drift tests in
/// `crates/clean-cli/tests/feature_coverage.rs` fail the build if a clap
/// path is missing from this list (or vice versa).
pub const FEATURES: &[FeatureDescriptor] = &[
    GENERATE_OVERLAY_DESC,
    VERIFY_BATCH_DESC,
    IMPORT_REVERIFY_METRIC_DESC,
];
