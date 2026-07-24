// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared clap subcommand tree and feature descriptors for
//! `clean tlaps <verb>`.
//!
//! Part of Epic #3436 (Phase 3 — absorb orphan `tlaps-bench` binary).
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.
//!
//! The top-level `clean` binary re-uses [`TlapsArgs`] / [`TlapsCommands`] to
//! route `clean tlaps bench …` / `clean tlaps validate …` / `clean tlaps show
//! …` into the handler functions that the legacy `tlaps-bench` binary exposed
//! directly. The legacy binary now forwards to the unified entrypoint; see
//! `crates/clean-tla/src/bin/tlaps_bench.rs`.

use std::path::PathBuf;

use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments for `clean tlaps …`.
#[derive(Debug, Args)]
pub struct TlapsArgs {
    /// `tlaps` subcommand (run / validate / show).
    #[command(subcommand)]
    pub command: TlapsCommands,
}

/// Subcommands exposed under `clean tlaps`.
#[derive(Debug, Subcommand)]
pub enum TlapsCommands {
    /// Run a TLAPS benchmark suite.
    Bench(BenchArgs),
    /// Validate benchmark JSON files without running proofs.
    Validate(ValidateArgs),
    /// Show details for a single obligation file.
    Show(ShowArgs),
}

/// Arguments for `clean tlaps bench`.
#[derive(Debug, Args)]
pub struct BenchArgs {
    /// Path to a benchmark directory or a single JSON file.
    #[arg(default_value = "benchmarks/tlaps")]
    pub path: PathBuf,

    /// Show detailed output for each obligation.
    #[arg(short, long)]
    pub verbose: bool,

    /// Emit results as JSON instead of a human-readable summary.
    #[arg(long)]
    pub json: bool,

    /// Restrict output to failing obligations.
    #[arg(long)]
    pub failures_only: bool,
}

/// Arguments for `clean tlaps validate`.
#[derive(Debug, Args)]
pub struct ValidateArgs {
    /// Path to a benchmark directory or a single JSON file.
    #[arg(default_value = "benchmarks/tlaps")]
    pub path: PathBuf,
}

/// Arguments for `clean tlaps show`.
#[derive(Debug, Args)]
pub struct ShowArgs {
    /// Path to the obligation JSON file.
    pub path: PathBuf,
}

const BENCH_DESCRIPTION: &str = "\
Run TLAPS proof-obligation benchmarks via the clean-tla backend.

Accepts either a single obligation JSON file or a directory which will be \
recursively scanned for `*.json` benchmark files. Results are written as a \
summary to stdout; pass `--json` to emit the structured
[`BenchmarkSummary`](crate::bench::BenchmarkSummary) for tooling.

Part of Epic #3436 (unified `clean` CLI) and absorbs the legacy \
`tlaps-bench` binary.
";

const VALIDATE_DESCRIPTION: &str = "\
Parse benchmark JSON files without running any proofs.

Useful as a fast lint step before committing new benchmark fixtures: each \
obligation is loaded, converted to its `TlaObligation` form, and errors are \
reported with the offending path.
";

const SHOW_DESCRIPTION: &str = "\
Print the parsed view of a single TLAPS obligation file.

Includes declarations, hypotheses, goal, parsed obligation classification \
(temporal? induction?), and any parse errors surfaced by the `TlaObligation` \
constructor.
";

const BENCH_EXAMPLES: &[Example] = &[
    Example {
        cmd: "clean tlaps bench benchmarks/tlaps",
        what: "run every benchmark under the default suite directory",
    },
    Example {
        cmd: "clean tlaps bench --json --failures-only benchmarks/tlaps",
        what: "emit a JSON summary restricted to failing obligations",
    },
];

const VALIDATE_EXAMPLES: &[Example] = &[Example {
    cmd: "clean tlaps validate benchmarks/tlaps",
    what: "parse every benchmark JSON file without invoking proofs",
}];

const SHOW_EXAMPLES: &[Example] = &[Example {
    cmd: "clean tlaps show benchmarks/tlaps/example.json",
    what: "inspect a single obligation's declarations, hypotheses, and goal",
}];

const COMMON_REFERENCES: &[Reference] = &[
    Reference {
        kind: RefKind::Design,
        label: "Unified clean CLI feature index",
        target: "designs/2026-04-18-unified-cli-feature-index.md",
    },
    Reference {
        kind: RefKind::Design,
        label: "CLI orphan inventory",
        target: "designs/2026-04-18-cli-orphan-inventory.md",
    },
    Reference {
        kind: RefKind::Issue,
        label: "Epic: unified CLI as feature index",
        target: "#3436",
    },
    Reference {
        kind: RefKind::Issue,
        label: "Absorb tlaps-bench into clean tlaps bench",
        target: "#3448",
    },
    Reference {
        kind: RefKind::Crate,
        label: "clean-tla",
        target: "clean-tla",
    },
];

/// Feature descriptors for the `clean tlaps …` command tree.
///
/// Registered in `crates/clean-cli/src/registry.rs` so `clean features` /
/// `clean help` surface each verb.
pub const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["tlaps", "bench"],
        summary: "Run TLAPS benchmark suites via the clean-tla backend",
        description: BENCH_DESCRIPTION,
        category: Category::Dev,
        stability: Stability::Building,
        examples: BENCH_EXAMPLES,
        see_also: &["tlaps validate", "tlaps show"],
        references: COMMON_REFERENCES,
        domain_root: Some("tlaps"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["tlaps", "validate"],
        summary: "Parse benchmark JSON files without invoking TLAPS proofs",
        description: VALIDATE_DESCRIPTION,
        category: Category::Dev,
        stability: Stability::Building,
        examples: VALIDATE_EXAMPLES,
        see_also: &["tlaps bench", "tlaps show"],
        references: COMMON_REFERENCES,
        domain_root: Some("tlaps"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["tlaps", "show"],
        summary: "Inspect a single TLAPS obligation JSON file",
        description: SHOW_DESCRIPTION,
        category: Category::Dev,
        stability: Stability::Building,
        examples: SHOW_EXAMPLES,
        see_also: &["tlaps bench", "tlaps validate"],
        references: COMMON_REFERENCES,
        domain_root: Some("tlaps"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{ensure_has_example, ensure_unique_paths};

    #[test]
    fn features_paths_are_unique() {
        let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&descriptors).expect("tlaps descriptor paths must be unique");
    }

    #[test]
    fn every_feature_has_at_least_one_example() {
        for descriptor in FEATURES {
            ensure_has_example(descriptor).unwrap_or_else(|e| {
                panic!(
                    "descriptor `{}` must have ≥1 example: {e}",
                    descriptor.path_display()
                )
            });
        }
    }

    #[test]
    fn feature_paths_match_clap_verbs() {
        // Sanity: the three descriptors correspond to the three TlapsCommands
        // variants. If a variant is added, the descriptor array must grow.
        let paths: Vec<&[&str]> = FEATURES.iter().map(|d| d.path).collect();
        assert!(paths.contains(&(&["tlaps", "bench"][..])));
        assert!(paths.contains(&(&["tlaps", "validate"][..])));
        assert!(paths.contains(&(&["tlaps", "show"][..])));
        assert_eq!(paths.len(), 3);
    }
}
