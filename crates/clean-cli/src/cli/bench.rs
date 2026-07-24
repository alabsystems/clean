// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean bench` (geometry benchmark runner).
//!
//! Part of Epic #3436 Phase 2. The `bench` subcommand currently wraps the
//! geometry benchmark suite under `crates/clean-cli/src/benchmarks/`. Kernel
//! microbench descriptors may be added later from `clean_kernel::cli`; for
//! now the whole group is owned here.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::path::PathBuf;

use clap::Subcommand;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Subcommands for `clean bench` (geometry benchmarks).
#[derive(Subcommand)]
pub(crate) enum BenchCommands {
    /// Run geometry benchmarks on a suite.
    Run {
        /// Directory containing benchmark problems (default: benchmarks/geometry/alphageometry)
        #[arg(short, long)]
        suite: Option<PathBuf>,
        /// Output directory for results
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
        /// Timeout per problem in milliseconds
        #[arg(long, default_value = "60000")]
        timeout: u64,
        /// Skip certificate verification (faster but less rigorous)
        #[arg(long)]
        no_verify: bool,
        /// Maximum number of problems to run (0 = all)
        #[arg(long, default_value = "0")]
        max_problems: usize,
        /// Only run specific problem IDs (comma-separated)
        #[arg(long)]
        only: Option<String>,
        /// Skip specific problem IDs (comma-separated)
        #[arg(long)]
        skip: Option<String>,
    },
    /// List problems in a benchmark suite.
    List {
        /// Directory containing benchmark problems
        #[arg(short, long)]
        suite: Option<PathBuf>,
        /// Show detailed problem info
        #[arg(short, long)]
        verbose: bool,
    },
    /// Show info about a specific problem.
    Info {
        /// Problem ID or path to problem directory
        problem: String,
        /// Suite directory (if problem is an ID)
        #[arg(short, long)]
        suite: Option<PathBuf>,
    },
    /// Verify a single problem's derivation.
    Verify {
        /// Problem ID or path to problem directory
        problem: String,
        /// Suite directory (if problem is an ID)
        #[arg(short, long)]
        suite: Option<PathBuf>,
        /// Show verbose output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Validate public benchmark publication metadata.
    #[command(name = "publication-check")]
    PublicationCheck {
        /// Require launch-grade published evidence.
        #[arg(long)]
        launch: bool,
        /// Emit a structured JSON report.
        #[arg(long)]
        json: bool,
        /// Repository root to inspect (default: current working directory).
        #[arg(long)]
        repo_root: Option<PathBuf>,
        /// Publication metadata root (default: <repo>/reports/benchmarks/publication).
        #[arg(long)]
        publication_root: Option<PathBuf>,
        /// Override today's date for deterministic checks (YYYY-MM-DD).
        #[arg(long)]
        today: Option<String>,
    },
}

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

/// Descriptors for every `clean bench ...` verb.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["bench", "run"],
        summary: "Run the geometry benchmark suite",
        description: "Runs every problem in the selected geometry benchmark \
suite through the clean pipeline, records per-problem timing and verification \
status, and (optionally) writes results to `--output`. Default suite is \
`benchmarks/geometry/alphageometry`.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean bench run --suite benchmarks/geometry/alphageometry --timeout 60000",
            what: "run the geometry bench with a 60s per-problem timeout",
        }],
        see_also: &["bench list", "bench verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["bench", "list"],
        summary: "List problems in a benchmark suite",
        description: "Lists every problem in the selected suite directory. \
Pass `--verbose` to include hypotheses, goals, and metadata for each problem.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean bench list --suite benchmarks/geometry/alphageometry",
            what: "list every problem id in the suite",
        }],
        see_also: &["bench info", "bench run"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["bench", "info"],
        summary: "Show info about a benchmark problem",
        description: "Prints the statement, hypotheses, and suite membership \
for a single problem. Accepts either a problem ID resolved under \
`--suite` or a direct path to the problem directory.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean bench info orthocenter_03",
            what: "inspect a single benchmark problem",
        }],
        see_also: &["bench list", "bench verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["bench", "verify"],
        summary: "Verify a single benchmark problem's derivation",
        description: "Verifies the stored derivation for one benchmark \
problem. Use this as a fast smoke check while iterating on derivation \
formats; prefer `bench run` for suite-level regression runs.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean bench verify orthocenter_03 --suite benchmarks/geometry/alphageometry",
            what: "verify one problem's derivation",
        }],
        see_also: &["bench run", "cert verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["bench", "publication-check"],
        summary: "Validate public benchmark publication metadata (Experimental)",
        description: "Experimental gate that checks `reports/benchmarks/publication/current.json` \
against the Rust-owned public benchmark publication contract. `--launch` \
requires published, fresh, committed benchmark evidence and fails closed with \
structured JSON when evidence is missing or stale.",
        category: Category::Meta,
        stability: Stability::Experimental,
        examples: &[Example {
            cmd: "clean bench publication-check --launch --json",
            what: "run the launch-grade benchmark publication gate",
        }],
        see_also: &["bench run", "bench verify"],
        references: &[DESIGN_REF, CRATE_REF],
        domain_root: Some("bench"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
