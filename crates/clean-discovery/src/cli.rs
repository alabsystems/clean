// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean discover` CLI surface: argument shape plus the static
//! [`FeatureDescriptor`] consumed by the unified feature index.
//!
//! The old orphan binary `clean-discover` exposed a single flag-driven
//! command for AI-driven proof discovery across theorem families. This
//! module hosts the canonical argument definition so the top-level
//! `clean` binary can dispatch `clean discover ...` using the same
//! parser. The legacy binary survives as a compat shim that re-execs
//! `clean discover`.
//!
//! Part of #3449. Epic: #3436. Design:
//! `designs/2026-04-18-unified-cli-feature-index.md`.

use clap::Args;
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

/// Arguments for `clean discover`.
///
/// Mirrors the flag surface of the legacy `clean-discover` binary so
/// downstream scripts keep working verbatim after the prefix change.
#[derive(Debug, Clone, Args)]
pub struct DiscoverArgs {
    /// Theorem family to search (cert_size_bound, domain_tightness,
    /// verification_complexity, new_abstract_domain).
    #[arg(long, default_value = "cert_size_bound")]
    pub family: String,

    /// Maximum depth parameter.
    #[arg(long, default_value_t = 5)]
    pub max_depth: u64,

    /// Maximum width parameter.
    #[arg(long, default_value_t = 5)]
    pub max_width: u64,

    /// Maximum constant C.
    #[arg(long, default_value_t = 5)]
    pub max_c: u64,

    /// Number of threads (omit for rayon default).
    #[arg(long)]
    pub threads: Option<usize>,

    /// Output path for the JSON results file.
    #[arg(long)]
    pub output: Option<String>,

    /// Suppress progress output on stderr.
    #[arg(long, short)]
    pub quiet: bool,
}

/// Feature descriptors registered by the discovery crate.
///
/// The unified `clean` registry extends itself with this slice so
/// `clean features` and `clean help discover` stay in sync with the
/// clap parser without a second source of truth.
pub const FEATURES: &[FeatureDescriptor] = &[FeatureDescriptor {
    path: &["discover"],
    summary: "AI-driven proof discovery loop over theorem families (Experimental)",
    description: "Runs the clean discovery pipeline: generate parameterized \
candidate theorems, batch type-check them via the kernel, and emit a JSON \
report of verified candidates. Families cover certificate size bounds, \
domain tightness, verification complexity, and new abstract-domain \
constructions. The flag surface matches the legacy `clean-discover` \
binary, which now execs back into this subcommand. \
Marked `Stability::Experimental` because the family catalog, JSON output \
schema, and search heuristics are all under active iteration and may \
change without notice (Epic #3436).",
    category: Category::Proof,
    stability: Stability::Experimental,
    examples: &[
        Example {
            cmd: "clean discover --family cert_size_bound --max-depth 3 --max-width 3 --max-c 3",
            what: "Search the certificate-size-bound family with a small parameter box.",
        },
        Example {
            cmd: "clean discover --quiet --output /tmp/discover.json",
            what: "Run the default search and write results to a file without progress chatter.",
        },
    ],
    see_also: &[],
    references: &[
        Reference {
            kind: RefKind::Design,
            label: "Unified CLI feature index",
            target: "designs/2026-04-18-unified-cli-feature-index.md",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Absorb clean-discover into clean discover",
            target: "3449",
        },
        Reference {
            kind: RefKind::Issue,
            label: "Discovery loop epic",
            target: "3258",
        },
        Reference {
            kind: RefKind::Crate,
            label: "clean-discovery",
            target: "clean-discovery",
        },
    ],
    domain_root: Some("discover"),
    alternative_forms: &[],
    feature_gate: None,
}];
