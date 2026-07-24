// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI surface for `clean promote` (DerivedPending → DerivedProved pipeline).
//!
//! Part of Epic #3436 Phase 2. The `PromoteCommands` enum stays in
//! `crate::cmd_promote` so dispatch handlers co-locate with the clap tree;
//! this module only registers descriptors. Part of #3221.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ISSUE_REF: Reference = Reference {
    kind: RefKind::Issue,
    label: "DerivedPending promotion pipeline",
    target: "3221",
};

const CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-verify",
    target: "clean-verify",
};

/// Descriptors for every `clean promote ...` verb.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["promote", "list"],
        summary: "List DerivedPending definitions and proof availability",
        description: "Enumerates every `DerivedPending` definition in the \
specification and reports whether a matching proof is available in the \
proof library. Pass `--verbose` for type signatures and axiom deps.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean promote list --verbose",
            what: "list DerivedPending definitions with details",
        }],
        see_also: &["promote run", "promote count"],
        references: &[DESIGN_REF, ISSUE_REF, CRATE_REF],
        domain_root: Some("promote"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["promote", "run"],
        summary: "Run the full promotion pipeline",
        description: "Attempts to promote every `DerivedPending` definition \
to `DerivedProved` by checking proof library entries against the \
specification. Reports per-attempt status when `--verbose` is set.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean promote run --verbose",
            what: "run the promotion pipeline and print per-attempt details",
        }],
        see_also: &["promote list", "promote check"],
        references: &[DESIGN_REF, ISSUE_REF, CRATE_REF],
        domain_root: Some("promote"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["promote", "check"],
        summary: "Check promotion status for one definition",
        description: "Runs the promotion pipeline for a single named \
definition and prints whether it was promoted plus any blocking axiom \
dependencies.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean promote check mySafeLemma",
            what: "check one DerivedPending definition",
        }],
        see_also: &["promote run", "promote count"],
        references: &[DESIGN_REF, ISSUE_REF, CRATE_REF],
        domain_root: Some("promote"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["promote", "count"],
        summary: "Print summary counts of promotion statuses",
        description: "Prints the aggregate count of definitions in each \
promotion status (`DerivedPending`, `DerivedProved`, etc.) so CI can gate \
on changes in the proved total.",
        category: Category::Meta,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean promote count",
            what: "print summary counts of promotion statuses",
        }],
        see_also: &["promote list", "promote run"],
        references: &[DESIGN_REF, ISSUE_REF, CRATE_REF],
        domain_root: Some("promote"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
