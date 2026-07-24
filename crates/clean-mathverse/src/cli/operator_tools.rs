// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Descriptor-only feature surfaces for the standalone `mathverse_convert` and
//! `mathverse_shard` operator binaries.
//!
//! Unlike [`crate::cli::FEATURES`] (which back the `clean mathverse <verb>` clap
//! tree 1:1), the descriptors here document binaries that are intentionally
//! **not** absorbed into the unified `clean` CLI:
//!
//! - `mathverse_convert` (1258 LOC, 9 sub-verbs) — the upstream-ingest tool
//! - `mathverse_shard` (500+ LOC, 8 sub-verbs) — the canonical shard builder
//!
//! Both binaries are invoked from pinned paths in release scripts
//! (`scripts/release_mathverse_shards.sh`, `scripts/download_all_libraries.sh`,
//! `scripts/prepare_mathverse_release.sh`, and friends) and from
//! `docs/MATHVERSE_RELEASE_CHECKLIST.md`. Full absorption would add a third entry
//! point, bloat the default `clean` binary, and create compat-shim
//! maintenance for two large dispatchers. Leaving them entirely outside the
//! feature index would, however, break Epic #3436's "every feature
//! discoverable" goal.
//!
//! This module resolves the tension: the descriptors participate in the
//! `clean features` / `clean help` index (so operators can find them) but
//! carry [`Category::OperatorTools`], which the coverage drift test treats as
//! exempt from the clap-routability invariant. Examples point at the
//! standalone `cargo run --locked -p clean-mathverse --bin …` invocation that the
//! release scripts use.
//!
//! Design: `designs/2026-04-19-epic-3436-orphan-triage.md` §"2. mathverse_convert"
//! and §"3. mathverse_shard". Tracking: #3513 (Phase 3.5). Epic: #3436.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const MATHVERSE_DESIGN_REF: Reference = Reference {
    kind: RefKind::Doc,
    label: "Mathverse Library architecture",
    target: "docs/DESIGN.md#mathverse-library",
};

const ORPHAN_TRIAGE_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Epic #3436 orphan triage — mathverse_convert / mathverse_shard",
    target: "designs/2026-04-19-epic-3436-orphan-triage.md",
};

const UNIFIED_CLI_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3513: Reference = Reference {
    kind: RefKind::Issue,
    label: "Descriptor-only surfaces under OperatorTools",
    target: "#3513",
};

const MATHVERSE_CONVERT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "convert"],
    summary: "Build .mathverse shards from 14+ upstream proof-system sources (operator tool)",
    description:
        "Standalone operator binary `mathverse_convert` — NOT wired into the top-level \
         `clean` CLI because every caller is a release script, and absorbing the \
         1258-LOC dispatcher would bloat the default `clean` binary with no user \
         benefit. See `scripts/download_all_libraries.sh` for the canonical \
         pipeline and `docs/MATHVERSE_RELEASE_CHECKLIST.md` for the full release \
         flow. Sub-verbs: `mathlib`, `metamath`, `metamath-dir`, `lean4-dir`, \
         `all`, `stats`, `verify`, `verify-shard`, `refresh`. Invoke via \
         `cargo run --locked -p clean-mathverse --release --bin mathverse_convert -- <verb> …`.",
    category: Category::OperatorTools,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "cargo run --locked -p clean-mathverse --release --bin mathverse_convert -- all /tmp/mathverse-data",
            what: "convert all 14 supported source systems in one directory",
        },
        Example {
            cmd: "cargo run --locked -p clean-mathverse --release --bin mathverse_convert -- stats data/mathverse-shards",
            what: "print aggregate stats over the pre-built shard set",
        },
    ],
    see_also: &["mathverse shard", "mathverse stats"],
    references: &[MATHVERSE_DESIGN_REF, ORPHAN_TRIAGE_REF, UNIFIED_CLI_REF, ISSUE_3436, ISSUE_3513],
    domain_root: Some("mathverse"),
    alternative_forms: &["mathverse_convert"],
    feature_gate: None,
};

const MATHVERSE_SHARD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "shard"],
    summary: "Build, verify, and audit .mathverse shards (operator tool)",
    description:
        "Standalone operator binary `mathverse_shard` — the canonical shard \
         release builder. NOT wired into the top-level `clean` CLI for the \
         same reason as `mathverse_convert`: every caller is a release script \
         (`scripts/release_mathverse_shards.sh`, `scripts/prepare_mathverse_release.sh`) \
         and absorbing the 500+-LOC dispatcher would bloat the default \
         binary. Sub-verbs: `build`, `build-native`, `verify`, `verify-kernel`, \
         `verify-incremental`, `audit`, `proof-search`. Invoke via \
         `cargo run --locked -p clean-mathverse --release --bin mathverse_shard -- <verb> …`.",
    category: Category::OperatorTools,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "cargo run --locked -p clean-mathverse --release --bin mathverse_shard -- build ~/.elan/toolchains/.../lib/lean data/mathverse-shards",
            what: "build .mathverse shards from a Lean 4 toolchain",
        },
        Example {
            cmd: "cargo run --locked -p clean-mathverse --release --bin mathverse_shard -- verify data/mathverse-shards",
            what: "verify integrity of a pre-built shard directory",
        },
    ],
    see_also: &["mathverse convert", "mathverse stats"],
    references: &[MATHVERSE_DESIGN_REF, ORPHAN_TRIAGE_REF, UNIFIED_CLI_REF, ISSUE_3436, ISSUE_3513],
    domain_root: Some("mathverse"),
    alternative_forms: &["mathverse_shard"],
    feature_gate: None,
};

/// Descriptor-only entries for the two standalone operator binaries.
///
/// These are registered via `v.extend(clean_mathverse::cli::OPERATOR_TOOLS_FEATURES)`
/// in `clean-cli`'s `registry.rs`. The coverage drift test in
/// `crates/clean-cli/tests/feature_coverage.rs` exempts
/// [`Category::OperatorTools`] descriptors from its clap-routability and
/// example-prefix invariants, because these descriptors intentionally do not
/// back a `clean <path>` clap subcommand.
pub const OPERATOR_TOOLS_FEATURES: &[FeatureDescriptor] =
    &[MATHVERSE_CONVERT_DESC, MATHVERSE_SHARD_DESC];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_every_operator_tool_descriptor_has_an_example() {
        for d in OPERATOR_TOOLS_FEATURES {
            assert!(
                !d.examples.is_empty(),
                "operator-tool descriptor `{}` must have >=1 example",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_operator_tool_descriptor_paths_are_unique() {
        let mut seen = std::collections::HashSet::new();
        for d in OPERATOR_TOOLS_FEATURES {
            let p = d.path_display();
            assert!(seen.insert(p.clone()), "duplicate path `{p}`");
        }
    }

    #[test]
    fn test_every_operator_tool_descriptor_is_categorized_as_operator_tools() {
        // Invariant the coverage drift test relies on: every descriptor in
        // OPERATOR_TOOLS_FEATURES must carry Category::OperatorTools so the
        // clap-routability exemption kicks in uniformly.
        for d in OPERATOR_TOOLS_FEATURES {
            assert_eq!(
                d.category,
                Category::OperatorTools,
                "descriptor `{}` in OPERATOR_TOOLS_FEATURES must be \
                 Category::OperatorTools",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_every_operator_tool_descriptor_lives_under_mathverse_root() {
        for d in OPERATOR_TOOLS_FEATURES {
            assert_eq!(
                d.path[0],
                "mathverse",
                "operator-tool descriptor `{}` must live under `mathverse`",
                d.path_display()
            );
            assert_eq!(
                d.domain_root,
                Some("mathverse"),
                "operator-tool descriptor `{}` must set domain_root = Some(\"mathverse\")",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_operator_tool_descriptors_cover_convert_and_shard() {
        // Issue #3513 acceptance criterion: both `mathverse convert` and
        // `mathverse shard` descriptors must exist in the registered slice.
        let paths: Vec<String> = OPERATOR_TOOLS_FEATURES
            .iter()
            .map(FeatureDescriptor::path_display)
            .collect();
        assert!(
            paths.iter().any(|p| p == "mathverse convert"),
            "missing descriptor for `mathverse convert`; got: {paths:?}"
        );
        assert!(
            paths.iter().any(|p| p == "mathverse shard"),
            "missing descriptor for `mathverse shard`; got: {paths:?}"
        );
    }

    #[test]
    fn test_operator_tool_descriptors_record_standalone_binary_names() {
        let convert = OPERATOR_TOOLS_FEATURES
            .iter()
            .find(|d| d.path == ["mathverse", "convert"])
            .expect("mathverse convert descriptor");
        assert!(
            convert.alternative_forms.contains(&"mathverse_convert"),
            "`mathverse convert` must point at the standalone `mathverse_convert` binary"
        );

        let shard = OPERATOR_TOOLS_FEATURES
            .iter()
            .find(|d| d.path == ["mathverse", "shard"])
            .expect("mathverse shard descriptor");
        assert!(
            shard.alternative_forms.contains(&"mathverse_shard"),
            "`mathverse shard` must point at the standalone `mathverse_shard` binary"
        );
    }
}
