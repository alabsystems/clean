// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for the 7 mathverse verbs re-absorbed via passthrough
//! in issue #3512 (`find`, `graph`, `diff`, `verify`, `download`, `export`,
//! `release`).
//!
//! Lineage:
//! - `ae3772027` absorbed all 11 remaining verbs as `PassthroughArgs`.
//! - `f43429751` re-typed 4 of them (`list`/`sample`/`deps`/`version`) as
//!   clap derive args but dropped the other 7.
//! - This file restores descriptors for the 7 dropped verbs, matching the
//!   passthrough wiring in `cli/passthrough_dispatch.rs`.
//!
//! Kept in a separate module from [`crate::cli::descriptors`] and
//! [`crate::cli::descriptors_browse`] so each descriptor file stays under
//! the 500-line file-size cap. Design:
//! `designs/2026-04-19-epic-3436-orphan-triage.md`. Epic: #3436.

use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};

const MATHVERSE_DESIGN_REF: Reference = Reference {
    kind: RefKind::Doc,
    label: "Mathverse Library architecture",
    target: "docs/DESIGN.md#mathverse-library",
};

const ORPHAN_TRIAGE_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Epic #3436 orphan triage — mathverse partial coverage",
    target: "designs/2026-04-19-epic-3436-orphan-triage.md",
};

const ISSUE_3436: Reference = Reference {
    kind: RefKind::Issue,
    label: "Epic: unified CLI as feature index",
    target: "#3436",
};

const ISSUE_3512: Reference = Reference {
    kind: RefKind::Issue,
    label: "Complete mathverse absorption — remaining 11 verbs",
    target: "#3512",
};

const FIND_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "find"],
    summary: "Unified search: name/tags/similarity/cross-system/domain/BM25",
    description: "A superset of `mathverse search`. `find` combines substring name search, \
         tag filtering (`--tag`), similarity lookup (`--similar <name>`), \
         cross-system matching (`--cross-system <name>`), domain/system \
         filters, and opt-in BM25 semantic search (`--semantic`). The default \
         mode is full-text over names; add `--tags` to list every known \
         keyword tag with counts. For a leaner single-mode search, use \
         `mathverse search`.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse find Nat.add --semantic",
        what: "BM25 semantic search over names and types",
    }],
    see_also: &["mathverse search", "mathverse list"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &["clean mathverse search"],
    feature_gate: None,
};

const GRAPH_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "graph"],
    summary: "Cross-system knowledge graph (`search`/`overlap`/`stats`)",
    description: "Inspect the cross-system knowledge graph built over the Mathverse \
         Library. Sub-verbs: `graph search <name>` walks nodes adjacent to a \
         declaration; `graph overlap` reports the set intersection between \
         source systems; `graph stats` prints node/edge counts. Defaults to \
         the table format; `--format json|csv|tsv` emits machine-readable \
         layouts. Use `mathverse deps` for name-level adjacency on a single \
         declaration, `mathverse graph` for the full concept-graph view.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse graph stats",
        what: "summary of the cross-system graph",
    }],
    see_also: &["mathverse deps", "mathverse systems"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const DIFF_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "diff"],
    summary: "Symmetric diff of two `.mathverse` shards by declaration name",
    description: "Compares two `.mathverse` shards and prints declarations present in one \
         but not the other. Supports the uniform `--format` flag \
         (`table`/`text`/`json`/`csv`/`tsv`). Useful when bumping a release \
         to spot churn between shard versions or when auditing which \
         declarations a shard rebuild introduced or dropped.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse diff a.mathverse b.mathverse",
        what: "name-level symmetric diff of two shards",
    }],
    see_also: &["mathverse verify", "mathverse list"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const VERIFY_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "verify"],
    summary: "Verify a shard directory or release manifest",
    description: "Structural walk of every `.mathverse` shard in a directory plus optional \
         blake3 verification against the release manifest. This is the \
         user-facing verification path; operators building releases should \
         additionally use the `mathverse_shard` binary (`verify-kernel`). Pair \
         with `mathverse release verify` when checking blake3 digests against a \
         pinned release manifest.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse verify data/mathverse-shards",
        what: "walk every shard and report structural errors",
    }],
    see_also: &["mathverse download", "mathverse release"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &["clean mathverse release verify"],
    feature_gate: None,
};

const DOWNLOAD_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "download"],
    summary: "Download a manifest-verified Mathverse Library release archive",
    description: "Fetches a prebuilt `.mathverse` shard archive only from a tagged GitHub \
         Release that publishes a compatible `mathverse-library-v*.tar.zst` asset \
         plus `mathverse-manifest.json` checksums, then unpacks it into the \
         discovery path (`$MATHVERSE_LIBRARY_PATH` / `./data/mathverse-library/` / \
         `$HOME/.mathverse/library/`). Use `--version <V>` to select a release \
         known to contain those assets, and pass `--force` to replace an \
         existing installation. Pairs with `mathverse verify` for a post-download \
         integrity check.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse download --version <V> --force",
        what: "download a compatible release archive and replace the local copy",
    }],
    see_also: &["mathverse verify", "mathverse release"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const EXPORT_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "export"],
    summary: "Export Mathverse Library data (`clean-native`/`arxiv`/`all`)",
    description: "Produces derived artifacts from the loaded library. Sub-verbs: \
         `export clean-native` emits the kernel-verified constructive subset \
         as a clean-Native shard; `export arxiv` writes the arXiv \
         autoformalization dataset; `export all` runs every exporter. Output \
         paths are printed to stdout on completion. Pair with `mathverse release` \
         when packaging these artifacts for a tagged release.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse export clean-native",
        what: "emit the clean-Native constructive shard",
    }],
    see_also: &["mathverse release", "mathverse stats"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const RELEASE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "release"],
    summary: "Release management (`build`/`package`/`verify`/`download`/`info`)",
    description: "Drives the end-to-end release lifecycle for `.mathverse` shard \
         archives. Sub-verbs: `release build` produces every shard from \
         upstream proof systems; `release package` assembles the tar.zst \
         archive and manifest; `release verify` checks blake3 digests; \
         `release download` is a thin wrapper over `mathverse download`; \
         `release info` prints the current release metadata.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[Example {
        cmd: "clean mathverse release info",
        what: "print release metadata for the installed library",
    }],
    see_also: &["mathverse download", "mathverse verify"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

/// Descriptor array for the 7 verbs re-absorbed via passthrough under #3512.
///
/// Registered by `clean-cli/src/registry.rs` via
/// `v.extend(clean_mathverse::cli::PASSTHROUGH_FEATURES)`. The Phase-1 set
/// (`search`, `info`, `stats`, `systems`) lives in
/// [`crate::cli::FEATURES`]; the browse-verb set
/// (`list`/`sample`/`deps`/`version`) lives in
/// [`crate::cli::BROWSE_FEATURES`]. All three slices register under the
/// `mathverse` root and participate in the same drift invariants.
pub const PASSTHROUGH_FEATURES: &[FeatureDescriptor] = &[
    FIND_DESC,
    GRAPH_DESC,
    DIFF_DESC,
    VERIFY_DESC,
    DOWNLOAD_DESC,
    EXPORT_DESC,
    RELEASE_DESC,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_every_passthrough_descriptor_has_an_example() {
        for d in PASSTHROUGH_FEATURES {
            assert!(
                !d.examples.is_empty(),
                "descriptor `{}` must have >=1 example",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_passthrough_descriptor_paths_are_unique() {
        let mut seen = std::collections::HashSet::new();
        for d in PASSTHROUGH_FEATURES {
            let p = d.path_display();
            assert!(seen.insert(p.clone()), "duplicate path `{p}`");
        }
    }

    #[test]
    fn test_every_passthrough_descriptor_points_to_mathverse_root() {
        for d in PASSTHROUGH_FEATURES {
            assert_eq!(
                d.path[0],
                "mathverse",
                "descriptor `{}` must live under `mathverse`",
                d.path_display()
            );
            assert_eq!(
                d.domain_root,
                Some("mathverse"),
                "descriptor `{}` must set domain_root = Some(\"mathverse\")",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_every_passthrough_descriptor_is_categorized_as_import() {
        for d in PASSTHROUGH_FEATURES {
            assert_eq!(
                d.category,
                Category::Import,
                "descriptor `{}` must be Category::Import",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_passthrough_descriptors_cover_all_seven_verbs() {
        // #3512 acceptance criterion: the 7 verbs dropped by f43429751 are
        // all restored in this slice.
        let paths: Vec<String> = PASSTHROUGH_FEATURES
            .iter()
            .map(FeatureDescriptor::path_display)
            .collect();
        for verb in [
            "mathverse find",
            "mathverse graph",
            "mathverse diff",
            "mathverse verify",
            "mathverse download",
            "mathverse export",
            "mathverse release",
        ] {
            assert!(
                paths.iter().any(|p| p == verb),
                "missing descriptor for `{verb}`; got: {paths:?}"
            );
        }
        assert_eq!(
            PASSTHROUGH_FEATURES.len(),
            7,
            "exactly 7 passthrough verbs expected",
        );
    }
}
