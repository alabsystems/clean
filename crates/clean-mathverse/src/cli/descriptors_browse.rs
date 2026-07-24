// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature descriptors for the browse-oriented `clean mathverse <verb>`
//! subcommands absorbed under Issue #3512 (`list`, `sample`, `deps`,
//! `version`).
//!
//! The top-level `clean-cli` binary registers these via
//! `v.extend(clean_mathverse::cli::BROWSE_FEATURES)` alongside the existing
//! `FEATURES` array. Kept in a separate module from [`crate::cli::descriptors`]
//! so both files stay under the 500-line file-size cap.
//!
//! Design: `designs/2026-04-19-epic-3436-orphan-triage.md` §"Mathverse partial
//! coverage". Epic: #3436. Tracking: #3512.

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

const ISSUE_3512: Reference = Reference {
    kind: RefKind::Issue,
    label: "Complete mathverse absorption — remaining 11 verbs",
    target: "#3512",
};

const LIST_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "list"],
    summary: "Enumerate Mathverse Library declarations with filtering and pagination",
    description: "Walks the loaded `.mathverse` shards in index order and emits declaration \
         names, source systems, and trust levels. Filter by source system \
         with `--system <name>` (canonical `SourceSystem` label or numeric \
         id), paginate with `--limit` (default 20) and `--offset`. Pass \
         `--json` for machine-readable output. Use this for deterministic \
         sweeps over the library when you want every matching row rather \
         than a sample.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse list --system lean4 --limit 10",
            what: "first 10 Lean 4 declarations",
        },
        Example {
            cmd: "clean mathverse list --offset 100 --limit 50 --json",
            what: "paginate the next 50 rows as JSON",
        },
    ],
    see_also: &["mathverse sample", "mathverse search", "mathverse stats"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const SAMPLE_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "sample"],
    summary: "Deterministic sample of N Mathverse Library declarations",
    description: "Draws N declarations from the loaded shards using a seeded LCG walk \
         across matching indices. Output is byte-identical across runs with \
         the same `--seed` and shard set, which makes this the preferred \
         fixture source for downstream tests. Filter by source system \
         (`--system`) and trust level (`--trust`). When no declarations match \
         the filter combination, the command exits 0 with an empty result set \
         rather than erroring — identical to the standalone `mathverse sample` \
         shape.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse sample --n 5",
            what: "5 declarations with the default seed",
        },
        Example {
            cmd: "clean mathverse sample --n 20 --system metamath --seed 42",
            what: "20 Metamath declarations, deterministic with seed=42",
        },
    ],
    see_also: &["mathverse list", "mathverse search", "mathverse stats"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const DEPS_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "deps"],
    summary: "Show direct or transitive dependencies of an Mathverse declaration",
    description: "Resolves `<name>` to a `ConstantIdx` via the library's name index, \
         then BFS-walks the dependency adjacency list built at load time. \
         Default behaviour is a direct-dependency listing (depth 1); pass \
         `--transitive` (or `--depth N`) for a bounded closure. `--limit` \
         caps total rows returned so the walk cannot explode on large \
         libraries. Pass `--reverse` (or use the `mathverse uses` alias) to \
         invert the walk — the declarations that DEPEND ON `<name>`, ranked by \
         impact. Pairs with `mathverse graph` when you want the full \
         concept-graph view instead of name-level adjacency.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse deps Nat.add_comm",
            what: "direct dependencies of `Nat.add_comm`",
        },
        Example {
            cmd: "clean mathverse deps Nat.add_comm --transitive --depth 3 --limit 500",
            what: "transitive closure up to depth 3",
        },
    ],
    see_also: &["mathverse uses", "mathverse info", "mathverse search"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const USES_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "uses"],
    summary: "Reverse dependencies: which declarations USE a given declaration (impact-ranked)",
    description: "The inverse of `mathverse deps`: resolves `<name>` (exact, else a \
         case-insensitive / substring match so a `search`/`find` hit pipes \
         straight in) and lists the declarations that DEPEND ON it — its users \
         and blast radius. Walks the lazily-built reverse of the load-time \
         dependency adjacency. Default is direct users (depth 1); `--transitive` \
         / `--depth N` widen the closure and `--limit` caps rows. Hits are ranked \
         by each user's own in-degree (the `USED-BY` column) so the most-reused / \
         highest-impact dependents surface first — the premise-selection and \
         \"what breaks if I change X\" question. Alias for `mathverse deps \
         --reverse`.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse uses Nat.add_comm",
            what: "declarations that directly depend on `Nat.add_comm`, ranked by impact",
        },
        Example {
            cmd: "clean mathverse uses Nat.add_comm --transitive --limit 500",
            what: "full transitive reverse closure (equivalent to `deps --reverse --transitive`)",
        },
    ],
    see_also: &["mathverse deps", "mathverse info", "mathverse search"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

const VERSION_DESC: FeatureDescriptor = FeatureDescriptor {
    path: &["mathverse", "version"],
    summary: "Show Mathverse Library release version and live summary stats",
    description: "Prints the Mathverse Library release string (matches the standalone \
         `mathverse version` value) followed by a one-line summary: shard count, \
         source-system count, and total declarations. When the shard \
         directory is present, also emits a per-trust-level breakdown \
         (KernelVerified / SourceVerified / Translated / Axiomatized / \
         Unverified). Degrades gracefully when the shard directory is \
         missing: falls back to the canonical `mathverse-v0.9.0` release \
         numbers.",
    category: Category::Import,
    stability: Stability::Usable,
    examples: &[
        Example {
            cmd: "clean mathverse version",
            what: "release string + live counts",
        },
        Example {
            cmd: "clean mathverse version --json",
            what: "machine-readable version/stats for release scripts",
        },
    ],
    see_also: &["mathverse stats", "mathverse systems"],
    references: &[
        MATHVERSE_DESIGN_REF,
        ORPHAN_TRIAGE_REF,
        UNIFIED_CLI_REF,
        ISSUE_3436,
        ISSUE_3512,
    ],
    domain_root: Some("mathverse"),
    alternative_forms: &[],
    feature_gate: None,
};

/// Descriptor array for the browse-oriented `clean mathverse <verb>`
/// subcommands absorbed under #3512. Registered via
/// `v.extend(clean_mathverse::cli::BROWSE_FEATURES)` in `clean-cli`'s
/// `registry.rs`.
pub const BROWSE_FEATURES: &[FeatureDescriptor] =
    &[LIST_DESC, SAMPLE_DESC, DEPS_DESC, USES_DESC, VERSION_DESC];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_every_descriptor_has_an_example() {
        for d in BROWSE_FEATURES {
            assert!(
                !d.examples.is_empty(),
                "descriptor `{}` must have >=1 example",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_descriptor_paths_are_unique() {
        let mut seen = std::collections::HashSet::new();
        for d in BROWSE_FEATURES {
            let p = d.path_display();
            assert!(seen.insert(p.clone()), "duplicate path `{p}`");
        }
    }

    #[test]
    fn test_every_descriptor_points_to_mathverse_root() {
        for d in BROWSE_FEATURES {
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
    fn test_every_descriptor_is_categorized_as_import() {
        // Browse verbs all share the Import category with the existing
        // `mathverse search/info/stats/systems` descriptors.
        for d in BROWSE_FEATURES {
            assert_eq!(
                d.category,
                Category::Import,
                "descriptor `{}` must be Category::Import",
                d.path_display()
            );
        }
    }

    #[test]
    fn test_browse_descriptors_cover_list_sample_deps_version() {
        // #3512 acceptance criterion — every absorbed verb present.
        let paths: Vec<String> = BROWSE_FEATURES
            .iter()
            .map(FeatureDescriptor::path_display)
            .collect();
        for verb in [
            "mathverse list",
            "mathverse sample",
            "mathverse deps",
            "mathverse version",
        ] {
            assert!(
                paths.iter().any(|p| p == verb),
                "missing descriptor for `{verb}`; got: {paths:?}"
            );
        }
    }
}
