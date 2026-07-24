// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `FeatureDescriptor` array for the `lake` domain of the unified CLI.
//!
//! One descriptor per leaf subcommand exposed by [`super::clap_args`]. These
//! descriptors power `clean features --category build`, `clean help
//! "lake.<verb>"`, and the drift gate in
//! `crates/clean-cli/tests/feature_coverage.rs`.
//!
//! Every descriptor here is `Stability::V1` because the Lake verbs have
//! shipped through the `clean-cli` binary since the first release. Category
//! is [`Category::Build`] for every verb — Lake is the build system.
//!
//! The descriptor set is split across two files to stay under the 500-line
//! per-file cap: core verbs (`build`, `new`, `clean`, `init`, `fetch`,
//! `update`, `env`, `run`, `resolve`, `exe`, `test`) live here in
//! [`FEATURES_CORE`]; the remainder (`script`, `cache`, `lint`, `check-*`,
//! `pack`, `unpack`, `upload`) live in [`super::features_ext::FEATURES_EXT`].
//! [`FEATURES`] is the concatenation, materialized at compile time via a
//! `const fn`.

use clean_features::{Category, Example, FeatureDescriptor, Stability};

use super::features_ext::FEATURES_EXT;
use super::features_refs::COMMON_REFS;

/// Core `lake` verbs shipped directly by the build system. See module docs
/// for why this is split from [`FEATURES_EXT`](super::features_ext::FEATURES_EXT).
pub(super) const FEATURES_CORE: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["lake", "build"],
        summary: "Build the project's Lean targets",
        description: "Compile every target declared in `lakefile.lean`, or a single target if provided. \
                      Honors the shared `--dir` flag and selects a parallel job count with `--jobs` (0 = auto).",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake build",
                what: "build every target in the current project",
            },
            Example {
                cmd: "clean lake build Mathlib",
                what: "build a single named target",
            },
        ],
        see_also: &["lake test", "lake clean", "lake check-build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "new"],
        summary: "Create a new Lake project in a fresh directory",
        description: "Scaffolds a new project directory containing `lakefile.lean`, `lean-toolchain`, \
                      and either a library or executable skeleton depending on `--lib`/`--exe`.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake new my-proj --lib",
                what: "create a new library project",
            },
            Example {
                cmd: "clean lake new my-tool --exe",
                what: "create a new executable project",
            },
        ],
        see_also: &["lake init"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "clean"],
        summary: "Remove build artifacts for the project",
        description: "Deletes `.lake/build` and `.lake/packages` for the current workspace so the next \
                      build runs fresh. Use `--verbose` for a file-by-file report.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake clean",
            what: "delete cached build output",
        }],
        see_also: &["lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "init"],
        summary: "Initialize Lake in the current directory",
        description: "Adds `lakefile.lean` and `lean-toolchain` to the current directory, preserving \
                      existing sources. The optional positional name overrides the inferred package name.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake init",
                what: "initialize Lake in the current directory",
            },
            Example {
                cmd: "clean lake init my-pkg",
                what: "initialize with an explicit package name",
            },
        ],
        see_also: &["lake new"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "fetch"],
        summary: "Fetch dependency sources from git",
        description: "Clones every git-backed dependency declared in `lakefile.lean`/`lake-manifest.json` \
                      into `.lake/packages`. Does not update recorded revisions — use `lake update` for that.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake fetch",
            what: "fetch all declared dependencies",
        }],
        see_also: &["lake update", "lake resolve"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "update"],
        summary: "Update dependencies to the latest revisions",
        description: "Pulls the latest upstream revision for each git dependency and rewrites \
                      `lake-manifest.json`. With a positional argument, limits the update to one package.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake update",
                what: "update every dependency",
            },
            Example {
                cmd: "clean lake update mathlib",
                what: "update a single dependency",
            },
        ],
        see_also: &["lake fetch", "lake resolve"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "env"],
        summary: "Show the project's build environment",
        description: "Prints the toolchain, resolved search paths, and other variables the Lake build \
                      would export for sub-processes. Useful for debugging dependency resolution.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake env --verbose",
            what: "dump the resolved build environment",
        }],
        see_also: &["lake resolve"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "run"],
        summary: "Build and run a Lean executable target",
        description: "Compiles the named executable target (or the default target if none is given) \
                      and runs it in the project environment, passing through any trailing arguments.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake run",
                what: "run the default executable target",
            },
            Example {
                cmd: "clean lake run my-exe --flag value",
                what: "run a named executable target with arguments",
            },
        ],
        see_also: &["lake exe", "lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "resolve"],
        summary: "Resolve dependencies and write lake-manifest.json",
        description: "Recomputes the dependency graph and rewrites `lake-manifest.json`. Use `--dry-run` \
                      to preview the resolution without modifying the manifest on disk.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake resolve",
                what: "resolve and update the manifest",
            },
            Example {
                cmd: "clean lake resolve --dry-run",
                what: "preview without writing changes",
            },
        ],
        see_also: &["lake fetch", "lake update"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "exe"],
        summary: "Run a pre-built native executable",
        description: "Executes a previously-built native binary by target name, passing through any \
                      trailing arguments. Unlike `lake run`, does not trigger a build first.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake exe my-tool -- --flag value",
            what: "run a built executable with arguments",
        }],
        see_also: &["lake run", "lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "test"],
        summary: "Build and run the project's test targets",
        description: "Runs every target declared as a test (or a single target by name). `--jobs` \
                      controls build parallelism; each test is invoked serially.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake test",
                what: "run every test target",
            },
            Example {
                cmd: "clean lake test MyLibTests",
                what: "run a single test target",
            },
        ],
        see_also: &["lake check-test", "lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// Total length of [`FEATURES`].
const FEATURES_LEN: usize = FEATURES_CORE.len() + FEATURES_EXT.len();

/// Materialized concatenation of [`FEATURES_CORE`] and
/// [`FEATURES_EXT`](super::features_ext::FEATURES_EXT). Copying the
/// `Copy` descriptors into a fixed-size array at compile time lets us keep
/// the public `FEATURES` constant a single contiguous `&'static
/// [FeatureDescriptor]`, so downstream consumers (`registry::all_features`,
/// the drift gate) see exactly one slice.
const fn build_features() -> [FeatureDescriptor; FEATURES_LEN] {
    // Use an arbitrary descriptor as the init value; every slot is overwritten
    // below before the array is returned. `FeatureDescriptor` is `Copy`, so
    // the init is free at compile time.
    let init = FEATURES_CORE[0];
    let mut out = [init; FEATURES_LEN];
    let mut i = 0;
    while i < FEATURES_CORE.len() {
        out[i] = FEATURES_CORE[i];
        i += 1;
    }
    let mut j = 0;
    while j < FEATURES_EXT.len() {
        out[FEATURES_CORE.len() + j] = FEATURES_EXT[j];
        j += 1;
    }
    out
}

/// Backing storage for [`FEATURES`]. Declared separately so the constant
/// expression is stored once and [`FEATURES`] can borrow it as
/// `&'static [FeatureDescriptor]`.
const FEATURES_ARRAY: [FeatureDescriptor; FEATURES_LEN] = build_features();

/// Every leaf `lake` verb surfaced by the unified `clean` CLI.
///
/// The array is consumed by `crates/clean-cli/src/registry.rs::all_features`
/// via a single `v.extend(clean_lake::cli::FEATURES)` line.
pub const FEATURES: &[FeatureDescriptor] = &FEATURES_ARRAY;

#[cfg(test)]
mod tests {
    use super::*;
    use clean_features::{ensure_has_example, ensure_unique_paths};

    #[test]
    fn features_has_every_expected_verb() {
        let expected: &[&[&str]] = &[
            &["lake", "build"],
            &["lake", "new"],
            &["lake", "clean"],
            &["lake", "init"],
            &["lake", "fetch"],
            &["lake", "update"],
            &["lake", "env"],
            &["lake", "run"],
            &["lake", "resolve"],
            &["lake", "exe"],
            &["lake", "test"],
            &["lake", "script", "list"],
            &["lake", "script", "run"],
            &["lake", "script", "doc"],
            &["lake", "cache", "get"],
            &["lake", "cache", "put"],
            &["lake", "cache", "add"],
            &["lake", "lint"],
            &["lake", "check-build"],
            &["lake", "check-test"],
            &["lake", "check-lint"],
            &["lake", "pack"],
            &["lake", "unpack"],
            &["lake", "upload"],
            &["lake", "verify-fresh"],
            &["lake", "goodness"],
        ];
        assert_eq!(FEATURES.len(), expected.len());
        for want in expected {
            let found = FEATURES.iter().any(|d| d.path == *want);
            assert!(found, "missing descriptor for {want:?}");
        }
    }

    #[test]
    fn features_have_examples() {
        for d in FEATURES {
            ensure_has_example(d).unwrap_or_else(|e| panic!("descriptor missing example: {e}"));
        }
    }

    #[test]
    fn feature_paths_unique() {
        let refs: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
        ensure_unique_paths(&refs).expect("lake descriptor paths must be unique");
    }

    #[test]
    fn every_feature_is_v1_build() {
        for d in FEATURES {
            assert_eq!(
                d.category,
                Category::Build,
                "{} should be Build",
                d.path_display()
            );
            assert_eq!(
                d.stability,
                Stability::V1,
                "{} should be V1 — Lake verbs have shipped for releases",
                d.path_display()
            );
        }
    }
}
