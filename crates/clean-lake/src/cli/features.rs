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
//! Category is [`Category::Build`] for every verb — Lake is the build system.
//!
//! **Stability is per-verb and earned, not inherited.** This block used to read
//! "every descriptor here is `Stability::V1` because the Lake verbs have
//! shipped since the first release" — that rationale is what produced the
//! overstatement class the 2026-08-25 and 2026-08-26 CLI audits found: having
//! shipped is not the same as keeping a v1 promise, and Lake supplied 45% of
//! every v1 claim in the CLI while `cache get` fetched nothing and
//! `check-build` wrote artifacts it said it would not. Grade each verb against
//! what a probe of that verb actually does; see
//! [`super::features_ext::FEATURES_EXT`] for the non-V1 rows.
//!
//! The descriptor set is split across two files to stay under the 500-line
//! per-file cap: core verbs (`build`, `new`, `clean`, `init`, `fetch`,
//! `update`, `env`, `run`, `resolve`, `exe`, `test`) live here in
//! [`FEATURES_CORE`]; the remainder (`script`, `cache`, `lint`, `check-*`,
//! `pack`, `unpack`, `upload`, `verify-fresh`, `goodness`, `smoke`, `serve`)
//! live in
//! [`super::features_ext::FEATURES_EXT`].
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
                      Honors the shared `--dir` flag and selects a parallel job count with `--jobs` (0 = auto). \
                      Import loading is fail-closed: a stdlib or local-dependency `.olean` that fails to \
                      load fails the module build unless `--permissive-imports` is passed.",
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
                      and either a library or executable skeleton depending on `--lib`/`--exe`. \
                      The `lean-toolchain` reads `clean`. elan resolves that name to a toolchain \
                      linked with `elan toolchain link clean <dir>`, and otherwise to a Lean \
                      release named `clean`, which does not exist, so `lean` or `lake` run \
                      through elan in the project fails loudly instead of running a Lean \
                      toolchain. Clean's own `lean` front door, `clean lean`, reads `clean` as \
                      Clean's pin.",
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
        description: "Deletes the workspace build directory (`.lake/build`) so the next build runs \
                      fresh. Fetched dependencies under `.lake/packages` are PRESERVED — matching \
                      Lean 4 Lake, whose `lake clean` removes build outputs only; re-fetch with \
                      `lake fetch`/`lake update` or delete `.lake/packages` by hand. Use `--verbose` \
                      for a file-by-file report of what is removed.",
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
                      existing sources. The optional positional name overrides the inferred package name. \
                      The `lean-toolchain` reads `clean`, as `clean lake new` writes it, so elan \
                      in the project fails loudly instead of running a Lean toolchain.",
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
                      would export for sub-processes. Useful for debugging dependency resolution. \
                      With a trailing command (`clean lake env <cmd> <args>`) it runs that command \
                      in the project directory, adding those variables to the inherited \
                      environment when the directory holds a Lake workspace. A Lean toolchain \
                      program is refused by name before anything is spawned: `lean`, `lake`, \
                      `leanchecker`, `leanexport`, `lean4export`, `leanc`, `leanir`, \
                      `leanmake` and `leanpkg`, matched on the basename wherever the program \
                      lives. It could run real Lean or a stale reroute rather than Clean, and \
                      each refusal names the Clean verb to use instead (`clean lean`, \
                      `clean lake <verb>`, `clean olean replay`, `clean run`, \
                      `clean compile`). A wrapper such as `sh -c` is run as given.",
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
        summary: "Build an executable target and run it",
        description: "Builds the named executable target and runs the resulting native binary, passing \
                      through any trailing arguments and propagating its exit status. This matches \
                      Lean 4 Lake, whose own `lake exe` is documented as \"build an exe and run it in \
                      Lake's environment\" — it is NOT a run-only verb. The difference from \
                      `lake run` is target selection, not building: `lake exe` requires an explicit \
                      target name, while `lake run` falls back to the default target and honors \
                      `--jobs`.",
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
            &["lake", "smoke"],
            &["lake", "serve"],
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

    /// Lake verbs are all `Category::Build`, and their stability is PINNED
    /// PER VERB rather than asserted uniformly.
    ///
    /// This test used to require `Stability::V1` for every verb, justified as
    /// "Lake verbs have shipped for releases". Shipping is not the same as
    /// working: `Stability::V1` is defined as "stable, public surface that is
    /// covered by semver" (`clean-features::Stability`), and several verbs do
    /// not meet it —
    ///
    /// - `lake upload` validates a build dir and then fails with an explicit
    ///   "not yet implemented" error (#421). It cannot publish anything.
    /// - `lake cache get` reports cache locations and fetches nothing.
    /// - `lake cache put` copies into `.lake/cache` only; cloud upload is
    ///   unimplemented and the command says so.
    /// - `lake pack`/`unpack` use a Clean-local directory + `manifest.json`
    ///   layout, not a Lake/Mathlib cache archive.
    /// - `lake check-lint` verifies its targets ELABORATE; it runs no linter.
    ///
    /// A blanket assertion made the CLI advertise a semver promise the code
    /// does not keep — and Lake supplied 45% of every `v1` claim in the whole
    /// CLI. The invariant is kept (labels still cannot drift silently) but it
    /// now pins the measured state; moving a verb between tiers is a
    /// deliberate edit here, with the evidence.
    #[test]
    fn lake_features_are_build_with_pinned_stability() {
        let downgraded: &[(&[&str], Stability)] = &[
            (&["lake", "upload"], Stability::Building),
            (&["lake", "cache", "get"], Stability::Building),
            (&["lake", "cache", "put"], Stability::Usable),
            (&["lake", "pack"], Stability::Usable),
            (&["lake", "unpack"], Stability::Usable),
            (&["lake", "check-lint"], Stability::Usable),
            // Added 2026-08-26, each from a probe of the shipped binary:
            //
            // - `check-build` is artifact-free again as of 2026-08-27 (the
            //   `check_only` option is honored by redirecting the build to a
            //   scratch directory), but it stays below V1 on cost, not on
            //   truth: reading no artifact means reusing no previous work, so
            //   it re-elaborates the whole project on every invocation.
            // - the three `script` verbs read the CURRENT lakefile only;
            //   scripts inherited from dependency packages are invisible to
            //   all of them, where Lean's `lake script list` shows them.
            //   `script run` additionally lowers to `main : IO Unit`, so it
            //   holds to the bridge's bounded stdout IO subset and cannot bind
            //   a declared `(args)` binder. (The `do`-form MIS-PARSE that put
            //   these three here on 2026-08-26 is fixed: `script <name>
            //   [(args)] do` now yields the bare name and keeps its body.)
            (&["lake", "check-build"], Stability::Usable),
            (&["lake", "script", "list"], Stability::Building),
            (&["lake", "script", "run"], Stability::Building),
            (&["lake", "script", "doc"], Stability::Building),
        ];
        for d in FEATURES {
            assert_eq!(
                d.category,
                Category::Build,
                "{} should be Build",
                d.path_display()
            );
            let want = downgraded
                .iter()
                .find(|(path, _)| *path == d.path)
                .map_or(Stability::V1, |(_, s)| *s);
            assert_eq!(
                d.stability,
                want,
                "{} stability must match its measured implementation state",
                d.path_display()
            );
        }
    }
}
