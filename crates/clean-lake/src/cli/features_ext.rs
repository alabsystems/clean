// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended `FeatureDescriptor` entries for the `lake` domain.
//!
//! Split out of [`super::features`] so neither file exceeds the 500-line cap
//! (see `design doc` / `rust_excellence.md`). The parent module concatenates
//! [`super::features::FEATURES_CORE`] and [`FEATURES_EXT`] into the public
//! `FEATURES` constant.
//!
//! Contains the `script`, `cache`, `lint`, `check-*`, `pack`, `unpack`,
//! `upload`, `verify-fresh`, `goodness`, `smoke`, and `serve` verbs —
//! everything
//! beyond the core build/test verbs.

use clean_features::{Category, Example, FeatureDescriptor, Stability};

use super::features_refs::COMMON_REFS;

/// Extended `lake` descriptors: `script`, `cache`, `lint`, `check-*`, `pack`,
/// `unpack`, `upload`. Concatenated with [`super::features::FEATURES_CORE`]
/// by `features::FEATURES`.
pub(super) const FEATURES_EXT: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["lake", "script", "list"],
        summary: "List scripts declared in lakefile.lean",
        description: "Prints every named `script` block declared in the current project's lakefile, \
                      including inherited scripts from dependencies.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake script list",
            what: "enumerate project scripts",
        }],
        see_also: &["lake script run", "lake script doc"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "script", "run"],
        summary: "Invoke a named script",
        description: "Runs the script identified by `name`, passing any trailing arguments through to it. \
                      The script is looked up in the current lakefile and inherited manifests.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake script run build-docs",
            what: "invoke a script by name",
        }],
        see_also: &["lake script list", "lake script doc"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "script", "doc"],
        summary: "Show documentation for a named script",
        description: "Prints the docstring attached to a script declared in `lakefile.lean`. Useful for \
                      discovering what a script does before invoking it.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake script doc build-docs",
            what: "show the documentation for a script",
        }],
        see_also: &["lake script list", "lake script run"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "cache", "get"],
        summary: "Download cached .olean files",
        description: "Fetches precompiled `.olean` files from the configured build cache, skipping \
                      modules that have not changed. Accelerates cold builds of large dependencies.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake cache get",
            what: "populate the local cache from remote",
        }],
        see_also: &["lake cache put", "lake cache add"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "cache", "put"],
        summary: "Upload .olean files to the build cache",
        description: "Pushes locally built `.olean` files to the configured remote cache so other \
                      machines can pick them up via `lake cache get`.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake cache put",
            what: "publish the local cache to remote",
        }],
        see_also: &["lake cache get", "lake cache add"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "cache", "add"],
        summary: "Add files to the local build cache",
        description: "Registers specific files (or every built `.olean` if none are listed) with the \
                      local cache index so they become eligible for subsequent `lake cache put` uploads.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake cache add",
                what: "index every built file",
            },
            Example {
                cmd: "clean lake cache add Foo.olean Bar.olean",
                what: "index specific files",
            },
        ],
        see_also: &["lake cache get", "lake cache put"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "lint"],
        summary: "Run configured linters on the project",
        description: "Invokes every linter declared for the project (or a single target by name) and \
                      reports findings. Does not fix anything; run `lake check-lint` to preview results \
                      without modifying state.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake lint",
            what: "lint every target",
        }],
        see_also: &["lake check-lint"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "check-build"],
        summary: "Report whether the project would build",
        description: "Performs the same analysis as `lake build` but stops before producing artifacts. \
                      Useful as a fast local/release gate when only type-check results are needed.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake check-build",
            what: "dry-run the full project build",
        }],
        see_also: &["lake build", "lake check-test", "lake check-lint"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "check-test"],
        summary: "Report whether the project's tests would pass",
        description: "Dry-run analogue of `lake test`: runs the same checks without executing test \
                      bodies, so local/release checks can surface failures early.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake check-test",
            what: "dry-run every test target",
        }],
        see_also: &["lake test", "lake check-build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "check-lint"],
        summary: "Report whether the project would pass linting",
        description: "Dry-run analogue of `lake lint`: runs linter analyses without applying fixes, \
                      producing the same diagnostic output for automation.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake check-lint",
            what: "dry-run every linter",
        }],
        see_also: &["lake lint", "lake check-build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "pack"],
        summary: "Pack built .olean files into a release archive",
        description: "Bundles every built `.olean` in the current workspace into a single archive \
                      (written to `--output` if provided, otherwise a conventional filename).",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake pack --output dist.tar.zst",
            what: "produce a release archive",
        }],
        see_also: &["lake unpack", "lake upload"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "unpack"],
        summary: "Unpack a prior `lake pack` archive",
        description: "Restores `.olean` files from a previously-packed archive into the local build \
                      tree so the project can be used without re-building.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake unpack dist.tar.zst",
            what: "restore a release archive",
        }],
        see_also: &["lake pack"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "upload"],
        summary: "Upload build artifacts to Reservoir",
        description: "Publishes the current build artifacts to Reservoir (the Lean package registry). \
                      Use `--dry-run` to print the upload plan without mutating remote state.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake upload --dry-run",
                what: "preview a Reservoir upload",
            },
            Example {
                cmd: "clean lake upload",
                what: "publish to Reservoir",
            },
        ],
        see_also: &["lake pack"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "verify-fresh"],
        summary: "Verify built .olean artifacts are content-fresh vs their .lean source",
        description: "Cake's content-hash freshness check: for each --module, compares the \
                      source's `import` lines against the imports recorded in the built \
                      `.olean` (stale iff the source declares an import the .olean lacks — a \
                      module was added but not rebuilt). Reports a per-module verdict plus a \
                      reproducible env_digest and exits non-zero on any stale module. Run it \
                      before graduating from an imported environment.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake verify-fresh --source-root crown-proofs/lean --module Crownproof",
            what: "check the project's olean tree is fresh",
        }],
        see_also: &["lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "goodness"],
        summary: "Report a constant's Cake profile: semantic identity, goodness, complexity",
        description: "Loads the `.olean` env and reports, for one --constant: its semantic \
                      identity (defeq + Tier-1.5 rewrite-canonical digests), its proof \
                      goodness (G mass + F weakest-link floor = the per-theorem \
                      bedrock-distance from the 3 foundational axioms, with the domain \
                      axioms / trust markers that lower it), and its derivation complexity. \
                      The queryable 'how good / how far from the 3 axioms' tool.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake goodness --module Crownproof --olean-search-path PATH --constant Crownproof.network_bridge",
            what: "profile a theorem's identity, goodness, and complexity",
        }],
        see_also: &["lake verify-fresh"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "smoke"],
        summary: "Run the governed Lake replacement smoke and write its JSON evidence artifact",
        description: "Runs the init/build/test sequence of the `clean lake init` template in a \
                      throwaway temp project, entirely through clean-owned in-process Lake \
                      handlers (never delegating to Lean4's `lean`/`lake` binaries), and writes \
                      per-step pass/fail evidence as JSON. This is the generator for the \
                      lake-workflow replacement row's artifact \
                      `reports/lake-replacement-smoke.json`; it exits non-zero when any step \
                      fails, after still recording the honest per-step results.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[
            Example {
                cmd: "clean lake smoke",
                what: "run the smoke and write reports/lake-replacement-smoke.json",
            },
            Example {
                cmd: "clean lake smoke --report reports/lake-replacement-smoke.json",
                what: "run the smoke with an explicit artifact path",
            },
        ],
        see_also: &["lake init", "lake build", "lake test"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "serve"],
        summary: "Start the Clean language server over stdio for this project",
        description: "Lake-compatible editor entry point: editors (the VS Code Lean 4 extension \
                      among them) launch `lake serve --` in the project root and speak LSP over \
                      the child's stdio. Loads the workspace configuration (lakefile + \
                      lean-toolchain) fail-closed, enters the project root, and runs the Clean \
                      LSP server until the client closes the stream.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake serve",
            what: "serve LSP over stdio for the current project",
        }],
        see_also: &["lake env", "lake build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
];
