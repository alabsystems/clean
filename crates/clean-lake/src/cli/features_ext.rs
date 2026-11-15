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
        description: "Prints the `script` blocks the declarative lakefile parser recognizes in the \
                      current project's lakefile. All three Lean spellings parse — \
                      `script <name> [(args)] do`, `script <name> := <body>` and \
                      `script <name> where` — and each prints the BARE declared name, which is the \
                      key `lake script run`/`doc` accept. Scripts inherited from dependencies are \
                      NOT listed: only the current lakefile is read.",
        category: Category::Build,
        stability: Stability::Building,
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
        description: "Lowers the named script's body into a synthetic `main : IO Unit` module and \
                      executes it through the same native bridge as `lake run`, forwarding trailing \
                      arguments and preserving the child exit code. The lookup reads the CURRENT \
                      lakefile only, not inherited manifests. A script with an empty body is \
                      REFUSED (it would otherwise run an empty `pure ()` and exit 0, reporting \
                      success for work that never happened). Two bounds remain: bodies must stay \
                      inside the bridge's stdout IO subset (`IO.print`/`IO.println`, \
                      do-sequencing), and a declared argument binder (`script s (args) do`) is \
                      parsed and reported but NOT bound in the synthetic `main : IO Unit`, so a \
                      body that reads it cannot be lowered. Both fail closed rather than delegating \
                      to `lean --run`.",
        category: Category::Build,
        stability: Stability::Building,
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
        description: "Prints a script's recorded documentation and body. The only documentation \
                      spelling read is a `doc := \"...\"` field inside ANY script block form — \
                      `script <name> where`, `script <name> do`, and `script <name> := ...` alike \
                      — a Lean `/-- ... -/` docstring above the declaration is NOT captured and \
                      reports \"No documentation available\". Subject to the same lookup limit as \
                      `lake script run`: the current lakefile only, not scripts inherited from \
                      dependencies.",
        category: Category::Build,
        stability: Stability::Building,
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
        summary: "Report the configured build cache (no remote fetch yet)",
        description: "Reports the configured cache locations. It does NOT fetch anything — remote \
                      fetch is not implemented — and it takes exactly one of three branches. If the \
                      project declares a `cache` executable, it prints the `clean lake exe cache \
                      get` invocation for you to run. Otherwise, if `.lake/cache` or `.lake/cloud` \
                      exists it reports each one's entry count (the usual outcome once `clean lake \
                      cache put` has run, since that creates `.lake/cache`). If neither exists it \
                      reports that no cache is configured and names the two ways to set one up.",
        category: Category::Build,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean lake cache get",
            what: "report the configured cache locations",
        }],
        see_also: &["lake cache put", "lake cache add"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "cache", "put"],
        summary: "Copy built .olean files into the local cache directory",
        description: "Copies locally built `.olean` files into `.lake/cache`. Cloud upload is not \
                      implemented — the command says so and stops, so nothing reaches a remote that \
                      another machine could fetch.",
        category: Category::Build,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean lake cache put",
            what: "copy built oleans into the local cache",
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
        description: "Copies specific files (or every built `.olean` if none are listed) directly \
                      into `.lake/cache`, flat, by file name — there is no cache index. `lake cache \
                      put` does NOT read what `add` placed: it rescans the build tree itself, so \
                      `add` is for hand-staging files `put`'s scan would not pick up.",
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
        description: "Runs Clean's BUILT-IN source lints over the project's library targets (or a \
                      single target by name) and reports findings — the lakefile grammar has no \
                      declared-linter concept, so project-declared linters are neither discovered \
                      nor run. Scope: every module of each library (its `globs` when it sets \
                      them, which replace its roots as in Lake; otherwise its roots and their \
                      submodules) and every workspace module they import; the count is printed. The \
                      lint is syntactic: nothing is elaborated or kernel-checked, so a clean lint \
                      credits no declaration (`lake check-build` checks them). Does not fix \
                      anything. `lake check-lint` does NOT preview these results: it only \
                      verifies the targets elaborate.",
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
        summary: "Report whether the project builds",
        description: "Reports whether every target builds, exiting non-zero with a per-module error \
                      list if any does not. It is artifact-free: every module is elaborated in \
                      dependency order into a scratch directory that is deleted when the command \
                      returns, so the project's `.lake/build` is neither written nor read. Because \
                      it reads no existing artifact it cannot inherit a verdict from one — it \
                      re-elaborates every module from source every time, which is what makes the \
                      answer a check, and which also means it is never cheaper than `lake build`.",
        category: Category::Build,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean lake check-build",
            what: "report whether every target builds (a scratch dir is used and deleted; the project's .lake/build is untouched)",
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
        description: "Analogue of `lake test` that elaborates the test targets and lists what it \
                      WOULD run without executing any test body — verified: a test whose body \
                      prints stays silent here. Like `lake check-build` the elaboration is \
                      artifact-free: it runs in a scratch directory that is deleted on return, so \
                      the project's `.lake/build` is untouched.",
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
        summary: "Check that the lint targets resolve and elaborate",
        description: "Resolves the library targets that `lake lint` would run over and verifies they \
                      ELABORATE (a check-only build), then lists them. It does not run linter \
                      analyses and produces no lint diagnostics — use `lake lint` for those. An \
                      unknown target name (the optional positional argument — there is no \
                      `--target` flag) is refused rather than reported as zero targets.",
        category: Category::Build,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean lake check-lint",
            what: "check that every lint target elaborates",
        }],
        see_also: &["lake lint", "lake check-build"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "pack"],
        summary: "Collect built .olean files into a distribution DIRECTORY",
        description: "Copies every built `.olean` in the current workspace into an output DIRECTORY \
                      alongside a `manifest.json`. This is a Clean-local layout, NOT a Lake/Mathlib \
                      cache archive: no tarball is produced, and the command prints the `tar` \
                      invocation to run if an archive is wanted.",
        category: Category::Build,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean lake pack --output dist",
            what: "collect built oleans into a distribution directory",
        }],
        see_also: &["lake unpack", "lake upload"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "unpack"],
        summary: "Restore .olean files from a `lake pack` directory",
        description: "Restores `.olean` files from a directory previously produced by `lake pack` \
                      into the local build tree, so the project can be used without re-building. \
                      Reads the Clean-local `manifest.json` layout, not a Lake/Mathlib cache \
                      archive.",
        category: Category::Build,
        stability: Stability::Usable,
        examples: &[Example {
            cmd: "clean lake unpack dist",
            what: "restore oleans from a pack directory",
        }],
        see_also: &["lake pack"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "upload"],
        summary: "Reservoir publish — DECLARED, NOT IMPLEMENTED",
        description: "Intended to publish the current build artifacts to Reservoir (the Lean \
                      package registry). NOT IMPLEMENTED: the command validates that a build \
                      directory exists, collects the artifact list, and then fails with \
                      \"Reservoir upload is not implemented (TODO #421)\" — stating that this is \
                      not a configuration problem, because the Reservoir API is undocumented and \
                      there is no endpoint or credential format to set up. `--dry-run` DOES print \
                      the plan: it lists every artifact that would be sent and exits 0. A build \
                      directory with no artifacts also exits 0, reporting that it found none.",
        category: Category::Build,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean lake upload",
            what: "currently fails: Reservoir upload is not implemented",
        }],
        see_also: &["lake pack"],
        references: COMMON_REFS,
        domain_root: Some("lake"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["lake", "verify-fresh"],
        summary: "Verify built .olean artifacts are exactly what their current source builds to",
        description: "Two fail-closed checks per --module. (1) Cake's import signature: \
                      stale iff the source declares an import the built `.olean` lacks. (2) \
                      Fresh-build digest: the module and its in-project dependencies are \
                      rebuilt from source into a scratch directory (the project's own build \
                      directory is neither read nor written) and the artifact on disk — \
                      `.olean`, `.olean.server`, `.olean.private` — must be byte-identical to \
                      that build. A rewritten or stale artifact is a DIGEST MISMATCH; an \
                      artifact `clean lake build` did not write (another producer's header \
                      git hash) cannot be reproduced and is reported as such. Exits non-zero \
                      unless every module passes both. Default search path: \
                      `.lake/build/lib/lean`, then `.lake/build/lib`.",
        category: Category::Build,
        stability: Stability::V1,
        examples: &[Example {
            cmd: "clean lake verify-fresh --source-root . --module K1Lib",
            what: "check a clean-built module's artifact against a fresh build of its source",
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
