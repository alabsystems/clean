// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Static feature descriptor registry for the `clean` CLI.
//!
//! Domain crates register their `FeatureDescriptor` arrays here with one
//! `v.extend(clean_<domain>::cli::FEATURES)` line per crate. The coverage
//! gate in `tests/feature_coverage.rs` asserts that every clap subcommand
//! either has a matching descriptor or is listed in [`META_PATHS`].
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use clean_features::FeatureDescriptor;

/// Collect every `FeatureDescriptor` surfaced by the `clean` binary.
///
/// Registration order is stable: one `v.extend(...)` per owning crate, grouped
/// by top-level verb. Phase 3 absorbed `discover` (#3449), `tlaps bench`
/// (#3448), and `mathverse` (#3440) orphan binaries into the unified CLI; the
/// `lake` subcommand tree migrated in #3479.
#[must_use]
pub(crate) fn all_features() -> Vec<&'static FeatureDescriptor> {
    let mut v: Vec<&'static FeatureDescriptor> = Vec::new();
    // Phase 2 — owning-crate migrations
    v.extend(clean_c_sem::cli::FEATURES);
    // #3451: Rust verification verb (Experimental). Nested under
    // `clean verify rust` so future language migrations can drop in.
    v.extend(clean_rust_sem::cli::FEATURES);
    // #3454: Automation entry point (Experimental). Nested under
    // `clean auto prove` so sibling verbs (`auto premise`, `auto smt`, …)
    // can drop in without reshaping the top-level clap tree.
    v.extend(clean_auto::cli::FEATURES);
    // #3452: TLA+ obligation verification verb (Experimental). Nested under
    // `clean verify tla` next to `verify rust`.
    v.extend(clean_tla::cli::FEATURES);
    v.extend(clean_server::cli::FEATURES);
    v.extend(clean_fold::cli::FEATURES);
    // `commit` verbs live in clean-fold's absorbed `commit` module
    // (ex clean-commit; rearch stage 9 facade consolidation).
    v.extend(clean_fold::commit::cli::FEATURES);
    v.extend(clean_kernel::cli::FEATURES);
    // Phase 3 kernel-verb orphan absorptions (Epic #3436: #3443/#3444/#3446/#3447).
    // Published separately to keep `clean-kernel/src/cli/mod.rs` under the
    // 500-line file-size cap.
    v.extend(clean_kernel::cli::KERNEL_VERB_FEATURES);
    v.extend(clean_elab::cli::FEATURES);
    v.extend(clean_lake::cli::FEATURES);
    v.extend(crate::cli::FEATURES);
    v.extend(crate::cli::bench::FEATURES);
    v.extend(crate::cli::promote::FEATURES);
    v.extend(crate::cmd_research::FEATURES);
    v.extend(crate::cmd_replacement::FEATURES);
    v.extend(crate::cmd_factory::FEATURES);
    v.extend(crate::cmd_math::FEATURES);
    v.extend(crate::cmd_project::FEATURES);
    v.extend(crate::cmd_attempts::FEATURES);
    // `clean prove run/status/list` — submit a Lean goal to a remote / automated
    // prover backend (Aristotle / ax-prover), retrieve the proof, and re-verify
    // it locally (lake build + #print axioms ⊆ foundational allowlist).
    v.extend(crate::cmd_prove::FEATURES);
    // `clean cake build/graduate/verify` — the Layer-1 CAKE project lifecycle
    // (build → graduate → verify) whose handlers live in `clean-cli`.
    v.extend(crate::cmd_cake::FEATURES);
    // `clean solver index-build/stats/weak/vbs-gap/export-dataset` — Phase-1
    // solver-results-cache tooling over the captured telemetry stream.
    v.extend(crate::cmd_solver::FEATURES);
    // `clean vendor fetch/package/status/clean` — vendored-sources lifecycle for
    // offline/reproducible builds (artifact-based; replaces fetch_vendor.sh).
    v.extend(crate::cmd_vendor::FEATURES);
    // Artifact system v0 (master design v2 §5.6): `clean artifacts
    // list/get/verify/extract` — generic release-artifact logistics with
    // mandatory fail-closed blake3 manifest verification.
    v.extend(crate::cmd_artifacts::FEATURES);
    // `clean audit trust-ledger` — per-declaration recursive trust ledger
    // diagnostic ported from the divergent `consolidation` branch.
    v.extend(crate::cmd_audit::FEATURES);
    // Phase 3 — absorbed orphan binaries
    v.extend(clean_discovery::cli::FEATURES);
    // `tlaps` verbs live in clean-tla's absorbed `bench::cli` module
    // (ex clean-tlaps-bench; rearch stage 9 facade consolidation).
    v.extend(clean_tla::bench::cli::FEATURES);
    v.extend(clean_mathverse::cli::FEATURES);
    // Phase 3.5 (#3512) — browse-oriented mathverse verbs absorbed into the
    // unified `clean mathverse <verb>` tree (list / sample / deps / version).
    // Kept in a separate descriptor module so each file stays under the
    // 500-line cap (see `designs/2026-04-19-epic-3436-orphan-triage.md`).
    v.extend(clean_mathverse::cli::BROWSE_FEATURES);
    // Phase 3.5 (#3512) — the 7 passthrough-absorbed mathverse verbs
    // (find / graph / diff / verify / download / export / release) that
    // regressed between `ae3772027` (original absorption) and
    // `f43429751` (partial re-type) and were re-absorbed via
    // `PassthroughArgs` delegation. See `descriptors_passthrough.rs` for
    // the full rationale on why passthrough (not typed-arg) is the right
    // design for these 7 verbs.
    v.extend(clean_mathverse::cli::PASSTHROUGH_FEATURES);
    // Phase 3.5 (#3513) — descriptor-only surfaces for the standalone
    // `mathverse_convert` and `mathverse_shard` operator binaries. These carry
    // `Category::OperatorTools` and are exempt from the clap-routability
    // drift check because they are intentionally not absorbed into the
    // unified `clean` clap tree (see `designs/2026-04-19-epic-3436-orphan-triage.md`).
    v.extend(clean_mathverse::cli::OPERATOR_TOOLS_FEATURES);
    v.extend(clean_olean::cli::FEATURES);
    v.extend(clean_lsp::cli::FEATURES);
    // Phase 3.5 — `clean verify proof` (#3511).
    #[cfg(feature = "sat-verify")]
    v.extend(clean_verify::cli::FEATURES);
    // Phase 4 — #3453: `clean compile` MVP (Experimental).
    v.extend(clean_compiler::cli::FEATURES);
    v
}

/// Clap subcommand paths that are intentionally _not_ backed by a
/// `FeatureDescriptor`.
///
/// Two categories live here:
///
/// 1. **True meta commands** (`features`, `help`) — these describe or host
///    the feature index itself rather than expose a new domain feature.
/// 2. **Pre-existing paths not yet migrated** — clap subcommands whose owning
///    crate still needs a `cli::FEATURES` array.
///
/// The goal of the gate is to prevent **new** clap paths from being added
/// without a matching descriptor once Phase 2+ lands. Pre-existing paths are
/// grandfathered until migrated.
pub(crate) const META_PATHS: &[&[&str]] = &[
    // --- True meta commands ---
    &["features"],
    &["help"],
];
