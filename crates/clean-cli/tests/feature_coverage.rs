// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Drift-prevention tests for Epic #3436.
//!
//! These tests enforce two invariants:
//!
//! 1. **`feature_coverage_matches_clap`** — every clap subcommand path is
//!    either backed by a matching `FeatureDescriptor` or is explicitly listed
//!    as a meta command (`features`, `help`, `repl`). Every descriptor must
//!    correspond to a routable clap path.
//! 2. **`every_feature_has_example`** — every descriptor exposes at least one
//!    example, and each example's `cmd` parses via
//!    `clean_features::try_parse_example` against the **real** `clean` clap
//!    tree (`clean_cli::__test_support::TestCli`). A companion negative test,
//!    `negative_example_rejects_invalid_cmd`, ensures the parser rejects
//!    unknown top-level verbs so any future regression to a permissive
//!    trampoline (e.g. `external_subcommand`) is caught immediately (#3481).
//!
//! Phase 2 seeds the registry from per-crate `cli` modules; both drift tests
//! must stay green as the registry grows.
//!
//! Phase 4 meta-gate (#3455) — `filter_by_stability_*` — asserts that the
//! `clean features --stability <slug>` filter parses through the real clap
//! grammar and that the live filter predicate returns only descriptors at
//! the requested stability level. The `experimental` case doubles as the
//! Phase 4 coverage gate: once #3451 (`clean verify rust`) and siblings
//! land, the filter must surface them as experimental.
//!
//! Design: `designs/2026-04-18-unified-cli-feature-index.md`.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use clap::Parser;
use clean_cli::__test_support::{
    all_features, collect_clap_paths, feature_sources, filter_descriptors, meta_paths, TestCli,
};
use clean_features::{
    ensure_has_example, ensure_unique_paths, Category, FeatureDescriptor, RefKind, Stability,
};

fn path_as_strings(path: &[&'static str]) -> Vec<String> {
    path.iter().map(|s| (*s).to_owned()).collect()
}

#[test]
fn feature_coverage_matches_clap() {
    let clap_paths: Vec<Vec<String>> = collect_clap_paths();
    assert!(
        !clap_paths.is_empty(),
        "clap tree must expose at least one subcommand"
    );

    let meta: HashSet<Vec<String>> = meta_paths().into_iter().collect();
    let descriptors: Vec<&'static FeatureDescriptor> = all_features();

    // Uniqueness: descriptor paths must be distinct.
    ensure_unique_paths(&descriptors).expect("descriptor paths must be unique");

    let descriptor_paths: HashSet<Vec<String>> = descriptors
        .iter()
        .map(|d| path_as_strings(d.path))
        .collect();

    // (1) Every clap path has a descriptor OR is meta.
    // Only require coverage for *leaf* clap paths — intermediate aggregator
    // groups (e.g. `lake` as a group containing `lake build`, `lake clean`,
    // etc.) are not themselves invocable as features. We detect aggregators
    // by whether any other clap path extends them.
    let mut non_leaf: HashSet<Vec<String>> = HashSet::new();
    for path in &clap_paths {
        for i in 1..path.len() {
            non_leaf.insert(path[..i].to_vec());
        }
    }

    for path in &clap_paths {
        if non_leaf.contains(path) {
            continue; // aggregator, not a leaf feature
        }
        if meta.contains(path) {
            continue; // explicitly meta (features, help, repl)
        }
        assert!(
            descriptor_paths.contains(path),
            "clap path {path:?} has no matching descriptor \
             (add one to a domain crate's cli::FEATURES, or add to META_PATHS \
              if it's a meta-command)"
        );
    }

    // (2) Every descriptor must correspond to some clap path (routable).
    //
    // Exception (Phase 3.5, #3513): descriptors under `Category::OperatorTools`
    // document standalone operator binaries (`mathverse_convert`, `mathverse_shard`)
    // that are intentionally NOT wired into the unified `clean` clap tree.
    // They participate in the feature index so `clean features` can discover
    // them, but they have no matching clap path and must be skipped here.
    let clap_set: HashSet<Vec<String>> = clap_paths.iter().cloned().collect();
    for descriptor in &descriptors {
        if descriptor.category == Category::OperatorTools {
            continue;
        }
        let path = path_as_strings(descriptor.path);
        assert!(
            clap_set.contains(&path),
            "descriptor path `{}` is not routable — add the matching clap \
             subcommand or remove the descriptor",
            descriptor.path_display()
        );
    }
}

#[test]
fn every_feature_has_example() {
    let descriptors: Vec<&'static FeatureDescriptor> = all_features();

    assert!(
        !descriptors.is_empty(),
        "Phase 2 registry must not be empty — at least one crate's FEATURES \
         should be registered via registry::all_features"
    );

    for descriptor in &descriptors {
        ensure_has_example(descriptor).unwrap_or_else(|e| {
            panic!(
                "descriptor `{}` must have ≥1 example: {e}",
                descriptor.path_display()
            )
        });

        // Exception (Phase 3.5, #3513): `Category::OperatorTools` descriptors
        // document standalone binaries invoked via
        // `cargo run --locked -p … --bin …`.
        // Their examples are intentionally not parseable by the `clean` clap
        // grammar, so skip the parse assertion for that category.
        if descriptor.category == Category::OperatorTools {
            continue;
        }

        for (index, example) in descriptor.examples.iter().enumerate() {
            clean_features::try_parse_example::<TestCli>(example.cmd).unwrap_or_else(|e| {
                panic!(
                    "descriptor `{}` example #{index} ({}) failed to parse: {e}",
                    descriptor.path_display(),
                    example.cmd
                )
            });
        }
    }
}

#[test]
fn negative_example_rejects_invalid_cmd() {
    // Drift guard (#3481): the real `Cli` parser must reject unknown
    // top-level verbs. Phase 1 used a stub with
    // `#[command(external_subcommand)]` that silently accepted *any* argv,
    // so malformed descriptor examples
    // wouldn't fire. This negative test asserts the stub bug is fixed: if
    // someone ever re-introduces a permissive trampoline, this assertion
    // will fail.
    let res = clean_features::try_parse_example::<TestCli>("clean totally-not-a-command");
    assert!(
        res.is_err(),
        "clap must reject unknown top-level verbs; \
         if this passes, the example-parse drift test is back to using a stub parser"
    );
}

#[test]
fn registry_is_non_empty_in_phase_2_plus() {
    // Phase 2+ must leave the registry non-empty. This guards against
    // accidentally regressing all descriptors back out. The mathverse descriptors
    // from Epic #3436 / issue #3440 are part of the expected non-empty set;
    // #3479 landed the lake descriptor batch. The registry is expected to
    // grow — never shrink to zero — as more domain crates migrate.
    let descriptors = all_features();
    assert!(
        !descriptors.is_empty(),
        "registry must expose at least one descriptor once Phase 2+ lands"
    );
}

#[test]
fn registry_contains_discover_feature() {
    // Phase 3 (#3449): `clean discover` must appear in the registry.
    let descriptors = all_features();
    assert!(
        descriptors.iter().any(|d| d.path == ["discover"]),
        "expected `clean discover` descriptor in the registry; \
         found paths: {:?}",
        descriptors
            .iter()
            .map(|d| d.path_display())
            .collect::<Vec<_>>()
    );
}

#[test]
fn registry_contains_tlaps_bench_feature() {
    // Phase 3 (#3448): `clean tlaps bench` must appear in the registry.
    let descriptors = all_features();
    assert!(
        descriptors.iter().any(|d| d.path == ["tlaps", "bench"]),
        "expected `clean tlaps bench` descriptor in the registry; \
         found paths: {:?}",
        descriptors
            .iter()
            .map(|d| d.path_display())
            .collect::<Vec<_>>()
    );
}

#[test]
fn registry_contains_mathverse_convert_operator_tool_descriptor() {
    // Phase 3.5 (#3513): descriptor-only surface for the standalone
    // `mathverse_convert` binary. The descriptor lives under
    // `Category::OperatorTools` and is exempt from the clap-routability
    // drift check above. Acceptance criterion: the descriptor must appear in
    // `registry::all_features()` with the expected path and category so
    // `clean features --category operator-tools` can surface it.
    let descriptors = all_features();
    let found = descriptors
        .iter()
        .find(|d| d.path == ["mathverse", "convert"])
        .unwrap_or_else(|| {
            panic!(
                "expected `mathverse convert` operator-tool descriptor in the registry; \
                 found paths: {:?}",
                descriptors
                    .iter()
                    .map(|d| d.path_display())
                    .collect::<Vec<_>>()
            )
        });
    assert_eq!(
        found.category,
        Category::OperatorTools,
        "`mathverse convert` descriptor must be Category::OperatorTools (found {:?})",
        found.category,
    );
    assert!(
        !found.examples.is_empty(),
        "`mathverse convert` operator-tool descriptor must expose at least one example"
    );
}

#[test]
fn registry_contains_mathverse_shard_operator_tool_descriptor() {
    // Phase 3.5 (#3513): descriptor-only surface for the standalone
    // `mathverse_shard` binary. Companion to the `mathverse convert` test above.
    let descriptors = all_features();
    let found = descriptors
        .iter()
        .find(|d| d.path == ["mathverse", "shard"])
        .unwrap_or_else(|| {
            panic!(
                "expected `mathverse shard` operator-tool descriptor in the registry; \
                 found paths: {:?}",
                descriptors
                    .iter()
                    .map(|d| d.path_display())
                    .collect::<Vec<_>>()
            )
        });
    assert_eq!(
        found.category,
        Category::OperatorTools,
        "`mathverse shard` descriptor must be Category::OperatorTools (found {:?})",
        found.category,
    );
    assert!(
        !found.examples.is_empty(),
        "`mathverse shard` operator-tool descriptor must expose at least one example"
    );
}

#[test]
fn operator_tool_descriptors_validate_against_lint_rules() {
    // Phase 3.5 (#3513): every operator-tool descriptor must still satisfy
    // the generic lint rules (non-empty examples, unique paths) even though
    // they are exempt from the clap-routability and example-prefix checks.
    // This guards against the exemption silently turning into a
    // "descriptor with no examples" loophole.
    let descriptors: Vec<&'static FeatureDescriptor> = all_features()
        .into_iter()
        .filter(|d| d.category == Category::OperatorTools)
        .collect();
    assert!(
        !descriptors.is_empty(),
        "expected at least one Category::OperatorTools descriptor (mathverse_convert, mathverse_shard)"
    );
    ensure_unique_paths(&descriptors).expect("operator-tool descriptor paths must be unique");
    for d in &descriptors {
        ensure_has_example(d).unwrap_or_else(|e| {
            panic!(
                "operator-tool descriptor `{}` must have at least one example: {e}",
                d.path_display()
            )
        });
        // Operator-tool examples are shell commands starting with locked
        // `cargo run --locked`, not `clean`. Assert the prefix so descriptors can't
        // silently land with a stale or lockfile-floating example.
        for (index, example) in d.examples.iter().enumerate() {
            assert!(
                example.cmd.starts_with("cargo run --locked"),
                "operator-tool descriptor `{}` example #{index} (`{}`) must start with \
                 `cargo run --locked` (invoking the standalone binary directly \
                 with the tracked lockfile)",
                d.path_display(),
                example.cmd
            );
        }
    }
}

#[test]
fn phase_two_registry_contains_check_eval_repl() {
    // Phase 2 of Epic #3436 migrates `check`, `eval`, and `repl` into
    // per-crate descriptor arrays. This test asserts the three expected
    // paths are present so future migrations don't silently regress.
    let descriptors = all_features();
    let paths: HashSet<Vec<String>> = descriptors
        .iter()
        .map(|d| path_as_strings(d.path))
        .collect();

    for expected in &[vec!["check"], vec!["eval"], vec!["repl"]] {
        let path: Vec<String> = expected.iter().map(|s| (*s).to_owned()).collect();
        assert!(
            paths.contains(&path),
            "Phase 2 descriptor registry must include `{}` — check that \
             `registry::all_features()` extends the owning crate's \
             `cli::FEATURES` slice",
            path.join(" ")
        );
    }
}

/// Assert that `clean features --stability <slug>` parses through the real
/// clap grammar and that applying the same filter the command uses at runtime
/// returns only descriptors at the requested stability level.
///
/// Used by the four drift tests below (one per stability level). Keeping the
/// logic in a helper means any new level added to
/// `clean_features::Stability::all()` only needs one new one-line test, not a
/// fresh copy of the parse-plus-filter scaffolding.
///
/// Phase 4 meta-gate (#3455): `Stability::Experimental` is the marker every
/// Phase 4 surface (`verify rust`, `verify tla`, `compile`, `auto`) must
/// carry. The experimental case below doubles as the coverage test for that
/// gate — it confirms the filter actually returns the experimental surface
/// once it lands, and it tolerates the empty case today so the test lands
/// before Phase 4 surfaces do.
fn assert_stability_filter_returns_only(level: Stability, slug: &str) {
    // (1) The real clap grammar must accept `--stability <slug>` for every
    // declared level. If a future refactor of `cli_args::Commands::Features`
    // drops the flag or renames a slug, this parse fails immediately.
    let argv = ["clean", "features", "--stability", slug];
    TestCli::try_parse_from(argv).unwrap_or_else(|e| {
        panic!("`clean features --stability {slug}` must parse via TestCli: {e}")
    });

    // (2) Applying the same filter the command dispatches returns only
    // descriptors at the requested stability level. We use the crate's
    // `__test_support::filter_descriptors` re-export so the assertion tracks
    // the real filter function — replicating the predicate locally would
    // defeat the drift-test purpose if `cmd_features::filter_descriptors`
    // ever grew additional logic.
    let out = filter_descriptors(all_features(), None, Some(level), None);

    for descriptor in &out {
        assert_eq!(
            descriptor.stability,
            level,
            "filter_descriptors(stability = {level:?}) returned descriptor `{}` \
             at stability {:?} — filter is broken",
            descriptor.path_display(),
            descriptor.stability,
        );
    }
}

#[test]
fn filter_by_stability_experimental_returns_only_experimental() {
    // Phase 4 meta-gate (#3455): ensures `clean features --stability
    // experimental` is both routable and correctly filtered. Empty output
    // is tolerated — this test still catches regressions the moment the
    // first Phase 4 descriptor lands (e.g. #3451 `clean verify rust`).
    assert_stability_filter_returns_only(Stability::Experimental, "experimental");
}

#[test]
fn filter_by_stability_v1_returns_only_v1() {
    assert_stability_filter_returns_only(Stability::V1, "v1");
}

#[test]
fn filter_by_stability_usable_returns_only_usable() {
    assert_stability_filter_returns_only(Stability::Usable, "usable");
}

#[test]
fn filter_by_stability_building_returns_only_building() {
    assert_stability_filter_returns_only(Stability::Building, "building");
}

#[test]
fn domain_root_matches_path_root_for_every_descriptor() {
    // Phase 4/5 drift gate (Epic #3436, issue #3483): whenever a descriptor
    // sets `domain_root`, it must equal `path[0]`. `domain_root = None` is
    // allowed for migration opt-out but any value MUST match the path root so
    // `clean features` grouping by verb tree stays consistent.
    let descriptors = all_features();
    for descriptor in &descriptors {
        if let Some(root) = descriptor.domain_root {
            assert_eq!(
                descriptor.path[0],
                root,
                "descriptor `{}` declares domain_root=`{root}` but path[0]=`{}`",
                descriptor.path_display(),
                descriptor.path[0]
            );
        }
    }
}

#[test]
fn alternative_forms_start_with_clean_prefix() {
    // Phase 5 drift gate: user-facing aliases in `alternative_forms` are full
    // unified-CLI invocations, so they must begin with `clean ` and include at
    // least one additional subcommand token. OperatorTools descriptors are the
    // intentional exception: they document standalone binaries that remain
    // outside the top-level clap tree but still need machine-readable coverage
    // in `clean features --category operator-tools` (#3513).
    let descriptors = all_features();
    for descriptor in &descriptors {
        for form in descriptor.alternative_forms {
            if descriptor.category == Category::OperatorTools {
                assert!(
                    !form.starts_with("clean "),
                    "operator-tool descriptor `{}` alt form `{form}` should name \
                     the standalone binary, not a unified CLI path",
                    descriptor.path_display()
                );
                assert!(
                    form.split_whitespace().count() == 1,
                    "operator-tool descriptor `{}` alt form `{form}` must be a \
                     single standalone binary token",
                    descriptor.path_display()
                );
                continue;
            }
            assert!(
                form.starts_with("clean "),
                "descriptor `{}` alt form `{form}` must start with `clean `",
                descriptor.path_display()
            );
            assert!(
                form.split_whitespace().count() >= 2,
                "descriptor `{}` alt form `{form}` must have ≥1 subcommand token",
                descriptor.path_display()
            );
        }
    }
}

#[test]
fn feature_gates_are_known_cargo_feature_names() {
    // Phase 5 drift gate: when a descriptor declares `feature_gate: Some(gate)`,
    // the gate name must match one of the known Cargo features exposed by the
    // `clean-cli` binary crate. Cross-crate Cargo.toml parsing is out of scope
    // here, so this test keeps an allowlist synced with `clean-cli/Cargo.toml`
    // `[features]`. Adding a new gate requires bumping this allowlist — a
    // deliberate friction that prevents stale `feature_gate` values from
    // sliding into the registry.
    const KNOWN_GATES: &[&str] = &[
        // Kept in sync with `crates/clean-cli/Cargo.toml` [features].
        "carcara-verify",
        "math-overlays",
    ];
    let descriptors = all_features();
    for descriptor in &descriptors {
        if let Some(gate) = descriptor.feature_gate {
            assert!(
                KNOWN_GATES.contains(&gate),
                "descriptor `{}` declares feature_gate=`{gate}` which is not a known Cargo feature; \
                 add it to KNOWN_GATES in this test and to `clean-cli/Cargo.toml` if needed",
                descriptor.path_display()
            );
        }
    }
}

/// Walk up from the test binary's current working directory looking for the
/// workspace root (the directory containing the root `Cargo.toml` with
/// `[workspace]`). Returns `None` when running in an unusual environment that
/// doesn't include the workspace on disk (the caller then skips any
/// filesystem-backed assertions).
///
/// Used by `references_point_to_existing_files` to resolve repo-relative
/// reference targets without hard-coding an absolute path.
fn find_workspace_root() -> Option<PathBuf> {
    let start = std::env::var("CARGO_MANIFEST_DIR")
        .ok()
        .map(PathBuf::from)?;
    let mut cur: &Path = &start;
    loop {
        let candidate = cur.join("Cargo.toml");
        if candidate.is_file() {
            if let Ok(contents) = std::fs::read_to_string(&candidate) {
                if contents.contains("[workspace]") {
                    return Some(cur.to_owned());
                }
            }
        }
        cur = cur.parent()?;
    }
}

#[test]
fn see_also_entries_are_known_descriptor_paths() {
    // Phase 4/5 drift gate (#3497): every `see_also` entry must be the
    // space-joined form of another descriptor's `path`. A typo like
    // examples with a misspelled root or path segment would ship silently today because
    // nothing cross-references `see_also` against the real registry. This
    // test closes that gap: `see_also` targets now have to resolve to a
    // routable descriptor path, exactly like the ones rendered by
    // `clean features`.
    let descriptors = all_features();
    let known_paths: HashSet<String> = descriptors.iter().map(|d| d.path_display()).collect();
    for descriptor in &descriptors {
        for target in descriptor.see_also {
            assert!(
                known_paths.contains(*target),
                "descriptor `{}` references see_also=`{target}` which is not a known descriptor \
                 path; `see_also` entries must be the space-joined form of another descriptor's \
                 `path` (e.g. `\"kernel verify\"`). Known paths: {:?}",
                descriptor.path_display(),
                {
                    let mut sorted: Vec<&String> = known_paths.iter().collect();
                    sorted.sort();
                    sorted
                }
            );
        }
    }
}

#[test]
fn examples_cmd_starts_with_descriptor_path_prefix() {
    // Phase 4/5 drift gate (#3497): `every_feature_has_example` only checks
    // that an example parses — it does *not* check that the example actually
    // exercises the descriptor's own path. Without this test, a descriptor
    // under `["lake", "build"]` could advertise `"clean check foo.lean"` and
    // ship silently: the parse succeeds (clap accepts `check`), but the
    // example teaches the user the wrong command. Close that gap by requiring
    // every example to begin with `clean <descriptor-path>` token-by-token.
    let descriptors = all_features();
    for descriptor in &descriptors {
        // Exception (Phase 3.5, #3513): `Category::OperatorTools` descriptors
        // document standalone binaries whose examples use
        // `cargo run --locked -p … --bin <binary> -- <verb> …`, not
        // `clean <path> …`.
        // Skip the prefix check for that category; the
        // `operator_tool_descriptors_validate_against_lint_rules` test above
        // asserts the cargo-run prefix instead.
        if descriptor.category == Category::OperatorTools {
            continue;
        }

        for (index, example) in descriptor.examples.iter().enumerate() {
            let tokens: Vec<&str> = example.cmd.split_whitespace().collect();
            assert!(
                tokens.first().copied() == Some("clean"),
                "descriptor `{}` example #{index} (`{}`) must start with the `clean ` binary \
                 prefix",
                descriptor.path_display(),
                example.cmd
            );
            for (seg_index, expected) in descriptor.path.iter().enumerate() {
                let actual = tokens.get(seg_index + 1).copied().unwrap_or_default();
                assert_eq!(
                    actual,
                    *expected,
                    "descriptor `{}` example #{index} (`{}`) has token `{actual}` at position \
                     {seg_index} but the descriptor path requires `{expected}`; examples must \
                     invoke the descriptor's own command",
                    descriptor.path_display(),
                    example.cmd,
                );
            }
        }
    }
}

#[test]
fn references_have_nonempty_label_and_target() {
    // Phase 4/5 drift gate (#3497): a `Reference` with an empty `label` or
    // `target` renders as a blank bullet in `clean help <path>` and in the
    // generated `docs/cli/` tree. Enforce non-empty strings on both fields so
    // descriptors can't land references that produce empty rows downstream.
    // This is a cheap invariant that fires immediately on bad registration.
    let descriptors = all_features();
    for descriptor in &descriptors {
        for (index, reference) in descriptor.references.iter().enumerate() {
            assert!(
                !reference.label.trim().is_empty(),
                "descriptor `{}` reference #{index} has an empty label",
                descriptor.path_display(),
            );
            assert!(
                !reference.target.trim().is_empty(),
                "descriptor `{}` reference #{index} (label=`{}`) has an empty target",
                descriptor.path_display(),
                reference.label,
            );
        }
    }
}

#[test]
fn references_point_to_existing_files() {
    // Phase 4/5 drift gate (#3497): `RefKind::Design` and `RefKind::Doc`
    // references point to markdown (and similar) files living in the
    // workspace. A typo in the path (`"dessigns/foo.md"`) ships silently
    // today because nothing hits the filesystem. Enforce on-disk existence
    // for repo-relative, non-URL targets — the only kinds where existence is
    // well-defined. URLs (`http://`, `https://`) and anchor-only fragments
    // are skipped (URL liveness is out of scope; network tests are flaky).
    //
    // `RefKind::Issue` and `RefKind::Crate` intentionally do not hit disk
    // because they identify logical entities (issue numbers, crate names),
    // not file paths. Those are already constrained elsewhere
    // (`feature_gates_are_known_cargo_feature_names` handles Cargo features;
    // `references_have_nonempty_label_and_target` catches blank values).
    let Some(workspace_root) = find_workspace_root() else {
        // Environmental safety: the test binary runs without a discoverable
        // workspace root (e.g. packaging tarball). Skip rather than false-
        // fail. Production invocations via `cargo test` always find one.
        return;
    };

    let descriptors = all_features();
    for descriptor in &descriptors {
        for (index, reference) in descriptor.references.iter().enumerate() {
            if !matches!(reference.kind, RefKind::Design | RefKind::Doc) {
                continue;
            }
            let target = reference.target;
            if target.starts_with("http://") || target.starts_with("https://") {
                continue;
            }
            // Strip an optional `#anchor` suffix before checking disk —
            // references such as `"docs/DESIGN.md#mathverse-library"` point at an
            // anchor inside a real file.
            let path_part = target.split_once('#').map_or(target, |(head, _)| head);
            if path_part.is_empty() {
                // Pure anchor (`"#foo"`) is not a file path — allow it.
                continue;
            }
            let full = workspace_root.join(path_part);
            assert!(
                full.is_file(),
                "descriptor `{}` reference #{index} (kind={:?}, label=`{}`) points at \
                 `{}` which does not exist on disk (resolved to `{}`). Fix the target or \
                 replace with the correct path relative to the workspace root",
                descriptor.path_display(),
                reference.kind,
                reference.label,
                target,
                full.display(),
            );
        }
    }
}

#[test]
fn experimental_descriptors_carry_stability_notice() {
    // Phase 4/5 drift gate (#3497, #3455): `Stability::Experimental` signals to
    // users that a surface is a research prototype that may change without
    // notice. That contract only reaches users if the descriptor *says so* in
    // the text `clean features` and `clean help <path>` render. Enforce that
    // every Experimental descriptor mentions "Experimental" (case-insensitive)
    // in either `summary` or `description`. Without this test, an Experimental
    // descriptor could ship with a fully-stable-sounding blurb — users would
    // depend on it, then be surprised when it changes.
    //
    // The check is deliberately loose (substring, either field) so authors can
    // frame the notice however reads best. The cost of adding the word to a
    // blurb is tiny; the cost of a user mistaking an Experimental surface for
    // a stable one is much larger.
    let descriptors = all_features();
    for descriptor in &descriptors {
        if descriptor.stability != Stability::Experimental {
            continue;
        }
        let summary_lc = descriptor.summary.to_ascii_lowercase();
        let description_lc = descriptor.description.to_ascii_lowercase();
        assert!(
            summary_lc.contains("experimental") || description_lc.contains("experimental"),
            "descriptor `{}` is Stability::Experimental but neither its summary nor its \
             description mentions \"Experimental\"; `clean help {0}` would render it as if \
             it were stable. Add a stability notice to the summary or description so users \
             see the marker.",
            descriptor.path_display(),
        );
    }
}

#[test]
fn source_slice_domain_roots_match_allowlist() {
    // Phase 4/5 drift gate (#3497, #3483): the registry is assembled from
    // per-crate `FEATURES` slices published under names like
    // `clean_<domain>::cli::FEATURES`. Each slice's owning crate declares in
    // [`clean_cli::__test_support::FeatureSource::allowed_roots`] which
    // top-level verbs it intends to register. A descriptor whose normalized
    // root (`domain_root` when set, else `path[0]`) is not in the allowlist
    // is a slice-rooting leak: a future crate registering `["foo"]` from
    // `clean-bar` would fire here immediately.
    //
    // The allowlist is declared next to the source slice rather than inferred
    // from it — inference would accept whatever the slice already contains
    // and defeat the drift check.
    //
    // The companion `domain_root_matches_path_root_for_every_descriptor` test
    // already asserts `domain_root == path[0]` when set, so the
    // "normalized root" used here is unambiguous.
    for source in feature_sources() {
        assert!(
            !source.slice.is_empty(),
            "feature source `{}` must expose at least one FeatureDescriptor; \
             a zero-descriptor slice would vanish silently from `clean features` without \
             firing any drift check",
            source.name,
        );
        for descriptor in source.slice {
            let root = descriptor.domain_root.unwrap_or(descriptor.path[0]);
            assert!(
                source.allowed_roots.contains(&root),
                "feature source `{}` registered descriptor `{}` rooted at `{root}`, which \
                 is not in the source's allowlisted roots {:?}. Either move the descriptor \
                 to the slice that owns `{root}`, or (if this is a legitimate new root for \
                 the owning crate) extend `allowed_roots` in \
                 `clean_cli::__test_support::feature_sources` with a justifying comment.",
                source.name,
                descriptor.path_display(),
                source.allowed_roots,
            );
        }
    }
}
