// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean auto prove` clap parsing, demo catalog execution,
//! and [`FEATURES`] descriptor shape. Mirror of
//! `crates/clean-rust-sem/src/cli/tests.rs` so both Phase-4 Experimental
//! CLI surfaces are drift-guarded the same way.

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::{catalog, run, AutoCliError, AutoCommands, AutoProveArgs, FEATURES};

/// Tiny parser embedding [`AutoProveArgs`] so we can exercise clap
/// integration in isolation from the top-level `clean-cli` tree.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    #[command(subcommand)]
    Auto(AutoCommands),
}

fn parse_args(argv: &[&str]) -> AutoProveArgs {
    let parsed = Harness::try_parse_from(argv).expect("clap parse");
    match parsed.command {
        Top::Auto(AutoCommands::Prove(args)) => args,
        Top::Auto(AutoCommands::Premise(_)) => panic!("expected auto prove args"),
    }
}

#[test]
fn auto_prove_list_parses() {
    let args = parse_args(&["clean", "auto", "prove", "--list"]);
    assert!(args.list);
    assert!(args.demo.is_none());
    assert!(!args.verbose);
    // Default budget matches the documented surface.
    assert_eq!(args.budget, 5_000);
}

#[test]
fn auto_prove_demo_parses() {
    let args = parse_args(&["clean", "auto", "prove", "--demo", "eq_refl"]);
    assert_eq!(args.demo.as_deref(), Some("eq_refl"));
    assert!(!args.list);
}

#[test]
fn auto_prove_verbose_and_budget_parse() {
    let args = parse_args(&[
        "clean",
        "auto",
        "prove",
        "--demo",
        "eq_refl",
        "--budget",
        "1500",
        "--verbose",
    ]);
    assert!(args.verbose);
    assert_eq!(args.budget, 1_500);
}

#[test]
fn auto_premise_parses() {
    let parsed = Harness::try_parse_from([
        "clean",
        "auto",
        "premise",
        "--goal",
        "Eq Nat 0 0",
        "--limit",
        "5",
        "--json",
    ])
    .expect("clap parse");
    match parsed.command {
        Top::Auto(AutoCommands::Premise(args)) => {
            assert_eq!(args.goal, "Eq Nat 0 0");
            assert_eq!(args.limit, 5);
            assert!(args.json);
            assert!(!args.verbose);
        }
        Top::Auto(AutoCommands::Prove(_)) => panic!("expected auto premise args"),
    }
}

#[test]
fn auto_prove_list_and_demo_conflict() {
    let err = Harness::try_parse_from(["clean", "auto", "prove", "--list", "--demo", "eq_refl"])
        .expect_err("clap must reject --list with --demo");
    // clap emits a generic `ArgumentConflict` kind — the exact variant
    // tag matters less than the fact that parsing failed, so we assert
    // on the kind name being a known conflict variant.
    let kind = err.kind();
    assert!(
        matches!(
            kind,
            clap::error::ErrorKind::ArgumentConflict
                | clap::error::ErrorKind::MissingRequiredArgument
        ),
        "expected conflict error, got {kind:?}"
    );
}

#[test]
fn run_list_prints_catalog_without_error() {
    let args = AutoProveArgs {
        demo: None,
        list: true,
        budget: 5_000,
        verbose: false,
    };
    run(args).expect("--list path must succeed");
}

#[test]
fn run_without_demo_or_list_errors() {
    let args = AutoProveArgs {
        demo: None,
        list: false,
        budget: 5_000,
        verbose: false,
    };
    match run(args) {
        Err(AutoCliError::NoAction) => {}
        other => panic!("expected NoAction, got {other:?}"),
    }
}

#[test]
fn run_unknown_demo_errors() {
    let args = AutoProveArgs {
        demo: Some("no_such_demo".to_owned()),
        list: false,
        budget: 5_000,
        verbose: false,
    };
    match run(args) {
        Err(AutoCliError::UnknownDemo { name }) => assert_eq!(name, "no_such_demo"),
        other => panic!("expected UnknownDemo, got {other:?}"),
    }
}

#[test]
fn run_eq_refl_demo_verifies() {
    // End-to-end coverage: the eq_refl demo must actually verify via the
    // AutomationEngine. Mirrors `test_auto_prove_reflexivity` in
    // `crates/clean-auto/src/tests.rs` so this CLI gate catches regressions
    // in the equality lane at CLI parity.
    let args = AutoProveArgs {
        demo: Some("eq_refl".to_owned()),
        list: false,
        budget: 5_000,
        verbose: false,
    };
    run(args).expect("eq_refl demo must verify within 5 s");
}

#[test]
fn catalog_is_non_empty_and_names_unique() {
    let demos = catalog();
    assert!(!demos.is_empty(), "demo catalog must be non-empty");
    let mut names: Vec<_> = demos.iter().map(|d| d.name).collect();
    names.sort_unstable();
    let len_before = names.len();
    names.dedup();
    assert_eq!(names.len(), len_before, "demo names must be unique");
}

#[test]
fn features_descriptor_is_well_formed() {
    let descriptors: Vec<&'static FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("descriptor paths must be unique");
    for descriptor in &descriptors {
        ensure_has_example(descriptor)
            .unwrap_or_else(|e| panic!("descriptor must have ≥1 example: {e}"));
    }
    assert_eq!(FEATURES.len(), 2);
    assert_eq!(FEATURES[1].path, ["auto", "premise"]);
    assert!(FEATURES
        .iter()
        .all(|feature| feature.domain_root == Some("auto")));
}
