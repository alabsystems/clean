// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `clean verify rust` clap parsing, pipeline execution, and
//! [`FEATURES`] descriptor shape.

use clap::Parser;
use clean_features::{ensure_has_example, ensure_unique_paths, FeatureDescriptor};

use super::{
    run, run_example, AliasingOutcome, BorrowOutcome, ProofBundleOutcome, RustSemCliError,
    RustVerifyArgs, FEATURES,
};

/// Tiny parser embedding [`RustVerifyArgs`] so we can exercise clap
/// integration in isolation from the top-level `clean-cli` tree.
#[derive(Debug, Parser)]
struct Harness {
    #[command(subcommand)]
    command: Top,
}

#[derive(Debug, clap::Subcommand)]
enum Top {
    #[command(subcommand)]
    Verify(Verify),
}

#[derive(Debug, clap::Subcommand)]
enum Verify {
    Rust(RustVerifyArgs),
}

fn parse_args(argv: &[&str]) -> RustVerifyArgs {
    let parsed = Harness::try_parse_from(argv).expect("clap parse");
    match parsed.command {
        Top::Verify(Verify::Rust(args)) => args,
    }
}

#[test]
fn rust_verify_list_parses() {
    let args = parse_args(&["clean", "verify", "rust", "--list"]);
    assert!(args.list);
    assert!(args.example.is_none());
    assert!(!args.verbose);
}

#[test]
fn rust_verify_example_parses() {
    let args = parse_args(&["clean", "verify", "rust", "--example", "inventory_restock"]);
    assert_eq!(args.example.as_deref(), Some("inventory_restock"));
    assert!(!args.list);
}

#[test]
fn rust_verify_verbose_parses() {
    let args = parse_args(&[
        "clean",
        "verify",
        "rust",
        "--example",
        "inventory_restock",
        "--verbose",
    ]);
    assert!(args.verbose);
}

#[test]
fn rust_verify_list_and_example_conflict() {
    let err = Harness::try_parse_from([
        "clean",
        "verify",
        "rust",
        "--list",
        "--example",
        "inventory_restock",
    ])
    .expect_err("--list and --example must conflict");
    let _ = err.to_string(); // force materialization
}

#[test]
fn run_without_action_errors() {
    let args = RustVerifyArgs {
        example: None,
        list: false,
        verbose: false,
    };
    let err = run(args).expect_err("no action must error");
    assert!(matches!(err, RustSemCliError::NoAction));
}

#[test]
fn run_unknown_example_errors() {
    let err = run_example("this-does-not-exist").expect_err("unknown example must error");
    match err {
        RustSemCliError::UnknownExample { name } => {
            assert_eq!(name, "this-does-not-exist");
        }
        other => panic!("expected UnknownExample, got {other:?}"),
    }
}

#[test]
fn run_list_succeeds() {
    let args = RustVerifyArgs {
        example: None,
        list: true,
        verbose: false,
    };
    run(args).expect("--list must succeed");
}

#[test]
fn run_positive_example_succeeds() {
    let report = run_example("inventory_restock").expect("positive example must verify");
    assert_eq!(report.name, "inventory_restock");
    assert!(matches!(report.borrow_outcome, BorrowOutcome::Clean));
    assert!(matches!(
        report.aliasing_outcome,
        AliasingOutcome::ReturnedU32(9)
    ));
    assert!(matches!(
        report.proof_bundle_outcome,
        ProofBundleOutcome::Built { .. }
    ));
}

#[test]
fn run_negative_example_reports_expected_error() {
    let report = run_example("overlapping_mut_borrows")
        .expect("negative example with clean aliasing must verify");
    match &report.borrow_outcome {
        BorrowOutcome::ExpectedError {
            function,
            error_count,
        } => {
            assert_eq!(function, "main");
            assert!(*error_count >= 1);
        }
        other => panic!("expected ExpectedError, got {other:?}"),
    }
    assert!(matches!(
        report.proof_bundle_outcome,
        ProofBundleOutcome::SkippedDueToExpectedError
    ));
}

#[test]
fn features_are_lint_clean() {
    let descriptors: Vec<&FeatureDescriptor> = FEATURES.iter().collect();
    ensure_unique_paths(&descriptors).expect("rust-sem descriptor paths are unique");
    for descriptor in FEATURES {
        ensure_has_example(descriptor).expect("every rust-sem descriptor has ≥1 example");
    }
}

#[test]
fn features_has_expected_path() {
    assert_eq!(FEATURES.len(), 1);
    assert_eq!(FEATURES[0].path, &["verify", "rust"]);
    assert_eq!(
        FEATURES[0].stability,
        clean_features::Stability::Experimental
    );
}
