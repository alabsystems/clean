// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check -D <name>=<value>` (gap G50): Lean's `lean -D`, measured
//! through the real check pipeline. Every refusal below has its control: the
//! same source with no override PASSES, so the refusal is the override's.

use super::cmd_core::{collect_check_outcome, FileCheckOutcome};
use crate::cli_args::{Cli, Commands};
use clean_elab::command_line_options::{parse_command_line_options, CommandLineOption};
use clean_kernel::cli::{CheckArgs, PreludeMode, DEFAULT_AUTOMATION_BUDGET, DEFAULT_DECL_BUDGET};
use std::fs;
use std::path::Path;

/// `Foo` is undefined: only auto-binding accepts it. Pinned Lean 4.8.0:
/// accepted by `lean f.lean`, refused by `lean -DautoImplicit=false f.lean`
/// with `unknown identifier 'Foo'`.
const UNDEFINED_TYPE: &str = "theorem t (x : Foo) : x = x := rfl\n";

fn check(path: &Path, options: &[&str]) -> FileCheckOutcome {
    let options: Vec<CommandLineOption> =
        parse_command_line_options(options).expect("fixture options are valid");
    let (outcome, _elapsed) = collect_check_outcome(
        path,
        false,
        false,
        PreludeMode::Builtin,
        false,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        DEFAULT_AUTOMATION_BUDGET,
        &options,
    )
    .expect("the check pipeline itself must not error out");
    outcome
}

fn check_snippet(code: &str, options: &[&str]) -> FileCheckOutcome {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("Snippet.lean");
    fs::write(&path, code).expect("write fixture");
    check(&path, options)
}

#[test]
fn test_check_define_auto_implicit_false_refuses_undefined_type() {
    let outcome = check_snippet(UNDEFINED_TYPE, &["autoImplicit=false"]);
    assert_eq!(outcome.success_count, 0, "{outcome:?}");
    assert!(
        outcome.errors.iter().any(|e| e.contains("Foo")),
        "the refusal names the unknown identifier: {outcome:?}"
    );
    assert_eq!(outcome.command_line_options, vec!["autoImplicit=false"]);
}

#[test]
fn test_check_define_absent_accepts_undefined_type_by_auto_bind() {
    let outcome = check_snippet(UNDEFINED_TYPE, &[]);
    assert_eq!(
        outcome.success_count, 1,
        "control: Lean's default auto-binds: {outcome:?}"
    );
    assert!(outcome.errors.is_empty(), "{outcome:?}");
    assert!(outcome.command_line_options.is_empty());
}

#[test]
fn test_check_define_reaches_source_elaborated_imports() {
    // Lake builds every module of the package with its leanOptions, so the
    // override reaches an intra-project import elaborated from source, not
    // only the entry file.
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("lakefile.lean"), "package p\n").expect("write lakefile");
    fs::write(dir.path().join("Dep.lean"), UNDEFINED_TYPE).expect("write dep");
    let entry = dir.path().join("Main.lean");
    fs::write(&entry, "import Dep\ntheorem u : 1 = 1 := rfl\n").expect("write entry");

    let control = check(&entry, &[]);
    assert!(
        control.errors.is_empty() && control.success_count == 1,
        "control: without the override the import auto-binds and the entry passes: {control:?}"
    );

    let outcome = check(&entry, &["autoImplicit=false"]);
    assert!(
        outcome.errors.iter().any(|e| e.contains("Foo")),
        "the import's undefined type is refused under the override: {outcome:?}"
    );
}

#[test]
fn test_cli_parse_check_define_both_spellings_in_order() {
    use clap::Parser;
    let cli = Cli::try_parse_from([
        "clean",
        "check",
        "-DautoImplicit=false",
        "-D",
        "relaxedAutoImplicit=false",
        "f.lean",
    ])
    .expect("-D parses attached and separated");
    let Commands::Check(CheckArgs { define, .. }) = cli.command else {
        panic!("expected the check command");
    };
    assert_eq!(
        define,
        vec!["autoImplicit=false", "relaxedAutoImplicit=false"]
    );
}

#[test]
fn test_check_define_unknown_option_is_lean_error() {
    let err = parse_command_line_options(&["bogus=1"]).expect_err("unknown option refused");
    assert_eq!(
        err.to_string(),
        "invalid -D parameter, unknown configuration option 'bogus'"
    );
}
