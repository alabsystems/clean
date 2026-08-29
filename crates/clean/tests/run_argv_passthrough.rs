// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean run` hands its trailing arguments to the program it builds.
//!
//! This drives the REAL CLI binary, because the gap this pins was never in the
//! engine. `native_build`'s driver has marshalled `argv[1..]` into the entry's
//! `List String` since the entry contract landed (f514848a8), and
//! `cmd_run::build_and_run_entry` has always taken a `run_args` slice — but
//! `RunArgs` had no field for program arguments and `handle_run_command`
//! passed `&[]`. Every in-crate test drove argv by calling the helper
//! directly, so all of them were green while no `clean run` user could supply
//! a single argument. Only a test that goes through argument PARSING and
//! dispatch can see that, which is what this file does.
//!
//! The fixture reports the arguments themselves, not just how many there were:
//! a driver that fabricated a list of the right length, or reversed it, or
//! included `argv[0]`, would pass a count assertion.

#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `def main (args : List String) : IO UInt32` — the full Lean entry contract.
///
/// `render` is a non-recursive `match`: it prints the arguments joined by `|`,
/// so the assertion pins content AND order, and returns the count as the
/// process status, so the same run pins the exit shape too.
const ARGV_FIXTURE: &str = "\
def render : List String -> String
  | [] => \"none\"
  | [a] => a
  | [a, b] => a ++ \"|\" ++ b
  | [a, b, c] => a ++ \"|\" ++ b ++ \"|\" ++ c
  | _ => \"more\"

def main (args : List String) : IO UInt32 := do
  IO.println (render args)
  pure (UInt32.ofNat args.length)
";

fn cc_available() -> bool {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    Command::new(cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn write_fixture(dir: &Path) -> PathBuf {
    let file = dir.join("argv_main.lean");
    std::fs::write(&file, ARGV_FIXTURE).expect("write argv fixture");
    file
}

fn run_clean(extra: &[&str], file: &Path) -> Output {
    let mut cmd = Command::new(clean_path());
    cmd.arg("run")
        .arg(file)
        .args(["--decl", "main"])
        .args(extra);
    cmd.output()
        .unwrap_or_else(|err| panic!("failed to spawn clean run {extra:?}: {err}"))
}

fn stdout_of(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// Three arguments after `--` reach the program, in order, with no `argv[0]`.
#[test]
fn clean_run_forwards_trailing_arguments_to_the_program() {
    if !cc_available() {
        eprintln!("skipping clean_run_forwards_trailing_arguments_to_the_program: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());

    let output = run_clean(&["--", "alpha", "beta", "gamma"], &file);
    assert_eq!(
        stdout_of(&output),
        "alpha|beta|gamma\n",
        "`clean run <file> --decl main -- alpha beta gamma` must hand the entry \
         exactly those three strings in that order; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.status.code(),
        Some(3),
        "the entry returns its argument count as the process status, and \
         `clean run` propagates it"
    );
}

/// NEGATIVE CONTROL. The same binary, no trailing arguments: `List.nil`, not a
/// one-element list holding the program path. Without this leg a driver that
/// always passed `argv[0]` would look correct above (it would print four
/// segments, but a laxer assertion would not notice).
#[test]
fn clean_run_without_trailing_arguments_passes_the_empty_list() {
    if !cc_available() {
        eprintln!("skipping clean_run_without_trailing_arguments_passes_the_empty_list: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());

    let output = run_clean(&[], &file);
    assert_eq!(
        stdout_of(&output),
        "none\n",
        "no trailing arguments must reach the entry as `[]` — the program path \
         is not one of Lean's args; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "an empty argument list is a zero count, hence exit 0"
    );
}

/// A flag-like argument belongs to the PROGRAM, not to `clean run`.
///
/// Without `allow_hyphen_values` clap would reject `--literal-flag` as an
/// unknown option of `clean run` itself and the program would never start;
/// this is the leg that pins the pass-through as literal.
#[test]
fn clean_run_forwards_flag_like_arguments_verbatim() {
    if !cc_available() {
        eprintln!("skipping clean_run_forwards_flag_like_arguments_verbatim: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());

    let output = run_clean(&["--", "--literal-flag", "two words"], &file);
    assert_eq!(
        stdout_of(&output),
        "--literal-flag|two words\n",
        "flag-like and whitespace-bearing arguments must survive verbatim; \
         stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(2), "two arguments");
}

/// `clean run`'s OWN flags still bind to `clean run` when they precede the
/// program arguments — `--keep-temp` here keeps a scratch directory rather
/// than becoming the program's first argument.
#[test]
fn clean_run_own_flags_before_the_arguments_still_bind_to_the_cli() {
    if !cc_available() {
        eprintln!("skipping clean_run_own_flags_before_the_arguments_still_bind_to_the_cli: no cc");
        return;
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let file = write_fixture(dir.path());

    let output = run_clean(&["--keep-temp", "--", "solo"], &file);
    assert_eq!(
        stdout_of(&output),
        "solo\n",
        "`--keep-temp` is `clean run`'s flag; only `solo` is the program's argv; \
         stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(1), "one argument");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("kept build directory at"),
        "`--keep-temp` must have been consumed by the CLI, not forwarded: {stderr}"
    );

    // The kept scratch directory is this test's litter; remove it.
    if let Some(rest) = stderr.split("kept build directory at ").nth(1) {
        let kept = rest.lines().next().unwrap_or("").trim();
        if !kept.is_empty() {
            let _ = std::fs::remove_dir_all(kept);
        }
    }
}
