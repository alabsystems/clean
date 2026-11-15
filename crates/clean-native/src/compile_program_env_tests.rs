// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Clean's program environment ([`lean_program_environment`]) against pinned
//! Lean v4.30.0-rc2, through the production entry `clean compile`/`run` and
//! `lake build`'s executable step share ([`elaborate_file_to_env`]). Every
//! verdict was measured on both tools on 2026-10-08 (decision R15).
//!
//! Three rows agree with Lean. The rest pin known gaps, recorded in
//! `docs/issues/2026-10-08-program-environment-lean-parity.md`, so each test
//! fails the day its gap closes: two refusals of programs Lean accepts, and
//! five acceptances of programs Lean rejects (four IO operations registered
//! at non-Lean names or types, and core-only `Type*`).

use super::*;

fn elaborate(source: &str) -> anyhow::Result<Environment> {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("Program.lean");
    std::fs::write(&file, source).expect("write fixture");
    elaborate_file_to_env(&file)
}

/// The refusal, rendered with its whole context chain.
fn refusal(source: &str) -> String {
    match elaborate(source) {
        Ok(_) => panic!("the program environment accepted:\n{source}"),
        Err(error) => format!("{error:#}"),
    }
}

/// Asserts the compile path refused a top-level declaration with `detail`.
fn assert_refused(source: &str, detail: &str) {
    let error = refusal(source);
    assert!(
        error.contains("failed to elaborate declaration in"),
        "{error}"
    );
    assert!(error.contains(detail), "expected `{detail}` in: {error}");
}

/// Asserts the compile path accepted `source` and registered `name`.
fn assert_accepted(source: &str, name: &str) {
    let env = elaborate(source).unwrap_or_else(|error| panic!("refused: {error:#}\n{source}"));
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "{name} is not registered"
    );
}

#[test]
fn test_program_env_io_main_accepted_as_lean_does() {
    assert_accepted(
        "def main : IO Unit := do\n  IO.println \"hi\"\n  IO.println (toString (2 + 3))\n",
        "main",
    );
}

#[test]
fn test_program_env_ill_typed_io_main_refused_as_lean_does() {
    assert_refused(
        "def main : IO Nat := IO.println \"x\"\n",
        "expected IO Nat, got IO Unit",
    );
}

#[test]
fn test_program_env_list_do_block_refused_as_lean_does() {
    // Lean core has no `List` monad. Clean's builtin `clean check` flavour
    // registers one (`instPureList`); the program environment does not.
    assert_refused(
        "def xs : List Nat := do\n  let x <- [1, 2]\n  pure (x + 1)\n",
        "failed to synthesize instance `Pure List`",
    );
}

#[test]
fn test_program_env_ulift_refused_known_gap_lean_accepts() {
    // KNOWN GAP: the program environment registers no `ULift`.
    assert_refused(
        "def u : ULift.{1} Nat := ULift.up 3\n",
        "Universe instance applied to non-constant expression",
    );
}

#[test]
fn test_program_env_println_of_nat_refused_known_gap_lean_accepts() {
    // KNOWN GAP: Lean's `IO.println` takes any `[ToString α]`; Clean's takes a
    // `String`.
    assert_refused("def main : IO Unit := IO.println 5\n", "expected String");
}

#[test]
fn test_program_env_non_lean_io_operations_accepted_known_false_acceptance() {
    // KNOWN FALSE ACCEPTANCES: Lean v4.30.0-rc2 rejects every row. Lean has no
    // `IO.getLine` or `IO.panic`; its `IO.getEnv` returns `IO (Option String)`
    // and its `IO.currentDir` returns `IO System.FilePath`.
    for (source, name) in [
        ("def f : IO String := IO.getEnv \"HOME\"\n", "f"),
        ("def g : IO String := IO.getLine\n", "g"),
        ("def h : IO Nat := IO.panic \"boom\"\n", "h"),
        ("def k : IO String := IO.currentDir\n", "k"),
    ] {
        assert_accepted(source, name);
    }
}

#[test]
fn test_program_env_core_type_star_accepted_known_false_acceptance() {
    // KNOWN FALSE ACCEPTANCE without a Mathlib import: Lean core rejects
    // `Type*` at parse time. With `import Mathlib.Tactic.TypeStar` Lean
    // accepts it, so a fix must stay import-aware.
    assert_accepted("def idT (a : Type*) (x : a) : a := x\n", "idT");
}
