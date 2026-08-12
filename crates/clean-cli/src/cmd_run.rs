// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean run` — the Phase 5 native build-and-run path.
//!
//! Closes the final link step of the file → emit → **link → run** pipeline
//! (Epic #3436). Where `clean compile --emit c` stops at C *source*, this
//! command takes that source the rest of the way: it synthesizes a `main()`
//! plus the small prelude extern shims the emitted closure calls, writes the
//! embedded Clean C runtime into a scratch directory, invokes the host C
//! compiler (`cc`, overridable via `$CC`/`$CLEAN_CC`) to compile and link a
//! native executable, then runs it and reports the captured stdout and exit
//! code.
//!
//! The emit + render + cc-link logic lives in [`crate::native_build`], shared
//! with `clean lake run` (which builds the same native binary to a stable
//! `build_dir/bin/<name>` path then executes it). This module is the thin
//! run-in-place wrapper: build to a scratch dir, run, capture stdout/exit.
//!
//! ## Scope (MVP)
//!
//! Two entry shapes are supported:
//!
//! 1. **Nullary `Nat`-returning** definitions, e.g.
//!    `def answer : Nat := Nat.succ (Nat.succ 0)`. The synthesized `main` calls
//!    `l_<decl>()`, unboxes the small-`Nat` tagged-pointer result, and prints it.
//!
//! 2. **`IO Unit`** programs, e.g. `def main : IO Unit := IO.println "hello"`.
//!    The synthesized `main` calls `l_<decl>()` to drive the eager IO action to
//!    completion and exits `0`. See [`crate::native_build`] for the IO lowering
//!    and shim model.

use std::path::PathBuf;
use std::process::Command;

use anyhow::{bail, Context};

use crate::cli::RunArgs;
use crate::native_build::{
    build_native_binary_in_scratch, emit_entry_c, keep_scratch, BuiltBinary,
};

pub(crate) use crate::native_build::is_primitive_denylisted;

/// Dispatch entry point for `clean run`, wired from `dispatch_sync`.
pub(crate) fn handle_run_command(args: RunArgs) -> anyhow::Result<()> {
    let emitted_c = emit_entry_c(&args.file, &args.decl, args.opt_level)?;
    let outcome = build_and_run_entry(&args.decl, &emitted_c, args.keep_temp)?;

    print!("{}", outcome.stdout);
    if !outcome.stdout.ends_with('\n') {
        println!();
    }
    if let Some(dir) = &outcome.kept_dir {
        eprintln!("clean run: kept build directory at {}", dir.display());
    }
    if outcome.exit_code != 0 {
        bail!(
            "native binary exited with status {} (stdout above)",
            outcome.exit_code
        );
    }
    Ok(())
}

/// The result of compiling, linking, and running the native entry binary.
struct RunOutcome {
    stdout: String,
    exit_code: i32,
    /// Set when `--keep-temp` is requested; the scratch dir is leaked so the
    /// caller can inspect it.
    kept_dir: Option<PathBuf>,
}

/// Build the native binary in a scratch dir (via the shared engine) and run it
/// in place, capturing stdout and the exit code. The shared engine classifies
/// the entry shape (`Nat` vs `IO Unit`), selects the needed shims, and cc-links;
/// this wrapper just executes the produced binary.
fn build_and_run_entry(decl: &str, emitted_c: &str, keep_temp: bool) -> anyhow::Result<RunOutcome> {
    let built = build_native_binary_in_scratch(decl, emitted_c, true)?;
    run_built_binary(built, keep_temp)
}

/// Execute a freshly-built scratch binary, capturing stdout and exit code.
fn run_built_binary(built: BuiltBinary, keep_temp: bool) -> anyhow::Result<RunOutcome> {
    let binary: PathBuf = built.binary.clone();
    let output = Command::new(&binary)
        .output()
        .with_context(|| format!("failed to run native binary {}", binary.display()))?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let exit_code = output.status.code().unwrap_or(-1);

    let kept_dir = if keep_temp {
        Some(keep_scratch(built))
    } else {
        None
    };
    Ok(RunOutcome {
        stdout,
        exit_code,
        kept_dir,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native_build::{classify_entry, emit_entry_c, EntryKind};

    fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("run_fixture.lean");
        std::fs::write(&file, source).expect("write fixture");
        (dir, file)
    }

    fn build_and_run_nat_entry(
        decl: &str,
        emitted_c: &str,
        keep_temp: bool,
    ) -> anyhow::Result<RunOutcome> {
        build_and_run_entry(decl, emitted_c, keep_temp)
    }

    fn build_and_run_io_entry(
        decl: &str,
        emitted_c: &str,
        keep_temp: bool,
    ) -> anyhow::Result<RunOutcome> {
        build_and_run_entry(decl, emitted_c, keep_temp)
    }

    fn cc_available() -> bool {
        let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
        Command::new(cc)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Full end-to-end: emit C for a nullary Nat decl, build, link, run, assert.
    #[test]
    fn test_run_nat_entry_builds_links_and_prints_result() {
        if !cc_available() {
            eprintln!("skipping test_run_nat_entry_builds_links_and_prints_result: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def answer : Nat := Nat.succ (Nat.succ 0)\n");
        let emitted = emit_entry_c(&file, "answer", 0).expect("emit C for answer");
        let outcome =
            build_and_run_nat_entry("answer", &emitted, false).expect("build+link+run answer");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout.trim(), "2", "answer should print 2");
    }

    /// Typeclass arithmetic: `def r : Nat := 40 + 2` must compute the true sum.
    #[test]
    fn test_run_nat_typeclass_add_prints_42() {
        if !cc_available() {
            eprintln!("skipping test_run_nat_typeclass_add_prints_42: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def r : Nat := 40 + 2\n");
        let emitted = emit_entry_c(&file, "r", 0).expect("emit C for r");
        assert!(
            emitted.contains("l_HAdd_hAdd("),
            "40 + 2 should lower through HAdd.hAdd: {emitted}"
        );
        assert_eq!(classify_entry(&emitted), EntryKind::Nat);
        let outcome = build_and_run_nat_entry("r", &emitted, false).expect("build+link+run r");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout.trim(), "42", "40 + 2 should print 42");
    }

    #[test]
    fn test_run_nat_typeclass_chained_add_prints_42() {
        if !cc_available() {
            eprintln!("skipping test_run_nat_typeclass_chained_add_prints_42: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def s : Nat := 10 + 30 + 2\n");
        let emitted = emit_entry_c(&file, "s", 0).expect("emit C for s");
        let outcome = build_and_run_nat_entry("s", &emitted, false).expect("build+link+run s");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout.trim(), "42", "10 + 30 + 2 should print 42");
    }

    #[test]
    fn test_run_nat_typeclass_mul_prints_42() {
        if !cc_available() {
            eprintln!("skipping test_run_nat_typeclass_mul_prints_42: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def m : Nat := 6 * 7\n");
        let emitted = emit_entry_c(&file, "m", 0).expect("emit C for m");
        let outcome = build_and_run_nat_entry("m", &emitted, false).expect("build+link+run m");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout.trim(), "42", "6 * 7 should print 42");
    }

    /// Full end-to-end `if`: branch actually taken drives the result (1 vs 0).
    #[test]
    fn test_run_if_bool_selects_branch() {
        if !cc_available() {
            eprintln!("skipping test_run_if_bool_selects_branch: no cc");
            return;
        }
        let src = "def g (b : Bool) : Nat := if b then 1 else 0\n\
                   def rTrue : Nat := g true\n\
                   def rFalse : Nat := g false\n";
        let (_dir, file) = write_temp_lean(src);

        let emitted_true = emit_entry_c(&file, "rTrue", 0).expect("emit C for rTrue");
        let outcome_true =
            build_and_run_nat_entry("rTrue", &emitted_true, false).expect("build+run rTrue");
        assert_eq!(outcome_true.exit_code, 0);
        assert_eq!(
            outcome_true.stdout.trim(),
            "1",
            "g true takes the then-branch"
        );

        let emitted_false = emit_entry_c(&file, "rFalse", 0).expect("emit C for rFalse");
        let outcome_false =
            build_and_run_nat_entry("rFalse", &emitted_false, false).expect("build+run rFalse");
        assert_eq!(outcome_false.exit_code, 0);
        assert_eq!(
            outcome_false.stdout.trim(),
            "0",
            "g false takes the else-branch"
        );
    }

    /// Full end-to-end `match` over `Nat`: zero vs successor arm by scrutinee.
    #[test]
    fn test_run_match_nat_selects_branch() {
        if !cc_available() {
            eprintln!("skipping test_run_match_nat_selects_branch: no cc");
            return;
        }
        let src = "def f (n : Nat) : Nat := match n with | 0 => 1 | _ => 2\n\
                   def f0 : Nat := f 0\n\
                   def f5 : Nat := f 5\n";
        let (_dir, file) = write_temp_lean(src);

        let emitted0 = emit_entry_c(&file, "f0", 0).expect("emit C for f0");
        let outcome0 = build_and_run_nat_entry("f0", &emitted0, false).expect("build+run f0");
        assert_eq!(outcome0.exit_code, 0);
        assert_eq!(outcome0.stdout.trim(), "1", "f 0 takes the zero arm");

        let emitted5 = emit_entry_c(&file, "f5", 0).expect("emit C for f5");
        let outcome5 = build_and_run_nat_entry("f5", &emitted5, false).expect("build+run f5");
        assert_eq!(outcome5.exit_code, 0);
        assert_eq!(outcome5.stdout.trim(), "2", "f 5 takes the successor arm");
    }

    /// Full end-to-end structural recursion: fact 0 = 1, fact 5 = 120, fact 6 = 720.
    #[test]
    fn test_run_recursive_factorial_distinct_values() {
        if !cc_available() {
            eprintln!("skipping test_run_recursive_factorial_distinct_values: no cc");
            return;
        }
        let src = "def fact : Nat -> Nat\n\
                   | 0 => 1\n\
                   | n+1 => (n+1) * fact n\n\
                   def f0 : Nat := fact 0\n\
                   def f5 : Nat := fact 5\n\
                   def f6 : Nat := fact 6\n";
        let (_dir, file) = write_temp_lean(src);

        for (decl, expected) in [("f0", "1"), ("f5", "120"), ("f6", "720")] {
            let emitted =
                emit_entry_c(&file, decl, 0).unwrap_or_else(|e| panic!("emit C for {decl}: {e:?}"));
            let outcome = build_and_run_nat_entry(decl, &emitted, false)
                .unwrap_or_else(|e| panic!("build+run {decl}: {e:?}"));
            assert_eq!(outcome.exit_code, 0, "{decl} exit code");
            assert_eq!(
                outcome.stdout.trim(),
                expected,
                "fact via {decl} must compute {expected} by real recursion"
            );
        }
    }

    /// #14 closure-boundary relaxation: `Nat.pred 5` compiled from source -> 4.
    #[test]
    fn test_run_compiles_nat_pred_from_source() {
        if !cc_available() {
            eprintln!("skipping test_run_compiles_nat_pred_from_source: no cc");
            return;
        }
        let src = "def r : Nat := Nat.pred 5\n";
        let (_dir, file) = write_temp_lean(src);
        let emitted = emit_entry_c(&file, "r", 0).expect("emit C for r");
        let outcome = build_and_run_nat_entry("r", &emitted, false).expect("build+run r");
        assert_eq!(outcome.exit_code, 0);
        assert_eq!(outcome.stdout.trim(), "4", "Nat.pred 5 must evaluate to 4");
    }

    /// PRIMITIVE_DENYLIST holds: `Nat.add` stays a shim, still computes 42.
    #[test]
    fn test_run_nat_add_stays_shim_not_compiled() {
        if !cc_available() {
            eprintln!("skipping test_run_nat_add_stays_shim_not_compiled: no cc");
            return;
        }
        let src = "def r : Nat := 40 + 2\n";
        let (_dir, file) = write_temp_lean(src);
        let emitted = emit_entry_c(&file, "r", 0).expect("emit C for r");
        let outcome = build_and_run_nat_entry("r", &emitted, false).expect("build+run r");
        assert_eq!(outcome.exit_code, 0);
        assert_eq!(
            outcome.stdout.trim(),
            "42",
            "40 + 2 via the O(1) Nat.add shim"
        );
    }

    /// Full end-to-end: `def main : IO Unit := IO.println "hello"` -> hello, exit 0.
    #[test]
    fn test_run_io_println_prints_hello_and_exits_zero() {
        if !cc_available() {
            eprintln!("skipping test_run_io_println_prints_hello_and_exits_zero: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def main : IO Unit := IO.println \"hello\"\n");
        let emitted = emit_entry_c(&file, "main", 0).expect("emit C for main");
        assert_eq!(
            classify_entry(&emitted),
            EntryKind::Io,
            "println main should classify as IO"
        );
        let outcome = build_and_run_io_entry("main", &emitted, false).expect("build+link+run main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout, "hello\n", "main should print hello");
    }

    /// Compute-and-print: recursive computation rendered via toString, printed.
    #[test]
    fn test_run_io_prints_computed_nat_via_tostring() {
        if !cc_available() {
            eprintln!("skipping test_run_io_prints_computed_nat_via_tostring: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def fact : Nat -> Nat | 0 => 1 | n+1 => (n+1) * fact n\n\
             def main : IO Unit := IO.println (toString (fact 5))\n",
        );
        let emitted = emit_entry_c(&file, "main", 0).expect("emit C for main");
        let outcome = build_and_run_io_entry("main", &emitted, false).expect("build+link+run main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "120\n",
            "should compute fact 5 and print 120"
        );
    }

    /// `do`-block sequencing: two prints in source order.
    #[test]
    fn test_run_io_do_block_prints_in_order() {
        if !cc_available() {
            eprintln!("skipping test_run_io_do_block_prints_in_order: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def main : IO Unit := do\n  IO.println \"hello\"\n  IO.println \"world\"\n",
        );
        let emitted = emit_entry_c(&file, "main", 0).expect("emit C for do main");
        assert_eq!(classify_entry(&emitted), EntryKind::Io);
        let outcome =
            build_and_run_io_entry("main", &emitted, false).expect("build+link+run do main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "hello\nworld\n",
            "do-block must print in source order"
        );
    }

    /// `pure ()` is a no-op IO action: nothing printed, exit 0.
    #[test]
    fn test_run_io_pure_unit_exits_zero_no_output() {
        if !cc_available() {
            eprintln!("skipping test_run_io_pure_unit_exits_zero_no_output: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean("def main : IO Unit := pure ()\n");
        let emitted = emit_entry_c(&file, "main", 0).expect("emit C for pure main");
        assert_eq!(classify_entry(&emitted), EntryKind::Io);
        let outcome =
            build_and_run_io_entry("main", &emitted, false).expect("build+link+run pure main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout, "", "pure () should print nothing");
    }
}
