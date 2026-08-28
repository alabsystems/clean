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
//! 2. **`IO` programs**, e.g. `def main : IO Unit := IO.println "hello"` or the
//!    real Lean entry contract `def main (args : List String) : IO UInt32`. The
//!    synthesized `main` marshals `argv[1..]` into a `List String` when the
//!    entry takes one, calls `l_<decl>(…)` to drive the eager IO action to
//!    completion, and returns the entry's `UInt32` as the process exit status
//!    (`0` for an `IO Unit` entry). See [`crate::native_build`] for the IO
//!    lowering, the entry contract, and the shim model.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

use anyhow::Context;
use clean_kernel::Expr;

use crate::cli::RunArgs;
use crate::native_build::{
    build_native_binary_in_scratch, emit_entry_c_with_type, keep_scratch, BuiltBinary,
};

pub(crate) use crate::native_build::is_primitive_denylisted;

/// Dispatch entry point for `clean run`, wired from `dispatch_sync`.
///
/// A nonzero status is PROPAGATED, not reported: `def main : IO UInt32 := …
/// pure 3` must make `clean run` itself exit 3, the same way `lake exe` does.
/// Reporting it as an error would collapse every status onto the CLI's own
/// exit 1 and lose the value the program returned.
pub(crate) fn handle_run_command(args: RunArgs) -> anyhow::Result<()> {
    let (emitted_c, decl_type) = emit_entry_c_with_type(&args.file, &args.decl, args.opt_level)?;
    let outcome = build_and_run_entry(
        &args.decl,
        &emitted_c,
        decl_type.as_ref(),
        &[],
        args.keep_temp,
    )?;

    print!("{}", outcome.stdout);
    if !outcome.stdout.ends_with('\n') {
        println!();
    }
    if let Some(dir) = &outcome.kept_dir {
        eprintln!("clean run: kept build directory at {}", dir.display());
    }
    if outcome.exit_code != 0 {
        // `std::process::exit` skips destructors, so flush what we just wrote.
        // The scratch dir is already released: `run_built_binary` drops the
        // `BuiltBinary` (or leaks it deliberately under `--keep-temp`) before
        // returning.
        let _ = std::io::stdout().flush();
        let _ = std::io::stderr().flush();
        std::process::exit(outcome.exit_code);
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
/// in place, capturing stdout and the exit code. The shared engine derives the
/// entry contract (`Nat` vs `IO`, argv shape, exit shape), selects the needed
/// shims, and cc-links; this wrapper just executes the produced binary.
fn build_and_run_entry(
    decl: &str,
    emitted_c: &str,
    decl_type: Option<&Expr>,
    run_args: &[&str],
    keep_temp: bool,
) -> anyhow::Result<RunOutcome> {
    let built = build_native_binary_in_scratch(decl, emitted_c, decl_type, true)?;
    run_built_binary(built, run_args, keep_temp)
}

/// Execute a freshly-built scratch binary, capturing stdout and exit code.
fn run_built_binary(
    built: BuiltBinary,
    run_args: &[&str],
    keep_temp: bool,
) -> anyhow::Result<RunOutcome> {
    let binary: PathBuf = built.binary.clone();
    let output = Command::new(&binary)
        .args(run_args)
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
    use crate::native_build::{classify_entry, entry_arity_in_c, EntryKind};
    use std::path::Path;

    fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
        let dir = tempfile::tempdir().expect("tempdir");
        let file = dir.path().join("run_fixture.lean");
        std::fs::write(&file, source).expect("write fixture");
        (dir, file)
    }

    /// Build and run a decl the way `clean run` does — emit + elaborated type in
    /// one pass, then drive the synthesized entry.
    ///
    /// The helpers take the FILE, not a pre-emitted C string, on purpose: the
    /// exit shape (`IO Unit` vs `IO UInt32`) lives only in the Lean type, so a
    /// helper that accepted just the C could not tell them apart and would
    /// silently exit `0` for every `IO UInt32` fixture written through it.
    fn build_and_run_decl(
        file: &Path,
        decl: &str,
        run_args: &[&str],
    ) -> anyhow::Result<RunOutcome> {
        let (emitted_c, decl_type) = emit_entry_c_with_type(file, decl, 0)?;
        build_and_run_entry(decl, &emitted_c, decl_type.as_ref(), run_args, false)
    }

    fn build_and_run_nat_entry(file: &Path, decl: &str) -> anyhow::Result<RunOutcome> {
        build_and_run_decl(file, decl, &[])
    }

    fn build_and_run_io_entry(file: &Path, decl: &str) -> anyhow::Result<RunOutcome> {
        build_and_run_decl(file, decl, &[])
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
        let outcome = build_and_run_nat_entry(&file, "answer").expect("build+link+run answer");
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
        let (emitted, _) = emit_entry_c_with_type(&file, "r", 0).expect("emit C for r");
        assert!(
            emitted.contains("l_HAdd_hAdd("),
            "40 + 2 should lower through HAdd.hAdd: {emitted}"
        );
        assert_eq!(classify_entry(&emitted), EntryKind::Nat);
        let outcome = build_and_run_nat_entry(&file, "r").expect("build+link+run r");
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
        let outcome = build_and_run_nat_entry(&file, "s").expect("build+link+run s");
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
        let outcome = build_and_run_nat_entry(&file, "m").expect("build+link+run m");
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

        let outcome_true = build_and_run_nat_entry(&file, "rTrue").expect("build+run rTrue");
        assert_eq!(outcome_true.exit_code, 0);
        assert_eq!(
            outcome_true.stdout.trim(),
            "1",
            "g true takes the then-branch"
        );

        let outcome_false = build_and_run_nat_entry(&file, "rFalse").expect("build+run rFalse");
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

        let outcome0 = build_and_run_nat_entry(&file, "f0").expect("build+run f0");
        assert_eq!(outcome0.exit_code, 0);
        assert_eq!(outcome0.stdout.trim(), "1", "f 0 takes the zero arm");

        let outcome5 = build_and_run_nat_entry(&file, "f5").expect("build+run f5");
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
            let outcome = build_and_run_nat_entry(&file, decl)
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
        let outcome = build_and_run_nat_entry(&file, "r").expect("build+run r");
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
        let outcome = build_and_run_nat_entry(&file, "r").expect("build+run r");
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
        let (emitted, _) = emit_entry_c_with_type(&file, "main", 0).expect("emit C for main");
        assert_eq!(
            classify_entry(&emitted),
            EntryKind::Io,
            "println main should classify as IO"
        );
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout, "hello\n", "main should print hello");
    }

    /// The canonical Lean entry point `def main : IO UInt32` — an exit code, not
    /// just `IO Unit`.
    ///
    /// Two bricks meet here. The shim brick made the entry BUILD at all:
    /// `UINT32_PRELUDE_SHIMS` is a member of `ALL_PRELUDE_SHIM_TABLES`, which
    /// feeds `is_primitive_denylisted`, so the emitter is FORCED to leave
    /// `UInt32.ofNat` extern and always writes `l_UInt32_ofNat(...)`, while
    /// `render_native_translation_unit` hand-listed its tables and omitted
    /// UINT32 from both entry arms — every UInt32-touching entry was refused
    /// 100% of the time with "native build cannot satisfy prelude extern
    /// `l_UInt32_ofNat`".
    ///
    /// The entry-contract brick made it EXIT correctly. Measured before it:
    /// this program printed `bye` and exited **0**, where Lean exits 3 — the
    /// synthesized driver hardcoded `return 0` and threw the entry's result
    /// away with `(void)_r`. The exit shape cannot be recovered from the
    /// emitted C (`IO Unit` and `IO UInt32` both lower to
    /// `clean_obj* l_main(void)`), so the driver reads it from the entry's
    /// elaborated Lean type.
    #[test]
    fn test_run_io_uint32_entry_propagates_exit_code() {
        if !cc_available() {
            eprintln!("skipping test_run_io_uint32_entry_propagates_exit_code: no cc");
            return;
        }
        let (_dir, file) =
            write_temp_lean("def main : IO UInt32 := do\n  IO.println \"bye\"\n  pure 3\n");
        let (emitted, _) =
            emit_entry_c_with_type(&file, "main", 0).expect("emit C for UInt32 main");
        assert_eq!(
            classify_entry(&emitted),
            EntryKind::Io,
            "an IO UInt32 main should classify as IO"
        );
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run UInt32 main");
        assert_eq!(outcome.stdout, "bye\n", "should print bye");
        assert_eq!(
            outcome.exit_code, 3,
            "`pure 3` in an `IO UInt32` main IS the process exit status (Lean exits 3)"
        );
    }

    /// NEGATIVE CONTROL for the exit-code assertion above: the same driver, the
    /// same `pure`, but at `IO Unit` — which must still exit 0. Without this a
    /// driver that blindly returned the last scalar would look correct on the
    /// UInt32 fixture alone.
    #[test]
    fn test_run_io_unit_entry_still_exits_zero() {
        if !cc_available() {
            eprintln!("skipping test_run_io_unit_entry_still_exits_zero: no cc");
            return;
        }
        let (_dir, file) =
            write_temp_lean("def main : IO Unit := do\n  IO.println \"bye\"\n  pure ()\n");
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run Unit main");
        assert_eq!(outcome.stdout, "bye\n", "should print bye");
        assert_eq!(outcome.exit_code, 0, "an `IO Unit` main always exits 0");
    }

    /// Lean's real entry point takes `argv`: `def main (args : List String)`.
    ///
    /// Measured before this brick: the emitted C is
    /// `clean_obj* l_main(clean_obj* _x0)` while the synthesized driver called
    /// `l_main()`, so the build died at cc with "too few arguments to function
    /// call, single argument '_x0' was not specified" — every argv-taking Lean
    /// program was outside the pillar, not merely mis-run.
    ///
    /// The counts are DISCRIMINATING: 3 args and 0 args through the same
    /// binary. A driver that passed nil unconditionally would pass the 0-arg
    /// leg and fail the 3-arg one; a driver that included `argv[0]` would print
    /// 4 and 1.
    #[test]
    fn test_run_io_argv_entry_marshals_argument_list() {
        if !cc_available() {
            eprintln!("skipping test_run_io_argv_entry_marshals_argument_list: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def main (args : List String) : IO Unit := IO.println (toString args.length)\n",
        );
        let (emitted, _) = emit_entry_c_with_type(&file, "main", 0).expect("emit C for argv main");
        assert_eq!(
            entry_arity_in_c(&emitted, "l_main"),
            Some(1),
            "the emitter declares the argv entry unary: {emitted}"
        );

        let three = build_and_run_decl(&file, "main", &["a", "b", "c"]).expect("run with 3 args");
        assert_eq!(three.exit_code, 0, "exit code");
        assert_eq!(
            three.stdout, "3\n",
            "three arguments must marshal to a 3-element List String \
             (argv[0], the program path, is NOT one of Lean's args)"
        );

        let none = build_and_run_decl(&file, "main", &[]).expect("run with no args");
        assert_eq!(none.exit_code, 0, "exit code");
        assert_eq!(none.stdout, "0\n", "no arguments must marshal to List.nil");
    }

    /// The full Lean entry contract in one program: argv in, status out.
    #[test]
    fn test_run_io_argv_uint32_entry_returns_argument_count() {
        if !cc_available() {
            eprintln!("skipping test_run_io_argv_uint32_entry_returns_argument_count: no cc");
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def main (args : List String) : IO UInt32 := do\n  \
             IO.println \"counting\"\n  \
             pure (UInt32.ofNat args.length)\n",
        );
        let outcome =
            build_and_run_decl(&file, "main", &["x", "y"]).expect("build+link+run argv UInt32");
        assert_eq!(outcome.stdout, "counting\n", "should print");
        assert_eq!(
            outcome.exit_code, 2,
            "the entry returns its argument count as the process status"
        );
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
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run main");
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
        let (emitted, _) = emit_entry_c_with_type(&file, "main", 0).expect("emit C for do main");
        assert_eq!(classify_entry(&emitted), EntryKind::Io);
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run do main");
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
        let (emitted, _) = emit_entry_c_with_type(&file, "main", 0).expect("emit C for pure main");
        assert_eq!(classify_entry(&emitted), EntryKind::Io);
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run pure main");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(outcome.stdout, "", "pure () should print nothing");
    }
}
