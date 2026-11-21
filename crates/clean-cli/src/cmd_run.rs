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
//! The emit + render + cc-link logic lives in [`clean_native::native_build`], shared
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
//!    (`0` for an `IO Unit` entry). See [`clean_native::native_build`] for the IO
//!    lowering, the entry contract, and the shim model.
//!
//! ## argv
//!
//! Trailing arguments — `clean run f.lean --decl main -- a b c` — are the
//! program's `argv`. They are handed to the scratch binary verbatim, which is
//! what `argv[1..]` the synthesized driver marshals into the entry's
//! `List String`. This wrapper is where they enter: the marshalling half has
//! worked since the entry contract landed, but `RunArgs` had no field for
//! program arguments, so `clean run` could BUILD an argv-taking Lean entry and
//! never hand it a non-empty argv — `args.length` printed `0` with no flag
//! able to change it.

use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};

use anyhow::Context;

use crate::cli::RunArgs;
use clean_native::native_build::{emit_native_c_artifact, keep_scratch};

/// Dispatch entry point for `clean run`, wired from `dispatch_sync`.
///
/// The program runs as Lean's `lean --run` runs it: it INHERITS this
/// process's stdin, stdout and stderr, so its bytes reach the caller exactly
/// as it wrote them, when it wrote them, and its diagnostics are never hidden.
/// Measured 2026-09-24 before this change, against pinned Lean v4.30.0-rc2:
/// the child ran under `Command::output()`, so `IO.print "abc"` came out as
/// the four bytes `abc\n` (this wrapper appended a newline to any output not
/// ending in one), `IO.eprintln` output and the runtime's own
/// `clean panic: …` diagnostics were discarded, stdin was `/dev/null`, stdout
/// arrived only after the program exited, and a program killed by a signal
/// was reported as status 255 with no message.
///
/// A nonzero status is PROPAGATED, not reported: `def main : IO UInt32 := …
/// pure 3` makes `clean run` itself exit 3, the same way `lake exe` does. A
/// program killed by signal `N` is reported on stderr — the one byte sequence
/// this wrapper adds, and only on that abnormal path — and `clean run` exits
/// with `128 + N`, the status a POSIX shell reports for it.
pub(crate) fn handle_run_command(args: RunArgs) -> anyhow::Result<()> {
    // The experimental trust-cg lane (LX0) is its own build; the default C
    // lane below is untouched by it.
    #[cfg(feature = "trust-ir-backend")]
    {
        use crate::cli::RunBackend;
        if args.backend == RunBackend::TrustCg {
            return crate::cmd_run_trustcg::handle_run_trustcg(&args);
        }
        if args.receipt.is_some() {
            anyhow::bail!(
                "`--receipt` records the `--backend trust-cg` build; the C lane writes no receipt"
            );
        }
    }
    let artifact = emit_native_c_artifact(&args.file, &args.decl, args.opt_level)?;
    let built = artifact.build_in_scratch(true)?;
    let status = run_inheriting_stdio(built.binary(), &args.args)?;
    // Release (or deliberately keep) the scratch directory BEFORE exiting:
    // `std::process::exit` skips destructors.
    if args.keep_temp {
        let dir = keep_scratch(built);
        eprintln!("clean run: kept build directory at {}", dir.display());
    } else {
        drop(built);
    }
    exit_like_program(status)
}

/// End `clean run` the way the program ended: success, its own nonzero
/// status, or `128 + N` after reporting signal `N` on stderr. Shared by the C
/// lane and the experimental trust-cg lane.
pub(crate) fn exit_like_program(status: ExitStatus) -> anyhow::Result<()> {
    match exit_disposition(status) {
        ExitDisposition::Success => Ok(()),
        ExitDisposition::Code(code) => std::process::exit(code),
        ExitDisposition::Signal(signal) => {
            eprintln!(
                "clean run: program terminated by signal {signal} ({})",
                signal_name(signal)
            );
            std::process::exit(128 + signal)
        }
    }
}

/// Run the built program with this process's own stdin, stdout and stderr,
/// and wait for it.
pub(crate) fn run_inheriting_stdio(
    binary: &Path,
    run_args: &[String],
) -> anyhow::Result<ExitStatus> {
    Command::new(binary)
        .args(run_args)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .with_context(|| format!("failed to run native binary {}", binary.display()))
}

/// How `clean run` itself ends, given how the program ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExitDisposition {
    /// The program exited with status 0.
    Success,
    /// The program exited with this nonzero status; `clean run` exits with it.
    Code(i32),
    /// The program was killed by this signal.
    Signal(i32),
}

/// Classify a finished program's status.
pub(crate) fn exit_disposition(status: ExitStatus) -> ExitDisposition {
    if let Some(code) = status.code() {
        return if code == 0 {
            ExitDisposition::Success
        } else {
            ExitDisposition::Code(code)
        };
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return ExitDisposition::Signal(signal);
        }
    }
    // Neither a code nor a signal: report a generic failure rather than a
    // success nobody observed.
    ExitDisposition::Code(1)
}

/// The conventional name of a POSIX signal number, for the report line.
pub(crate) fn signal_name(signal: i32) -> &'static str {
    match signal {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        5 => "SIGTRAP",
        6 => "SIGABRT",
        8 => "SIGFPE",
        9 => "SIGKILL",
        10 if cfg!(target_os = "macos") => "SIGBUS",
        7 if cfg!(target_os = "linux") => "SIGBUS",
        11 => "SIGSEGV",
        13 => "SIGPIPE",
        14 => "SIGALRM",
        15 => "SIGTERM",
        _ => "unknown signal",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_native::native_build::emit_entry_c_with_type;
    use clean_native::native_build::{classify_entry, entry_arity_in_c, EntryKind};
    use std::path::PathBuf;

    /// What a test reads back from a built program: its stdout and status.
    /// The production wrapper hands the program this process's own stdio
    /// instead ([`run_inheriting_stdio`]); these tests are about the BUILT
    /// program's bytes, so they capture them.
    struct RunOutcome {
        stdout: String,
        exit_code: i32,
    }

    /// The wrapper's status mapping, on real processes: a nonzero exit is
    /// propagated as itself, and a signal is reported as a signal — never as
    /// the `255` / `-1` the captured-output wrapper used to print.
    #[test]
    fn test_exit_disposition_code_and_signal_are_distinguished() {
        let run = |script: &str| {
            Command::new("sh")
                .args(["-c", script])
                .status()
                .expect("run sh")
        };
        assert_eq!(exit_disposition(run("exit 0")), ExitDisposition::Success);
        assert_eq!(exit_disposition(run("exit 7")), ExitDisposition::Code(7));
        // SIGKILL and SIGTERM: a crash signal (SEGV, ABRT) would make macOS
        // write a crash report for the shell on every run of this test.
        assert_eq!(
            exit_disposition(run("kill -KILL $$")),
            ExitDisposition::Signal(9)
        );
        assert_eq!(
            exit_disposition(run("kill -TERM $$")),
            ExitDisposition::Signal(15)
        );
        assert_eq!(signal_name(11), "SIGSEGV");
        assert_eq!(signal_name(6), "SIGABRT");
        // The production runner hands the status back unchanged.
        let status = run_inheriting_stdio(
            Path::new("/bin/sh"),
            &["-c".to_string(), "exit 5".to_string()],
        )
        .expect("run /bin/sh");
        assert_eq!(exit_disposition(status), ExitDisposition::Code(5));
    }

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
        let artifact = emit_native_c_artifact(file, decl, 0)?;
        let built = artifact.build_in_scratch(true)?;
        let output = Command::new(built.binary()).args(run_args).output()?;
        Ok(RunOutcome {
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            exit_code: output.status.code().unwrap_or(-1),
        })
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

    #[test]
    fn test_run_preserves_string_literal_that_looks_like_a_native_call() {
        if !cc_available() {
            return;
        }
        let (_dir, file) =
            write_temp_lean(r#"def main : IO Unit := IO.println "l_missingFromThisString()""#);
        let outcome = build_and_run_io_entry(&file, "main").expect("build and run literal");
        assert_eq!(outcome.exit_code, 0);
        assert_eq!(outcome.stdout, "l_missingFromThisString()\n");
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

    /// RECURSION through a `do`-block: a list-printing program prints its
    /// elements in list order, not reversed.
    ///
    /// The straight-line control above passed while this printed `c b a` with
    /// status 0 — silent wrong output, the shape of every argv- or
    /// list-printing Lean program. The recursor lowering materialized the arm's
    /// induction hypothesis (`dump rest`) as a `let` at the HEAD of the arm,
    /// ahead of `IO.println s`; under the eager-effect `IO` model of
    /// [`clean_native::native_build`] a hoisted self-call is a hoisted EFFECT, so the
    /// whole tail printed before the head. Fixed at the lowering
    /// (`to_lcnf::rec_ih`): the IH is a call of the recursive function made
    /// where the arm uses it, inside the bind continuation, never at its head.
    ///
    /// Note what this asserts and why it is not C-implementation-defined: the
    /// emitted effects are separate C STATEMENTS, never operands of one call,
    /// so their order is fixed by the emitted sequence and no C compiler is
    /// free to choose it.
    #[test]
    fn test_run_io_recursive_do_block_over_list_prints_in_list_order() {
        if !cc_available() {
            eprintln!(
                "skipping test_run_io_recursive_do_block_over_list_prints_in_list_order: no cc"
            );
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def dump : List String -> IO Unit\n  \
             | [] => pure ()\n  \
             | s :: rest => do\n    \
             IO.println s\n    \
             dump rest\n\
             def main : IO Unit := dump [\"a\", \"b\", \"c\"]\n",
        );
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run recursive dump");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "a\nb\nc\n",
            "a recursive do-block must print in list order, not reversed"
        );
    }

    /// The same defect on the `Nat` arm of the recursor lowering, which binds
    /// its induction hypothesis at a second site (`build_nat_succ_arm_body`).
    /// Measured reversed (`0 1 2`) before the fix.
    #[test]
    fn test_run_io_recursive_do_block_over_nat_counts_down_in_source_order() {
        if !cc_available() {
            eprintln!(
                "skipping test_run_io_recursive_do_block_over_nat_counts_down_in_source_order: no cc"
            );
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def countdown : Nat -> IO Unit\n  \
             | 0 => pure ()\n  \
             | n + 1 => do\n    \
             IO.println (toString n)\n    \
             countdown n\n\
             def main : IO Unit := countdown 3\n",
        );
        let outcome =
            build_and_run_io_entry(&file, "main").expect("build+link+run recursive countdown");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "2\n1\n0\n",
            "each iteration must print before it recurses"
        );
    }

    /// THREE statements in the recursive arm, not two: the IH is used in a
    /// continuation nested inside another continuation, so its call has to be
    /// made there (`to_lcnf::rec_ih` resolves an IH where it occurs), past a
    /// `Fun`, rather than in the first one.
    ///
    /// Measured scope, so this is not read as more than it is: with
    /// `lambda_lift`'s capture-boundary swap restricted back to the self entry
    /// this case still PASSES — the shape that needs two boundaries is a
    /// recursion nested inside another recursion, pinned by
    /// `lambda_lift::tests::test_lift_call_crossing_two_capture_boundaries_binds_every_argument`
    /// and by `native_build`'s nested-`for` fixture. What this pins is the
    /// call made in the innermost continuation.
    #[test]
    fn test_run_io_recursive_do_block_with_two_statements_per_arm_runs() {
        if !cc_available() {
            eprintln!(
                "skipping test_run_io_recursive_do_block_with_two_statements_per_arm_runs: no cc"
            );
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def dump2 : List String -> IO Unit\n  \
             | [] => pure ()\n  \
             | s :: rest => do\n    \
             IO.println s\n    \
             IO.println \"-\"\n    \
             dump2 rest\n\
             def main : IO Unit := dump2 [\"a\", \"b\"]\n",
        );
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run nested arm");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "a\n-\nb\n-\n",
            "both statements run before the recursive call, once per element"
        );
    }

    /// The order fix must not disturb a PURE recursion, whose induction
    /// hypothesis is consumed directly in the arm and therefore never moves.
    #[test]
    fn test_run_io_pure_recursion_results_are_unchanged_by_the_order_fix() {
        if !cc_available() {
            eprintln!(
                "skipping test_run_io_pure_recursion_results_are_unchanged_by_the_order_fix: no cc"
            );
            return;
        }
        let (_dir, file) = write_temp_lean(
            "def sumList : List Nat -> Nat\n  \
             | [] => 0\n  \
             | x :: rest => x + sumList rest\n\
             def main : IO Unit := IO.println (toString (sumList [1, 2, 3, 4]))\n",
        );
        let outcome = build_and_run_io_entry(&file, "main").expect("build+link+run pure recursion");
        assert_eq!(outcome.exit_code, 0, "exit code");
        assert_eq!(
            outcome.stdout, "10\n",
            "a directly-consumed IH still computes"
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
