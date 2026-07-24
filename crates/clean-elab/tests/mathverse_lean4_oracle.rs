// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Lean 4 oracle harness for mathverse tactic property tests.
//!
//! Shells out to a `lean` binary, posing each Presburger formula as a goal
//! that Lean 4's mathlib-mathverse should be able to refute when the formula
//! is `ℤ`-unsatisfiable. Used to cross-check the clean mathverse
//! implementation against the canonical Lean 4 implementation.
//!
//! Tests are env-gated so the default `cargo test` run doesn't pay the
//! subprocess cost. Enable with `CLEAN_MATHVERSE_ORACLE=1`. Override the
//! binary with `CLEAN_LEAN4_BIN=/path/to/lean`.
//!
//! See `docs/DESIGN_MATHVERSE_COMPLETION.md` §5 PR-4 for the design.

use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

/// Outcome of asking Lean 4's mathverse tactic whether a constraint set is
/// `ℤ`-unsatisfiable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleAnswer {
    /// Lean's `mathverse` proved the negation — the formula is `ℤ`-unsat.
    Unsat,
    /// Lean's `mathverse` failed to prove the negation. The formula may be
    /// satisfiable, or it may exceed Lean's mathverse's reach. Don't read
    /// this as definitive `Sat`.
    Maybe,
    /// Couldn't run Lean (no binary, timeout, harness error). Tests
    /// should `skip` rather than fail.
    Unavailable(String),
}

/// Locate the `lean` binary. Priority order:
/// 1. `CLEAN_LEAN4_BIN` env override
/// 2. `~/.elan/bin/lean` (elan-managed install)
/// 3. `lean` on `$PATH`
fn lean4_binary() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("CLEAN_LEAN4_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    if let Some(home) = std::env::var_os("HOME") {
        let p = PathBuf::from(home).join(".elan/bin/lean");
        if p.exists() {
            return Some(p);
        }
    }
    // Final fallback: PATH lookup via `which`.
    let out = Command::new("which").arg("lean").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    p.exists().then_some(p)
}

/// Ask Lean 4's `mathverse` tactic whether the supplied conjunction of
/// `Int` constraints is `ℤ`-unsatisfiable. The argument is the *body* of
/// the formula: e.g. `"2 * x = 1"` or `"3 * x ≥ 5 ∧ 3 * x ≤ 6"`. The
/// supplied free variables must be `xN` (`x0`, `x1`, ...). The harness
/// adds the `∀ : Int → ... → ¬ <body> → False`-shaped wrapper and runs
/// mathverse.
pub fn lean4_mathverse_decides_unsat(formula: &str, num_vars: usize) -> OracleAnswer {
    let Some(lean_bin) = lean4_binary() else {
        return OracleAnswer::Unavailable("no lean binary found".to_string());
    };

    let tmp = match tempfile::tempdir() {
        Ok(d) => d,
        Err(e) => return OracleAnswer::Unavailable(format!("tempdir: {e}")),
    };
    let lean_file = tmp.path().join("oracle.lean");

    let binders: String = (0..num_vars)
        .map(|i| format!("(x{i} : Int)"))
        .collect::<Vec<_>>()
        .join(" ");

    let source = if binders.is_empty() {
        format!("example : ¬ ({formula}) := by omega\n")
    } else {
        format!("example {binders} : ¬ ({formula}) := by omega\n")
    };

    match std::fs::File::create(&lean_file).and_then(|mut f| f.write_all(source.as_bytes())) {
        Ok(()) => {}
        Err(e) => return OracleAnswer::Unavailable(format!("write source: {e}")),
    }

    let mut cmd = Command::new(&lean_bin);
    cmd.arg(&lean_file);
    cmd.current_dir(tmp.path());

    let child = match cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => return OracleAnswer::Unavailable(format!("spawn lean: {e}")),
    };

    let output = match wait_with_timeout(child, Duration::from_secs(30)) {
        Ok(o) => o,
        Err(e) => return OracleAnswer::Unavailable(format!("lean run: {e}")),
    };

    // Lean 4 writes diagnostics to stdout (not stderr) and exits 0 even when
    // a tactic fails. Classify by looking for the canonical omega-failure
    // message; anything else with "error:" is a harness / source issue.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");

    if combined.contains("omega could not prove")
        || combined.contains("omega could not solve")
        || combined.contains("unsolved goals")
        || combined.contains("no progress")
    {
        return OracleAnswer::Maybe;
    }
    if combined.contains("error:") {
        return OracleAnswer::Unavailable(format!(
            "lean reported an error other than omega failure: {combined}"
        ));
    }
    if !output.status.success() {
        return OracleAnswer::Unavailable(format!(
            "lean exited non-zero (exit {}): {combined}",
            output.status
        ));
    }
    OracleAnswer::Unsat
}

fn wait_with_timeout(
    mut child: std::process::Child,
    timeout: Duration,
) -> std::io::Result<std::process::Output> {
    use std::sync::mpsc;
    use std::thread;

    let stdout = child.stdout.take();
    let stderr = child.stderr.take();

    let (tx, rx) = mpsc::channel();
    let stdout_thread = thread::spawn(move || -> Vec<u8> {
        use std::io::Read;
        let mut buf = Vec::new();
        if let Some(mut s) = stdout {
            let _ = s.read_to_end(&mut buf);
        }
        buf
    });
    let stderr_thread = thread::spawn(move || -> Vec<u8> {
        use std::io::Read;
        let mut buf = Vec::new();
        if let Some(mut s) = stderr {
            let _ = s.read_to_end(&mut buf);
        }
        buf
    });

    let id = child.id();
    thread::spawn(move || {
        let status = child.wait();
        let _ = tx.send(status);
    });

    match rx.recv_timeout(timeout) {
        Ok(status) => {
            let stdout_buf = stdout_thread.join().unwrap_or_default();
            let stderr_buf = stderr_thread.join().unwrap_or_default();
            Ok(std::process::Output {
                status: status?,
                stdout: stdout_buf,
                stderr: stderr_buf,
            })
        }
        Err(_) => {
            // Timeout: best-effort kill.
            let _ = Command::new("kill").arg("-9").arg(id.to_string()).status();
            Err(std::io::Error::new(
                std::io::ErrorKind::TimedOut,
                "lean subprocess exceeded 30s",
            ))
        }
    }
}

fn skip_unless_enabled() -> bool {
    if std::env::var("CLEAN_MATHVERSE_ORACLE").is_ok() {
        return true;
    }
    eprintln!("skip: oracle tests gated on CLEAN_MATHVERSE_ORACLE=1 (subprocess to lean is slow)");
    false
}

// -----------------------------------------------------------------------------
// Hand-curated correctness probes for the oracle harness itself.
//
// These tests verify:
//   (a) the harness can locate `lean`, write a source, run it, and parse the
//       outcome (the binary plumbing works);
//   (b) Lean 4's mathverse gives the answers we expect on cases that drove
//       development of this work.
//
// The Pugh case (`3x ≥ 5 ∧ 3x ≤ 6`) is included specifically because that's
// the integer-satisfiable example that exposed the soundness bug in the
// reverted PR-1.
// -----------------------------------------------------------------------------

#[test]
fn oracle_finds_lean_binary() {
    let bin = lean4_binary();
    assert!(
        bin.is_some(),
        "no `lean` binary found on this machine (checked CLEAN_LEAN4_BIN, ~/.elan/bin/lean, PATH)"
    );
}

#[test]
fn oracle_refutes_2x_equals_1() {
    if !skip_unless_enabled() {
        return;
    }
    let result = lean4_mathverse_decides_unsat("2 * x0 = 1", 1);
    assert_eq!(
        result,
        OracleAnswer::Unsat,
        "Lean 4 mathverse should refute `2*x = 1` over ℤ"
    );
}

#[test]
fn oracle_refutes_3x_between_4_and_5() {
    if !skip_unless_enabled() {
        return;
    }
    // 3x ≤ 5 ∧ 3x ≥ 4 — no integer in [4/3, 5/3]; ℤ-unsat.
    let result = lean4_mathverse_decides_unsat("3 * x0 ≤ 5 ∧ 3 * x0 ≥ 4", 1);
    assert_eq!(result, OracleAnswer::Unsat);
}

#[test]
fn oracle_does_not_refute_3x_between_5_and_6() {
    if !skip_unless_enabled() {
        return;
    }
    // 3x ≥ 5 ∧ 3x ≤ 6 — integer solution x = 2; ℤ-sat. Lean's mathverse
    // must NOT prove the negation. This is the soundness probe that
    // caught the reverted PR-1 bug.
    let result = lean4_mathverse_decides_unsat("3 * x0 ≥ 5 ∧ 3 * x0 ≤ 6", 1);
    assert_eq!(
        result,
        OracleAnswer::Maybe,
        "the formula has integer solution x=2; mathverse must not refute it"
    );
}

#[test]
fn oracle_refutes_simple_contradiction() {
    if !skip_unless_enabled() {
        return;
    }
    let result = lean4_mathverse_decides_unsat("x0 > 0 ∧ x0 < 1", 1);
    assert_eq!(result, OracleAnswer::Unsat);
}
