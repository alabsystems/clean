// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rfl` over wrapped UInt64 arithmetic is DECIDED by `clean check`, inside a
//! resource ceiling (WS6.11, finding F-106, proof-program row AL.uf05).
//!
//! Measured 2026-09-19 at 9185207ab with the release binary, before the fix:
//! `dotOf (2^64-1) (2^64-1) 2 3 = 2^64-5 := rfl` passed 8 GB of RSS in 40 s and
//! was killed there, as did `triple 2^63` and the bare
//! `(18446744073709551615 : UInt64) * 2 = 18446744073709551614`, while every
//! off-by-one twin was refused in about a second. The cause was the
//! elaborator's unifier WHNF-ing a proof argument (`Nat.mod_lt <value> …`, a
//! `Nat.rec` as long as the value); see
//! `crates/clean-elab/src/unify/unifier/proof_irrel.rs`.
//!
//! The ceiling is the discriminator, not the clock: the runaway grows by
//! hundreds of megabytes a second, so it crosses 1 GB within seconds on any
//! build, while the decided check peaks well under 0.1 GB. The wall budget is
//! only a guard against a hang that does not allocate, and is generous because
//! this suite runs the DEBUG binary on a shared box. The release timing (the
//! increment's "under 5 s") is recorded in
//! `docs/issues/2026-09-19-uint64-rfl-wrapped-literal-runaway.md`.
//!
//! Driven through the real `clean` binary: the repo's landing rule is that a
//! capability does not count without the production caller that invokes it.

#![cfg(unix)]

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// RSS ceiling for one `clean check` invocation.
const CEILING_KB: u64 = 1024 * 1024;
/// Hang guard only (see the module doc); never a performance claim.
const WALL_BUDGET: Duration = Duration::from_secs(600);

/// `probes/p07_structure.lean` of the proof program, verbatim.
const DOT_OF: &str = "structure Pt where
  x : UInt64
  y : UInt64

def dot (p q : Pt) : UInt64 := p.x * q.x + p.y * q.y
def dotOf (a b c d : UInt64) : UInt64 := dot ⟨a, b⟩ ⟨c, d⟩
";

/// `probes/p11_typeclass_instance.lean` of the proof program, verbatim.
const TRIPLE: &str = "class Scale (α : Type) where
  scale : α → α

instance instScaleU64 : Scale UInt64 where
  scale := fun (x : UInt64) => x * 3

def triple (x : UInt64) : UInt64 := @Scale.scale UInt64 instScaleU64 x
";

/// `(name, lhs, rhs)`: each is `theorem name : lhs = rhs := rfl`, with the
/// right-hand side the Lean semantics of the left (wrapping mod 2^64).
const STATEMENTS: &[(&str, &str, &str)] = &[
    ("dot_small", "dotOf 1 2 3 4", "11"),
    (
        "dot_wrap",
        "dotOf 18446744073709551615 18446744073709551615 2 3",
        "18446744073709551611",
    ),
    (
        "dot_all_max",
        "dotOf 18446744073709551615 18446744073709551615 18446744073709551615 18446744073709551615",
        "2",
    ),
    (
        "dot_high_bit",
        "dotOf 9223372036854775808 3 9223372036854775808 1",
        "3",
    ),
    (
        "triple_high_bit",
        "triple 9223372036854775808",
        "9223372036854775808",
    ),
    (
        "add_wraps_to_zero",
        "(18446744073709551615 : UInt64) + 1",
        "0",
    ),
    // Review additions (adversarial rows the first cut did not carry): the
    // other widths, an underflow, the wrapped value flowing through a `let`,
    // a division, and `toNat` — each a different consumer of the same
    // `Fin.ofNat` proof field.
    ("u32_mul_wraps", "(4294967295 : UInt32) * 2", "4294967294"),
    ("u8_mul_wraps", "(255 : UInt8) * 2", "254"),
    ("sub_underflows", "(0 : UInt64) - 2", "18446744073709551614"),
    (
        "let_bound_wrap",
        "(let x : UInt64 := 18446744073709551615; x * 2)",
        "18446744073709551614",
    ),
    (
        "div_after_wrap",
        "((18446744073709551615 : UInt64) * 3) / 2",
        "9223372036854775806",
    ),
    (
        "to_nat_after_wrap",
        "((18446744073709551615 : UInt64) * 2).toNat",
        "18446744073709551614",
    ),
];

struct Run {
    code: Option<i32>,
    output: String,
    peak_kb: u64,
    killed: Option<&'static str>,
}

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn rss_kb(pid: u32) -> u64 {
    Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .and_then(|s| s.trim().parse().ok())
        .unwrap_or(0)
}

/// `clean check <file>`, polled for RSS and killed at the ceiling or budget.
fn check_under_ceiling(file: &Path) -> Run {
    let mut child = Command::new(clean_path())
        .arg("check")
        .arg(file)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn clean check");
    let mut stdout = child.stdout.take().expect("stdout");
    let mut stderr = child.stderr.take().expect("stderr");
    let out_reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stdout.read_to_string(&mut s);
        s
    });
    let err_reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr.read_to_string(&mut s);
        s
    });
    let started = Instant::now();
    let mut peak_kb = 0;
    let mut killed = None;
    let code = loop {
        if let Some(status) = child.try_wait().expect("poll clean check") {
            break status.code();
        }
        peak_kb = peak_kb.max(rss_kb(child.id()));
        if peak_kb > CEILING_KB {
            killed = Some("RSS ceiling");
        } else if started.elapsed() > WALL_BUDGET {
            killed = Some("wall budget");
        }
        if killed.is_some() {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let output = out_reader.join().unwrap_or_default() + &err_reader.join().unwrap_or_default();
    Run {
        code,
        output,
        peak_kb,
        killed,
    }
}

fn write_source(dir: &Path, name: &str, off_by_one: bool) -> PathBuf {
    let mut text = format!("{DOT_OF}\n{TRIPLE}\n");
    for (thm, lhs, rhs) in STATEMENTS {
        let rhs = if off_by_one {
            (rhs.parse::<u128>().expect("numeric rhs") + 1).to_string()
        } else {
            (*rhs).to_string()
        };
        text.push_str(&format!("theorem {thm} : {lhs} = {rhs} := rfl\n"));
    }
    let path = dir.join(name);
    std::fs::write(&path, text).expect("write probe source");
    path
}

fn scratch_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("clean-al-uf05-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    dir
}

/// AL.uf05 (GAP flips): the statements the proof program's oracle could not
/// decide with `clean check` — it killed them at ~25 GB, or reported
/// `triple 2^63` UNDECIDED — are all PROVED, under the ceiling.
#[test]
fn al_uf05_wrapped_uint64_rfl_is_decided_under_the_ceiling() {
    let dir = scratch_dir("pos");
    let run = check_under_ceiling(&write_source(&dir, "Pos.lean", false));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.killed.is_none(),
        "clean check was killed at the {} (peak {} KB) — the F-106 runaway is back:\n{}",
        run.killed.unwrap_or(""),
        run.peak_kb,
        run.output
    );
    assert_eq!(
        run.code,
        Some(0),
        "every statement must check:\n{}",
        run.output
    );
    assert!(
        run.output.contains(", 0 failed"),
        "no declaration may fail:\n{}",
        run.output
    );
    for (thm, _, _) in STATEMENTS {
        assert!(
            !run.output.contains(&format!("✗ {thm}")),
            "{thm} failed:\n{}",
            run.output
        );
    }
}

/// AL.uf05 negative twin: every right-hand side off by one is REFUSED — a
/// named type mismatch per theorem, under the same ceiling — never a timeout.
#[test]
fn al_uf05_off_by_one_twins_are_refused_not_timed_out() {
    let dir = scratch_dir("neg");
    let run = check_under_ceiling(&write_source(&dir, "Neg.lean", true));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.killed.is_none(),
        "the twins must be refused, not killed at the {} (peak {} KB):\n{}",
        run.killed.unwrap_or(""),
        run.peak_kb,
        run.output
    );
    assert_eq!(
        run.code,
        Some(1),
        "a false theorem must fail the check:\n{}",
        run.output
    );
    for (thm, _, _) in STATEMENTS {
        let line = run
            .output
            .lines()
            .find(|l| l.contains(&format!("✗ {thm}:")))
            .unwrap_or_else(|| panic!("{thm} must be refused by name:\n{}", run.output));
        assert!(
            line.contains("Type mismatch"),
            "{thm} must be refused as a type mismatch, got: {line}"
        );
    }
}
