// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standalone executable wrapper around the paragon integration benchmark.
//!
//! The benchmark body lives in
//! `crates/clean-cli/tests/paragon_integration_bench.rs` (the durable test
//! artifact, where it LINKS for a normal non-worktree checkout). Here it is
//! `include!`d so this trust-ir-free standalone workspace can EXECUTE the same
//! measurement inside a worktree, where the full-workspace lockfile collides.
//!
//! To survive goals that ABORT the in-repo prover (stack overflow), the parent
//! process runs each goal in its OWN child process (`--goal <idx>`): a child
//! that crashes is recorded as `Crashed`, never killing the batch. The
//! `#[cfg(test)] #[test]` wrapper in the included file is compiled out of this
//! normal binary build.

include!("../../crates/clean-cli/tests/paragon_integration_bench.rs");

use std::process::Command;
// NOTE: `Duration` is already in scope from the `include!`d benchmark file.
use std::time::Instant;

/// Hard wall-clock budget per child goal. The engine's 30 s soft timeout is not
/// honored by every lane (a runaway search was observed running ~29 min); this
/// guarantees the batch terminates. A child exceeding it is killed and recorded
/// as `Crashed`.
const CHILD_WALL_LIMIT: Duration = Duration::from_secs(75);

/// Spawn one goal in a child process, enforcing `CHILD_WALL_LIMIT`. Returns the
/// child's `OUTCOME`, or `Crashed` on abort (non-zero/signal exit) or wall-limit
/// kill.
fn run_child(exe: &std::path::Path, idx: usize) -> Outcome {
    // Pipe stdout (to read `OUTCOME`); inherit stderr so child RESULT/DIAG and
    // overflow messages stream straight through without a pipe-buffer deadlock.
    let mut child = Command::new(exe)
        .arg("--goal")
        .arg(idx.to_string())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("spawn child");

    let deadline = Instant::now() + CHILD_WALL_LIMIT;
    let killed = loop {
        match child.try_wait().expect("try_wait") {
            Some(_) => break false,
            None if Instant::now() >= deadline => {
                child.kill().ok();
                break true;
            }
            None => std::thread::sleep(Duration::from_millis(200)),
        }
    };

    let output = child.wait_with_output().expect("collect child output");
    if killed || !output.status.success() {
        return Outcome::Crashed;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout
        .lines()
        .find_map(|l| l.strip_prefix("OUTCOME "))
        .and_then(|rest| rest.split_whitespace().nth(1))
        .and_then(Outcome::from_token)
        .unwrap_or_else(|| panic!("child {idx} produced no OUTCOME line"))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Child mode: run exactly one goal and print `OUTCOME <idx> <token>`.
    if let Some(pos) = args.iter().position(|a| a == "--goal") {
        let idx: usize = args
            .get(pos + 1)
            .and_then(|s| s.parse().ok())
            .expect("--goal needs a numeric index");
        run_one(idx);
        return;
    }

    // In-process regression mode (no crash isolation): run every NON-aborting
    // spec on one big-stack worker and check each live outcome against its
    // pinned `expected` — the exact path the `#[cfg(test)] #[test]` exercises.
    // The two aborting goals are not run here (pinned `Crashed`, measured by the
    // default fan-out mode). Exits non-zero on any pinned-outcome drift.
    if args.iter().any(|a| a == "--in-process") {
        let (rows, mismatches) = run_regression();
        print_report(&rows);
        if !mismatches.is_empty() {
            eprintln!(
                "FAIL: {} pinned outcome(s) changed:\n{}",
                mismatches.len(),
                mismatches.join("\n")
            );
            std::process::exit(1);
        }
        return;
    }

    // Parent mode: fan each goal out to a child process for crash isolation.
    let specs = build_specs();
    let exe = std::env::current_exe().expect("current_exe");
    let mut rows: Vec<(Class, String, Outcome)> = Vec::with_capacity(specs.len());

    for (idx, spec) in specs.iter().enumerate() {
        let outcome = run_child(&exe, idx);
        eprintln!(
            "RESULT class={} outcome={outcome:?} label={:?}",
            spec.class.tag(),
            spec.label
        );
        rows.push((spec.class, spec.label.clone(), outcome));
    }

    let (total, _solved, bogus) = print_report(&rows);
    if bogus != 0 {
        eprintln!("FAIL: {bogus} returned proof(s) failed the kernel re-check");
        std::process::exit(1);
    }
    if total != 30 {
        eprintln!("FAIL: expected 30 curated goals, ran {total}");
        std::process::exit(1);
    }
}
