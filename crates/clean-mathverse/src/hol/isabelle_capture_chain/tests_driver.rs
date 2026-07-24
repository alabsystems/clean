// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the capture-chain [`super::driver`] loop, driven
//! entirely through a fake [`IsabelleBuildRunner`] — no live Isabelle build.

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

use super::driver::{run_capture_chain, RunOptions};
use super::runner::{BuildInvocation, BuildRun, IsabelleBuildRunner};
use super::spec::{ChainSpec, CollectSpec, Segment};
use super::state::{ChainState, SegStatus};

/// A scripted runner: per-session response queues (popped per call), defaulting
/// to OK. Records every invocation for assertions.
struct ScriptedRunner {
    responses: RefCell<HashMap<String, VecDeque<BuildRun>>>,
    calls: RefCell<Vec<String>>,
}

impl ScriptedRunner {
    fn new(scripts: &[(&str, Vec<BuildRun>)]) -> Self {
        let mut map = HashMap::new();
        for (session, runs) in scripts {
            map.insert((*session).to_string(), runs.iter().cloned().collect());
        }
        Self {
            responses: RefCell::new(map),
            calls: RefCell::new(Vec::new()),
        }
    }

    fn call_sessions(&self) -> Vec<String> {
        self.calls.borrow().clone()
    }
}

impl IsabelleBuildRunner for ScriptedRunner {
    fn run_build(
        &self,
        inv: &BuildInvocation,
    ) -> Result<BuildRun, super::error::CaptureChainError> {
        self.calls.borrow_mut().push(inv.session.clone());
        let mut map = self.responses.borrow_mut();
        if let Some(queue) = map.get_mut(&inv.session) {
            if let Some(run) = queue.pop_front() {
                return Ok(run);
            }
        }
        Ok(ok_run())
    }
}

fn ok_run() -> BuildRun {
    BuildRun {
        exit_code: 0,
        output: "Finished\n".to_string(),
    }
}

fn oom_run() -> BuildRun {
    BuildRun {
        exit_code: 1,
        output: "Building X ...\nRun out of store - interrupting threads\n\
                 *** At command \"by\" (line 567 of \"~~/src/HOL/Library/Interval.thy\")\n"
            .to_string(),
    }
}

fn other_run() -> BuildRun {
    BuildRun {
        exit_code: 2,
        output: "*** Type unification failed\n*** Failed to finish proof\n".to_string(),
    }
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("cc_drv_{}_{}", tag, std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mk scratch");
    dir
}

fn seg(session: &str, dir: &Path, parent: &str, theories: &[&str]) -> Segment {
    Segment {
        session: session.to_string(),
        dir: dir.to_path_buf(),
        theories: theories.iter().map(|t| (*t).to_string()).collect(),
        parent: parent.to_string(),
        record_proofs: 4,
        note: None,
    }
}

/// Build a spec whose seg dirs / collect dirs live under `base`.
fn spec_in(base: &Path, threads: usize, segments: Vec<Segment>) -> ChainSpec {
    ChainSpec {
        segments,
        isabelle_home: "/opt/Isabelle".into(),
        dirs: vec![base.join("base_heap")],
        threads,
        collect: CollectSpec {
            from_dir: base.join("from"),
            to_dir: base.join("to"),
            glob: "HOL-Library.*.jsonl".into(),
        },
        comment: None,
    }
}

fn opts(base: &Path, resume: bool, dry: bool) -> RunOptions {
    RunOptions {
        work_dir: base.join("work"),
        resume,
        dry,
    }
}

fn load_state(base: &Path) -> ChainState {
    ChainState::load(&base.join("work").join("capture_chain_state.json")).expect("state exists")
}

#[test]
fn test_happy_path_all_ok_collects_captures() {
    let base = scratch("happy");
    // Seed one capture file that the first OK build should relocate.
    let from = base.join("from");
    std::fs::create_dir_all(&from).expect("mk from");
    std::fs::write(from.join("HOL-Library.Foo.jsonl"), b"{}").expect("seed capture");

    let spec = spec_in(
        &base,
        1,
        vec![
            seg("ZP-A", &base.join("zp_a"), "ZP-Base", &["HOL-Library.Foo"]),
            seg("ZP-B", &base.join("zp_b"), "ZP-A", &["HOL-Library.Bar"]),
        ],
    );
    let runner = ScriptedRunner::new(&[]);
    let summary =
        run_capture_chain(&spec, &opts(&base, false, false), &runner).expect("chain runs");

    assert_eq!(summary.total_segments, 2);
    assert_eq!(summary.ok, 2);
    assert_eq!(summary.proofless, 0);
    assert_eq!(
        summary.captures_collected, 1,
        "the seeded capture was moved"
    );
    assert_eq!(runner.call_sessions(), vec!["ZP-A", "ZP-B"]);
    assert!(base.join("to").join("HOL-Library.Foo.jsonl").exists());
    // ROOT files were generated per segment.
    assert!(base.join("zp_a").join("ROOT").exists());
    assert!(base.join("zp_b").join("ROOT").exists());
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_proofless_ladder_single_theory() {
    let base = scratch("proofless");
    let spec = spec_in(
        &base,
        1,
        vec![seg(
            "ZP-Interval",
            &base.join("zp_iv"),
            "ZP-Base",
            &["HOL-Library.Interval"],
        )],
    );
    // First build OOMs; after demotion to record_proofs=2 it succeeds.
    let runner = ScriptedRunner::new(&[("ZP-Interval", vec![oom_run(), ok_run()])]);
    let summary =
        run_capture_chain(&spec, &opts(&base, false, false), &runner).expect("chain heals");

    assert_eq!(summary.proofless, 1, "segment ended proofless");
    assert_eq!(summary.ok, 0);
    let state = load_state(&base);
    assert_eq!(state.segments[0].status, SegStatus::Proofless);
    assert_eq!(
        state.segments[0].segment.record_proofs, 2,
        "demoted to a proofless (record_proofs=2) bake"
    );
    assert_eq!(
        state.segments[0].proofless_theory.as_deref(),
        Some("HOL-Library.Interval")
    );
    assert_eq!(
        state.segments[0].attempts.len(),
        2,
        "one OOM + one OK attempt"
    );
    assert_eq!(runner.call_sessions(), vec!["ZP-Interval", "ZP-Interval"]);
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_bisect_ladder_multitheory_repoints_successor() {
    let base = scratch("bisect");
    let spec = spec_in(
        &base,
        1,
        vec![
            seg("ZP-A", &base.join("zp_a"), "ZP-Base", &["HOL-Library.A"]),
            seg(
                "ZP-B",
                &base.join("zp_b"),
                "ZP-A",
                &["HOL-Library.B1", "HOL-Library.B2"],
            ),
            seg("ZP-C", &base.join("zp_c"), "ZP-B", &["HOL-Library.C"]),
        ],
    );
    // ZP-B OOMs at threads=1 → bisect into ZP-B-1 / ZP-B-2 (both then OK).
    let runner = ScriptedRunner::new(&[("ZP-B", vec![oom_run()])]);
    let summary =
        run_capture_chain(&spec, &opts(&base, false, false), &runner).expect("chain heals");

    assert_eq!(summary.bisects, 1);
    assert_eq!(
        summary.total_segments, 4,
        "ZP-B replaced by two sub-segments"
    );
    let state = load_state(&base);
    let sessions: Vec<&str> = state
        .segments
        .iter()
        .map(|s| s.segment.session.as_str())
        .collect();
    assert_eq!(sessions, vec!["ZP-A", "ZP-B-1", "ZP-B-2", "ZP-C"]);
    // The successor was repointed onto the last sub-segment.
    let zp_c = state
        .segments
        .iter()
        .find(|s| s.segment.session == "ZP-C")
        .unwrap();
    assert_eq!(zp_c.segment.parent, "ZP-B-2", "ZP-C now chains on ZP-B-2");
    let zp_b2 = state
        .segments
        .iter()
        .find(|s| s.segment.session == "ZP-B-2")
        .unwrap();
    assert_eq!(
        zp_b2.segment.parent, "ZP-B-1",
        "suffix chains on the prefix"
    );
    assert_eq!(summary.ok, 4);
    // Call order: A, B(OOM), then the two subs, then C.
    assert_eq!(
        runner.call_sessions(),
        vec!["ZP-A", "ZP-B", "ZP-B-1", "ZP-B-2", "ZP-C"]
    );
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_retry_threads1_then_ok() {
    let base = scratch("retry");
    // Global threads=6: the first attempt runs concurrent and OOMs.
    let spec = spec_in(
        &base,
        6,
        vec![seg(
            "ZP-R",
            &base.join("zp_r"),
            "ZP-Base",
            &["HOL-Library.R1", "HOL-Library.R2"],
        )],
    );
    let runner = ScriptedRunner::new(&[("ZP-R", vec![oom_run(), ok_run()])]);
    let summary =
        run_capture_chain(&spec, &opts(&base, false, false), &runner).expect("chain heals");

    assert_eq!(summary.retries_threads1, 1);
    assert_eq!(summary.ok, 1);
    let state = load_state(&base);
    assert_eq!(state.segments[0].threads, 1, "retried serialized");
    assert!(state.segments[0].ladder.retry_threads1);
    assert_eq!(state.segments[0].status, SegStatus::Ok);
    assert_eq!(runner.call_sessions(), vec!["ZP-R", "ZP-R"]);
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_other_failure_halts_and_marks_failed() {
    let base = scratch("other");
    let spec = spec_in(
        &base,
        1,
        vec![seg(
            "ZP-X",
            &base.join("zp_x"),
            "ZP-Base",
            &["HOL-Library.X"],
        )],
    );
    let runner = ScriptedRunner::new(&[("ZP-X", vec![other_run()])]);
    let err = run_capture_chain(&spec, &opts(&base, false, false), &runner)
        .expect_err("non-OOM failure halts the chain");
    assert!(
        format!("{err}").contains("build failed"),
        "surfaced as BuildFailed: {err}"
    );
    let state = load_state(&base);
    assert_eq!(state.segments[0].status, SegStatus::Failed);
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_resume_skips_resolved_segments() {
    let base = scratch("resume");
    let spec = spec_in(
        &base,
        1,
        vec![
            seg("ZP-A", &base.join("zp_a"), "ZP-Base", &["HOL-Library.A"]),
            seg("ZP-B", &base.join("zp_b"), "ZP-A", &["HOL-Library.B"]),
        ],
    );
    // First run: ZP-A OK, ZP-B fails (non-OOM) → halt.
    let runner1 = ScriptedRunner::new(&[("ZP-B", vec![other_run()])]);
    let _ = run_capture_chain(&spec, &opts(&base, false, false), &runner1)
        .expect_err("first run halts on ZP-B");
    assert_eq!(runner1.call_sessions(), vec!["ZP-A", "ZP-B"]);

    // Resume: ZP-A is already OK and must be skipped; only ZP-B rebuilds (now OK).
    let runner2 = ScriptedRunner::new(&[]);
    let summary = run_capture_chain(&spec, &opts(&base, true, false), &runner2).expect("resume ok");
    assert_eq!(
        runner2.call_sessions(),
        vec!["ZP-B"],
        "resume rebuilt only the unresolved segment"
    );
    assert_eq!(summary.ok, 2);
    let state = load_state(&base);
    assert!(state.segments.iter().all(|s| s.status == SegStatus::Ok));
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_resume_refuses_changed_spec() {
    let base = scratch("changed");
    let spec = spec_in(
        &base,
        1,
        vec![seg(
            "ZP-A",
            &base.join("zp_a"),
            "ZP-Base",
            &["HOL-Library.A"],
        )],
    );
    run_capture_chain(&spec, &opts(&base, false, false), &ScriptedRunner::new(&[]))
        .expect("first run ok");
    // Mutate the spec, then resume: the hash mismatch must be refused.
    let mut changed = spec.clone();
    changed.threads = 4;
    let err = run_capture_chain(
        &changed,
        &opts(&base, true, false),
        &ScriptedRunner::new(&[]),
    )
    .expect_err("changed spec is refused on resume");
    assert!(format!("{err}").contains("different spec"), "got: {err}");
    let _ = std::fs::remove_dir_all(&base);
}

#[test]
fn test_dry_run_builds_nothing_and_writes_no_state() {
    let base = scratch("dry");
    let spec = spec_in(
        &base,
        1,
        vec![seg(
            "ZP-A",
            &base.join("zp_a"),
            "ZP-Base",
            &["HOL-Library.A"],
        )],
    );
    let runner = ScriptedRunner::new(&[]);
    let summary = run_capture_chain(&spec, &opts(&base, false, true), &runner).expect("dry ok");
    assert_eq!(summary.total_segments, 1);
    assert!(runner.call_sessions().is_empty(), "dry run builds nothing");
    assert!(
        !base.join("work").join("capture_chain_state.json").exists(),
        "dry run writes no state file"
    );
    let _ = std::fs::remove_dir_all(&base);
}
