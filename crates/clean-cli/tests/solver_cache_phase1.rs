// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for the Phase-1 solver-results-cache tooling
//! (`clean solver` — `VCIDX01` index + telemetry analysis).
//!
//! See `designs/2026-06-24-solver-results-cache-service.md`. This test lives in
//! `clean-cli` (not `clean-auto`) on purpose: `clean-auto`'s lib *test* binary
//! pulls in the trust-cg/trust-ir dev-dependencies, whose linkability is being
//! repaired in a parallel session. `clean-cli` depends only on `clean-auto`'s
//! *lib* (no trust-cg), so this test links regardless of that repair, and it
//! drives the exact public API surface (`clean_auto::solver_cache_service`) the
//! `clean solver` CLI uses.
//!
//! What it proves:
//! - a synthetic `solver-attempt-record-v1` corpus builds a `VCIDX01` index that
//!   loads fail-closed and looks up the correct per-obligation summary;
//! - a tampered index is rejected at load (self-digest check);
//! - the stats / weak-area / VBS-gap aggregates are computed correctly.

use std::fs;
use std::io::Write;
use std::path::Path;

use clean_auto::solver_cache_service as svc;

/// Write a synthetic `attempts.jsonl` telemetry corpus into `<dir>/attempts.jsonl`.
///
/// Two obligations, two engines, complementary outcomes — the canonical case
/// where the VBS−SBS gap is positive (each engine wins on the obligation the
/// other loses):
///
/// | obligation | clean-smt        | oracle           |
/// |------------|------------------|------------------|
/// | `aa…`      | proved, 30 ms    | timeout, 5000 ms |
/// | `bb…`      | timeout, 5000 ms | proved, 20 ms    |
fn write_corpus(dir: &Path) {
    fs::create_dir_all(dir).expect("mkdir telemetry dir");
    let oblig_a = format!("blake3:{}", "aa".repeat(32));
    let oblig_b = format!("blake3:{}", "bb".repeat(32));
    let cert = format!("blake3:{}", "cd".repeat(32));
    let rows = [
        // aa: smt proves fast, oracle times out.
        row(
            &oblig_a,
            "clean-smt",
            "clean-cic",
            "proved",
            30,
            Some(&cert),
            false,
        ),
        row(&oblig_a, "oracle", "oracle", "timeout", 5000, None, false),
        // bb: smt times out, oracle proves fast.
        row(
            &oblig_b,
            "clean-smt",
            "clean-cic",
            "timeout",
            5000,
            None,
            false,
        ),
        row(
            &oblig_b,
            "oracle",
            "oracle",
            "proved",
            20,
            Some(&cert),
            false,
        ),
    ];
    let path = dir.join("attempts.jsonl");
    let mut f = fs::File::create(&path).expect("create attempts.jsonl");
    for r in &rows {
        writeln!(f, "{r}").expect("write row");
    }
}

/// Build one `solver-attempt-record-v1` JSON line.
fn row(
    oblig: &str,
    solver: &str,
    theory: &str,
    result: &str,
    wall_ms: u64,
    cert: Option<&str>,
    cache_hit: bool,
) -> String {
    let success = result == "proved";
    let cert_field = match cert {
        Some(c) => format!(",\"proof_term_digest\":\"{c}\""),
        None => String::new(),
    };
    let cache = if cache_hit { "cache_hit" } else { "miss" };
    format!(
        "{{\"schema\":\"solver-attempt-record-v1\",\"obligation_digest\":\"{oblig}\",\
         \"theory_logic\":\"{theory}\",\"solver\":{{\"name\":\"{solver}\",\"version\":\"t\"}},\
         \"strategy\":\"smt→superposition→oracle\",\"result\":\"{result}\",\"wall_ms\":{wall_ms},\
         \"success\":{success}{cert_field},\"cache_outcome\":\"{cache}\",\
         \"decided_at_epoch_s\":1750000000}}"
    )
}

#[test]
fn test_index_build_load_and_lookup() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let out = tmp.path().join("solver.vcidx");

    let summary = svc::build_index(std::slice::from_ref(&dir), &out).expect("build VCIDX01");
    assert_eq!(summary.entries, 2, "two distinct obligations");
    assert_eq!(summary.attempts, 4, "four attempt rows");
    assert_eq!(
        summary.cached, 0,
        "no .scache proof terms in the telemetry dir"
    );
    assert!(summary.corpus_digest.starts_with("blake3:"));

    let index = svc::load_index(&out).expect("index loads fail-closed");
    assert_eq!(index.entry_count(), 2);
    assert_eq!(index.corpus_digest_str(), summary.corpus_digest);

    // aa: 2 attempts, 1 solved, best wall 30 ms.
    let aa = format!("blake3:{}", "aa".repeat(32));
    let s = index.lookup(&aa).expect("aa present");
    assert_eq!(s.attempts, 2);
    assert_eq!(s.solved, 1);
    assert_eq!(s.best_wall_ms, Some(30));
    assert!(!s.cached);

    // bb: best wall 20 ms (oracle).
    let bb = format!("blake3:{}", "bb".repeat(32));
    let s = index.lookup(&bb).expect("bb present");
    assert_eq!(s.best_wall_ms, Some(20));

    // Absent key is a clean miss.
    let cc = format!("blake3:{}", "cc".repeat(32));
    assert!(
        index.lookup(&cc).is_none(),
        "absent obligation is a clean miss"
    );
}

#[test]
fn test_index_load_fail_closed_on_tamper() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let out = tmp.path().join("solver.vcidx");
    svc::build_index(&[dir], &out).expect("build VCIDX01");

    // Flip one byte inside the entry table — the trailing self-digest no longer
    // matches, so the loader must reject it rather than serve a corrupted index.
    let mut bytes = fs::read(&out).expect("read index");
    let flip = 60; // within the entry table, after the 56-byte header
    bytes[flip] ^= 0xff;
    fs::write(&out, &bytes).expect("write tampered index");

    let err = svc::load_index(&out).expect_err("tampered index must fail closed");
    let msg = err.to_string();
    assert!(
        msg.contains("corrupt") || msg.contains("digest"),
        "expected a fail-closed corruption error, got: {msg}"
    );
}

#[test]
fn test_stats_aggregates_are_correct() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);

    let report = svc::stats(&[dir], 5000).expect("stats");
    assert_eq!(report.total_attempts, 4);
    assert_eq!(report.distinct_obligations, 2);

    // clean-smt: 1 proved @ 30, 1 timeout. mean PAR-2 = (30 + 10000)/2 = 5015.
    let smt = &report
        .by_solver
        .iter()
        .find(|(k, _)| k == "clean-smt")
        .expect("clean-smt class")
        .1;
    assert_eq!(smt.attempts, 2);
    assert_eq!(smt.solved, 1);
    assert!((smt.success_rate - 0.5).abs() < 1e-9);
    assert!(
        (smt.mean_par2 - 5015.0).abs() < 1e-9,
        "mean PAR-2 = {}",
        smt.mean_par2
    );
    assert!((smt.timeout_rate - 0.5).abs() < 1e-9);
    assert_eq!(smt.wall_p50, Some(30));

    // Theory slicing: clean-cic seen on clean-smt rows only.
    let cic = &report
        .by_theory
        .iter()
        .find(|(k, _)| k == "clean-cic")
        .expect("clean-cic theory")
        .1;
    assert_eq!(cic.attempts, 2);
}

#[test]
fn test_vbs_gap_positive_when_engines_complement() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);

    let gap = svc::vbs_gap(&[dir], 5000).expect("vbs-gap");
    // VBS picks the winner per obligation: aa→smt(30), bb→oracle(20) ⇒ mean 25.
    assert!(
        (gap.vbs_mean_par2 - 25.0).abs() < 1e-9,
        "VBS mean PAR-2 = {}",
        gap.vbs_mean_par2
    );
    assert_eq!(gap.obligations, 2);
    // Each single engine alone scores ~5010-5015 mean PAR-2, so the gap is large
    // (the engines genuinely complement — the headroom a selector could capture).
    assert!(gap.gap > 4000.0, "gap = {}", gap.gap);
}

#[test]
fn test_weak_areas_worst_first() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    // A clearly-good and a clearly-bad theory so the ordering is deterministic.
    fs::create_dir_all(&dir).expect("mkdir");
    let path = dir.join("attempts.jsonl");
    let mut f = fs::File::create(&path).expect("create");
    let good = format!("blake3:{}", "11".repeat(32));
    let bad = format!("blake3:{}", "22".repeat(32));
    let cert = format!("blake3:{}", "cd".repeat(32));
    // good theory: always solved fast.
    writeln!(
        f,
        "{}",
        row(&good, "clean-smt", "good", "proved", 5, Some(&cert), false)
    )
    .unwrap();
    writeln!(
        f,
        "{}",
        row(&good, "clean-smt", "good", "proved", 6, Some(&cert), false)
    )
    .unwrap();
    // bad theory: always times out.
    writeln!(
        f,
        "{}",
        row(&bad, "clean-smt", "bad", "timeout", 5000, None, false)
    )
    .unwrap();
    writeln!(
        f,
        "{}",
        row(&bad, "clean-smt", "bad", "timeout", 5000, None, false)
    )
    .unwrap();
    drop(f);

    let weak = svc::weak(&[dir], svc::WeakArea::Theory, 5000, 10).expect("weak");
    assert_eq!(weak.len(), 2);
    assert_eq!(weak[0].0, "bad", "worst-PAR-2 theory ranks first");
    assert!(weak[0].1.mean_par2 > weak[1].1.mean_par2);
}

#[test]
fn test_export_dataset_groups_and_filters() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);

    // Full export: one row per attempt, siblings share obligation_digest.
    let out = tmp.path().join("ds.jsonl");
    let n = svc::export_dataset(
        std::slice::from_ref(&dir),
        &svc::DatasetFilter::default(),
        5000,
        &out,
    )
    .expect("export full");
    assert_eq!(n, 4);
    let text = fs::read_to_string(&out).expect("read dataset");
    assert_eq!(text.lines().count(), 4);

    // Engine filter keeps only the two clean-smt rows.
    let out2 = tmp.path().join("ds_smt.jsonl");
    let filter = svc::DatasetFilter {
        engine: Some("clean-smt".to_string()),
        theory: None,
    };
    let n2 = svc::export_dataset(&[dir], &filter, 5000, &out2).expect("export filtered");
    assert_eq!(n2, 2, "engine filter keeps only clean-smt attempts");
}

#[test]
fn test_missing_directory_is_empty_not_error() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let missing = tmp.path().join("no-such-dir");
    let report = svc::stats(&[missing], 5000).expect("missing dir is empty, not an error");
    assert_eq!(report.total_attempts, 0);
}
