// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration test for the Phase-2 solver-results-cache SERVICE surface
//! (`clean_auto::solver_cache_service` transport-agnostic dispatch + ingest).
//!
//! See `designs/2026-06-24-solver-results-cache-service.md` §10. Like the Phase-1
//! test, this lives in `clean-cli` (not `clean-auto`) on purpose: `clean-auto`'s
//! lib *test* binary pulls the trust-cg/trust-ir dev-dependencies, whose
//! linkability is repaired in a parallel session; `clean-cli` depends only on
//! `clean-auto`'s *lib*, so this links regardless and drives the exact public
//! API the `solver_serve` binary uses.
//!
//! What it proves:
//! - the read endpoints (`/healthz`, `/stats`, `/weak`, `/vbs-gap`, `/lookup`,
//!   `/export-dataset`) return the right data with the honest trust note;
//! - `/lookup` serves both the µs `VCIDX01` path and the live-aggregate path;
//! - `POST /ingest` validates + appends a record (+ optional re-checkable proof
//!   blob), and NEVER mints a `verified` badge — the soundness model is a
//!   distribution front-end, not a trust authority.

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use clean_auto::solver_cache_service as svc;
use clean_kernel::{Expr, Level};

/// Two obligations, two complementary engines (the canonical positive-VBS-gap
/// corpus). `aa…`: smt proves fast / oracle times out; `bb…`: the reverse.
fn write_corpus(dir: &Path) {
    fs::create_dir_all(dir).expect("mkdir telemetry dir");
    let oblig_a = format!("blake3:{}", "aa".repeat(32));
    let oblig_b = format!("blake3:{}", "bb".repeat(32));
    let cert = format!("blake3:{}", "cd".repeat(32));
    let rows = [
        row(
            &oblig_a,
            "clean-smt",
            "clean-cic",
            "proved",
            30,
            Some(&cert),
        ),
        row(&oblig_a, "oracle", "oracle", "timeout", 5000, None),
        row(&oblig_b, "clean-smt", "clean-cic", "timeout", 5000, None),
        row(&oblig_b, "oracle", "oracle", "proved", 20, Some(&cert)),
    ];
    let mut f = fs::File::create(dir.join("attempts.jsonl")).expect("create attempts.jsonl");
    for r in &rows {
        writeln!(f, "{r}").expect("write row");
    }
}

/// One `solver-attempt-record-v1` JSON line.
fn row(
    oblig: &str,
    solver: &str,
    theory: &str,
    result: &str,
    wall_ms: u64,
    cert: Option<&str>,
) -> String {
    let success = result == "proved";
    let cert_field = match cert {
        Some(c) => format!(",\"proof_term_digest\":\"{c}\""),
        None => String::new(),
    };
    format!(
        "{{\"schema\":\"solver-attempt-record-v1\",\"obligation_digest\":\"{oblig}\",\
         \"theory_logic\":\"{theory}\",\"solver\":{{\"name\":\"{solver}\",\"version\":\"t\"}},\
         \"strategy\":\"smt→superposition→oracle\",\"result\":\"{result}\",\"wall_ms\":{wall_ms},\
         \"success\":{success}{cert_field},\"cache_outcome\":\"miss\",\
         \"decided_at_epoch_s\":1750000000}}"
    )
}

fn read_only_state(dir: &Path, index: Option<PathBuf>) -> svc::ServeState {
    svc::ServeState::new(vec![dir.to_path_buf()], index, None, None, None, 5000)
        .expect("build read-only serving state")
}

#[test]
fn test_healthz_ok() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let resp = svc::dispatch(&state, "GET", "/healthz", &HashMap::new(), b"");
    assert_eq!(resp.status, 200);
    assert_eq!(resp.body["status"], serde_json::json!("ok"));
}

#[test]
fn test_stats_carries_report_and_trust_note() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let resp = svc::dispatch(&state, "GET", "/stats", &HashMap::new(), b"");
    assert_eq!(resp.status, 200);
    assert_eq!(resp.body["report"]["total_attempts"], serde_json::json!(4));
    assert_eq!(
        resp.body["report"]["distinct_obligations"],
        serde_json::json!(2)
    );
    // The honest trust note + soundness model are on EVERY substantive response.
    assert!(resp.body["trust_note"]
        .as_str()
        .unwrap()
        .contains("not a trust authority"));
    assert!(resp.body["soundness_model"]["raw_verdict"].is_string());
}

#[test]
fn test_vbs_gap_positive_for_complementary_engines() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let resp = svc::dispatch(&state, "GET", "/vbs-gap", &HashMap::new(), b"");
    assert_eq!(resp.status, 200);
    let gap = resp.body["vbs_gap"]["gap"].as_f64().expect("gap f64");
    assert!(
        gap > 4000.0,
        "complementary engines ⇒ large VBS−SBS gap, got {gap}"
    );
}

#[test]
fn test_weak_worst_first() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let mut q = HashMap::new();
    q.insert("by".to_string(), "solver".to_string());
    let resp = svc::dispatch(&state, "GET", "/weak", &q, b"");
    assert_eq!(resp.status, 200);
    assert!(resp.body["classes"].is_array());
}

#[test]
fn test_export_dataset_inline_rows() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let resp = svc::dispatch(&state, "GET", "/export-dataset", &HashMap::new(), b"");
    assert_eq!(resp.status, 200);
    assert_eq!(resp.body["count"], serde_json::json!(4));
    assert_eq!(
        resp.body["schema"],
        serde_json::json!("solver-attempt-dataset-v1")
    );
    assert!(resp.body["rows"].as_array().unwrap().len() == 4);
}

#[test]
fn test_lookup_via_vcidx01_index() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let index = tmp.path().join("solver.vcidx");
    svc::build_index(std::slice::from_ref(&dir), &index).expect("build index");
    let state = read_only_state(&dir, Some(index));

    let aa = format!("blake3:{}", "aa".repeat(32));
    let resp = svc::dispatch(
        &state,
        "GET",
        &format!("/lookup/{aa}"),
        &HashMap::new(),
        b"",
    );
    assert_eq!(resp.status, 200);
    assert_eq!(resp.body["found"], serde_json::json!(true));
    assert_eq!(resp.body["summary"]["attempts"], serde_json::json!(2));
    assert_eq!(resp.body["summary"]["solved"], serde_json::json!(1));
    // No cached proof term ⇒ telemetry-only, not re-checkable.
    assert_eq!(resp.body["re_checkable"], serde_json::json!(false));
    assert_eq!(
        resp.body["verdict_kind"],
        serde_json::json!("telemetry-only")
    );
}

#[test]
fn test_lookup_malformed_digest_400() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None);
    let resp = svc::dispatch(&state, "GET", "/lookup/not-a-digest", &HashMap::new(), b"");
    assert_eq!(resp.status, 400);
}

/// The core soundness assertion: ingest of a proof-bearing record APPENDS the
/// telemetry + stores the re-checkable proof, but NEVER mints `verified`, and a
/// follow-up `/lookup` reflects it as re-checkable PROVENANCE.
#[test]
fn test_ingest_proof_bearing_is_provenance_never_verified() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let tele = tmp.path().join("tele");
    let cache = tmp.path().join("cache");
    fs::create_dir_all(&tele).expect("mkdir tele");
    fs::create_dir_all(&cache).expect("mkdir cache");

    let state = svc::ServeState::new(
        vec![tele.clone(), cache.clone()],
        None,
        Some(tele.clone()),
        Some(cache.clone()),
        None,
        5000,
    )
    .expect("ingest-enabled state");

    // A small, well-formed closed kernel term, encoded for the ingest envelope.
    let term = Expr::sort(Level::zero());
    let hex = svc::encode_proof_hex(&term).expect("encode proof hex");
    let digest = format!("blake3:{}", "11".repeat(32));
    let envelope = serde_json::json!({
        "record": {
            "schema": "solver-attempt-record-v1",
            "obligation_digest": digest,
            "theory_logic": "clean-cic",
            "solver": { "name": "clean-smt", "version": "t" },
            "strategy": "smt→superposition→oracle",
            "result": "proved",
            "wall_ms": 12,
            "success": true,
            "proof_term_digest": format!("blake3:{}", "cd".repeat(32)),
            "decided_at_epoch_s": 1_750_000_000
        },
        "proof_term_hex": hex
    });
    let body = serde_json::to_vec(&envelope).expect("ser envelope");
    let resp = svc::dispatch(&state, "POST", "/ingest", &HashMap::new(), &body);
    assert_eq!(resp.status, 202, "accepted: {:?}", resp.body);
    assert_eq!(
        resp.body["verified"],
        serde_json::json!(false),
        "NEVER mints verified"
    );
    assert_eq!(resp.body["accepted"], serde_json::json!(true));
    assert_eq!(resp.body["proof_stored"], serde_json::json!(true));
    assert_eq!(resp.body["re_checkable"], serde_json::json!(true));
    assert!(resp.body["trust_note"].as_str().unwrap().contains("never"));

    // The record is now durable: a live /lookup reflects it as re-checkable.
    let look = svc::dispatch(
        &state,
        "GET",
        &format!("/lookup/{digest}"),
        &HashMap::new(),
        b"",
    );
    assert_eq!(look.status, 200);
    assert_eq!(look.body["found"], serde_json::json!(true));
    assert_eq!(look.body["summary"]["cached"], serde_json::json!(true));
    assert_eq!(look.body["re_checkable"], serde_json::json!(true));
    assert_eq!(
        look.body["verdict_kind"],
        serde_json::json!("proof-bearing-provenance")
    );
}

#[test]
fn test_ingest_disabled_503() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let dir = tmp.path().join("tele");
    write_corpus(&dir);
    let state = read_only_state(&dir, None); // ingest not enabled
    let resp = svc::dispatch(&state, "POST", "/ingest", &HashMap::new(), b"{}");
    assert_eq!(resp.status, 503);
}

#[test]
fn test_ingest_rejects_malformed_and_misattached_proof() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let tele = tmp.path().join("tele");
    let cache = tmp.path().join("cache");
    let state = svc::ServeState::new(
        vec![tele.clone(), cache.clone()],
        None,
        Some(tele),
        Some(cache),
        None,
        5000,
    )
    .expect("ingest state");

    // (1) Not JSON at all.
    let r = svc::dispatch(&state, "POST", "/ingest", &HashMap::new(), b"not json");
    assert_eq!(r.status, 400);

    // (2) A proof attached to a NON-Proved verdict is rejected (a raw verdict is
    //     telemetry, never a proof).
    let env = serde_json::json!({
        "record": {
            "schema": "solver-attempt-record-v1",
            "obligation_digest": format!("blake3:{}", "22".repeat(32)),
            "theory_logic": "clean-cic",
            "solver": { "name": "clean-smt", "version": "t" },
            "strategy": "s",
            "result": "timeout",
            "wall_ms": 5000,
            "success": false,
            "decided_at_epoch_s": 1_750_000_000
        },
        "proof_term_hex": "00ff"
    });
    let r2 = svc::dispatch(
        &state,
        "POST",
        "/ingest",
        &HashMap::new(),
        &serde_json::to_vec(&env).unwrap(),
    );
    assert_eq!(
        r2.status, 400,
        "proof on a non-Proved verdict must be rejected"
    );

    // (3) A Proved verdict with an undecodable proof blob is rejected (the store
    //     never holds garbage; the consumer's kernel re-check is the arbiter).
    let env2 = serde_json::json!({
        "record": {
            "schema": "solver-attempt-record-v1",
            "obligation_digest": format!("blake3:{}", "33".repeat(32)),
            "theory_logic": "clean-cic",
            "solver": { "name": "clean-smt", "version": "t" },
            "strategy": "s",
            "result": "proved",
            "wall_ms": 1,
            "success": true,
            "decided_at_epoch_s": 1_750_000_000
        },
        "proof_term_hex": "zzzz"
    });
    let r3 = svc::dispatch(
        &state,
        "POST",
        "/ingest",
        &HashMap::new(),
        &serde_json::to_vec(&env2).unwrap(),
    );
    assert_eq!(r3.status, 400, "undecodable proof blob must be rejected");
}
