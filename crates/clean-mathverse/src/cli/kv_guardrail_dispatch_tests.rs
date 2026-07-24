// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavior-parity tests for the KV-guardrail dispatch verbs.
//!
//! Ports the cases from the retired Python suites
//! (`scripts/test_check_kv_ratchet.py`, `scripts/test_check_kv_elision_subset.py`)
//! and adds fingerprint coverage. Hosted in a sibling file (pulled into
//! `kv_guardrail_dispatch.rs` via `#[path]`) so the dispatch module stays under
//! the 500-line cap.

use std::path::Path;

use super::*;
use crate::cli::{
    ElisionGateArgs, FingerprintArgs, MathverseCliError, RatchetCheckArgs, RatchetUpdateArgs,
};
use crate::verify::kernel_verified_manifest::{KernelVerifiedManifest, StampEnvFingerprint};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn write_json(dir: &Path, name: &str, body: &str) -> std::path::PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, body).expect("write fixture json");
    path
}

fn write_summary(dir: &Path, kv: i64, stored: i64, heuristic: i64) -> std::path::PathBuf {
    write_json(
        dir,
        "summary.json",
        &format!(
            "{{\"kernel_verified\": {kv}, \"stored_kernel_verified\": {stored}, \
             \"heuristic_kernel_verified\": {heuristic}, \"unrelated\": \"ignored\"}}"
        ),
    )
}

fn write_ratchet(dir: &Path, kv_base: i64, stored_base: i64, notes: &str) -> std::path::PathBuf {
    write_json(
        dir,
        "ratchet.json",
        &format!(
            "{{\"last_updated\": \"2026-01-01\", \"kernel_verified_baseline\": {kv_base}, \
             \"stored_kernel_verified_baseline\": {stored_base}, \"notes\": \"{notes}\"}}"
        ),
    )
}

fn manifest_with_names(names: &[&str]) -> KernelVerifiedManifest {
    KernelVerifiedManifest::from_worker_parts(
        "test-module",
        names.len(),
        0,
        0,
        0.0,
        names.iter().map(|s| (*s).to_owned()).collect(),
    )
}

fn write_manifest(dir: &Path, name: &str, names: &[&str]) -> std::path::PathBuf {
    let m = manifest_with_names(names);
    let path = dir.join(name);
    m.write_to_file(&path).expect("write manifest");
    path
}

fn check_args(summary: &Path, ratchet: &Path) -> RatchetCheckArgs {
    RatchetCheckArgs {
        summary: summary.to_path_buf(),
        ratchet: ratchet.to_path_buf(),
        json: false,
    }
}

fn update_args(summary: &Path, ratchet: &Path) -> RatchetUpdateArgs {
    RatchetUpdateArgs {
        summary: summary.to_path_buf(),
        ratchet: ratchet.to_path_buf(),
        json: false,
    }
}

// ---------------------------------------------------------------------------
// ratchet check (ports test_check_kv_ratchet.py)
// ---------------------------------------------------------------------------

#[test]
fn test_ratchet_check_absent_summary_skips_green() {
    // do_check: missing summary -> SKIP, exit 0 (Ok). Load-bearing for the local
    // gate's green-on-absent contract.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = dir.path().join("does-not-exist.json");
    let ratchet = write_ratchet(dir.path(), 100, 100, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(res.is_ok(), "absent summary must SKIP green, got {res:?}");
}

#[test]
fn test_ratchet_check_floor_breach_fails() {
    // soundness_floor_ok: heuristic_kernel_verified != 0 -> fail closed.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 100, 100, 3);
    let ratchet = write_ratchet(dir.path(), 0, 0, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetSoundnessFloor(3))),
        "heuristic != 0 must breach the soundness floor, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_malformed_summary_fails_closed() {
    // extract_kv_counts: a missing integer field raises -> FAIL (never default-pass).
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_json(
        dir.path(),
        "summary.json",
        "{\"kernel_verified\": 5, \"heuristic_kernel_verified\": 0}",
    );
    let ratchet = write_ratchet(dir.path(), 0, 0, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetMalformedSummary(_))),
        "missing stored_kernel_verified must fail closed, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_bool_field_fails_closed() {
    // bool-is-not-int parity: JSON `true` deserializes into i64 as an ERROR.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_json(
        dir.path(),
        "summary.json",
        "{\"kernel_verified\": true, \"stored_kernel_verified\": 1, \
         \"heuristic_kernel_verified\": 0}",
    );
    let ratchet = write_ratchet(dir.path(), 0, 0, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetMalformedSummary(_))),
        "a bool in an int field must fail closed, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_regression_fails() {
    // compare: cur < baseline -> violation naming the regressed key.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 90, 100, 0);
    let ratchet = write_ratchet(dir.path(), 100, 100, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    match res {
        Err(MathverseCliError::RatchetRegressed(violations)) => {
            assert_eq!(violations.len(), 1, "exactly kernel_verified regressed");
            assert!(
                violations[0].contains("kernel_verified"),
                "violation names the key: {}",
                violations[0]
            );
        }
        other => panic!("expected RatchetRegressed, got {other:?}"),
    }
}

#[test]
fn test_ratchet_check_equal_and_progress_pass() {
    // compare: equal and above-baseline both pass.
    let dir = tempfile::tempdir().expect("tmp");
    let ratchet = write_ratchet(dir.path(), 100, 100, "n");

    let equal = write_summary(dir.path(), 100, 100, 0);
    assert!(
        cmd_ratchet_check(check_args(&equal, &ratchet)).is_ok(),
        "equal to baseline must pass"
    );

    let progress = write_summary(dir.path(), 150, 175, 0);
    assert!(
        cmd_ratchet_check(check_args(&progress, &ratchet)).is_ok(),
        "above baseline must pass"
    );
}

#[test]
fn test_ratchet_check_identity_floor_zero_baseline_always_green() {
    // test_identity_floor_zero_baseline_always_green: 0 baseline, 0 counts -> green.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 0, 0, 0);
    let ratchet = write_ratchet(dir.path(), 0, 0, "n");
    assert!(
        cmd_ratchet_check(check_args(&summary, &ratchet)).is_ok(),
        "identity floor must always be green"
    );
}

#[test]
fn test_ratchet_check_missing_ratchet_file_uses_zero_baseline() {
    // No ratchet file on disk -> default all-zero identity baseline -> any real
    // count is >= 0, so green.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 42, 42, 0);
    let ratchet = dir.path().join("no-ratchet.json");
    assert!(
        cmd_ratchet_check(check_args(&summary, &ratchet)).is_ok(),
        "absent ratchet file must default to a green identity floor"
    );
}

// ---------------------------------------------------------------------------
// ratchet update
// ---------------------------------------------------------------------------

#[test]
fn test_ratchet_update_absent_summary_fails() {
    // do_update: absent summary -> FAIL (not skip).
    let dir = tempfile::tempdir().expect("tmp");
    let summary = dir.path().join("missing.json");
    let ratchet = dir.path().join("ratchet.json");
    let res = cmd_ratchet_update(update_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetUpdateNoSummary(_))),
        "update with no summary must fail, got {res:?}"
    );
}

#[test]
fn test_ratchet_update_floor_breach_refuses() {
    // Shared floor: update must also refuse a floor-breaching summary so it can't
    // ratchet an unsound run.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 100, 100, 1);
    let ratchet = dir.path().join("ratchet.json");
    let res = cmd_ratchet_update(update_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetSoundnessFloor(1))),
        "update must enforce the soundness floor, got {res:?}"
    );
}

#[test]
fn test_ratchet_update_writes_date_only_and_preserves_notes() {
    // write_ratchet: last_updated is DATE-ONLY (YYYY-MM-DD), existing notes round-trip.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 123, 456, 0);
    let ratchet = write_ratchet(dir.path(), 0, 0, "operator prose to keep");

    cmd_ratchet_update(update_args(&summary, &ratchet)).expect("update should succeed");

    let written = std::fs::read_to_string(&ratchet).expect("read back");
    let parsed: serde_json::Value = serde_json::from_str(&written).expect("parse back");
    assert_eq!(parsed["kernel_verified_baseline"], 123);
    assert_eq!(parsed["stored_kernel_verified_baseline"], 456);
    assert_eq!(
        parsed["notes"], "operator prose to keep",
        "existing operator notes must be preserved"
    );
    let last_updated = parsed["last_updated"]
        .as_str()
        .expect("last_updated string");
    assert_eq!(
        last_updated.len(),
        10,
        "last_updated must be date-only (YYYY-MM-DD), got `{last_updated}`"
    );
}

#[test]
fn test_ratchet_update_default_notes_when_absent() {
    // No existing ratchet file -> default BASELINE_NOTES written.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 1, 2, 0);
    let ratchet = dir.path().join("fresh-ratchet.json");

    cmd_ratchet_update(update_args(&summary, &ratchet)).expect("update should succeed");

    let written = std::fs::read_to_string(&ratchet).expect("read back");
    let parsed: serde_json::Value = serde_json::from_str(&written).expect("parse back");
    let notes = parsed["notes"].as_str().expect("notes string");
    assert!(
        notes.contains("Monotonic-UP floor"),
        "default baseline notes must be written, got `{notes}`"
    );
}

// ---------------------------------------------------------------------------
// elision-gate (ports test_check_kv_elision_subset.py)
// ---------------------------------------------------------------------------

fn elision_args(opaque: &Path, oat: &Path) -> ElisionGateArgs {
    ElisionGateArgs {
        opaque_manifest: opaque.to_path_buf(),
        opaque_and_theorem_manifest: oat.to_path_buf(),
        json: false,
    }
}

#[test]
fn test_elision_gate_subset_ok() {
    // opaque-and-theorem is a strict superset -> sound direction -> Ok.
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a"]);
    let oat = write_manifest(dir.path(), "oat.json", &["a", "b", "c"]);
    assert!(
        cmd_elision_gate(elision_args(&opaque, &oat)).is_ok(),
        "opaque subset of opaque-and-theorem must pass"
    );
}

#[test]
fn test_elision_gate_equal_sets_pass() {
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a", "b"]);
    let oat = write_manifest(dir.path(), "oat.json", &["a", "b"]);
    assert!(cmd_elision_gate(elision_args(&opaque, &oat)).is_ok());
}

#[test]
fn test_elision_gate_empty_opaque_passes() {
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &[]);
    let oat = write_manifest(dir.path(), "oat.json", &["a"]);
    assert!(cmd_elision_gate(elision_args(&opaque, &oat)).is_ok());
}

#[test]
fn test_elision_gate_dropped_fails() {
    // opaque verified "b" but opaque-and-theorem dropped it -> unsound -> FAIL.
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a", "b"]);
    let oat = write_manifest(dir.path(), "oat.json", &["a", "c"]);
    match cmd_elision_gate(elision_args(&opaque, &oat)) {
        Err(MathverseCliError::ElisionDropped(dropped)) => {
            assert_eq!(dropped, vec!["b".to_string()], "names the dropped constant");
        }
        other => panic!("expected ElisionDropped, got {other:?}"),
    }
}

#[test]
fn test_elision_gate_dropped_names_are_sorted() {
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["z", "a", "m"]);
    let oat = write_manifest(dir.path(), "oat.json", &[]);
    match cmd_elision_gate(elision_args(&opaque, &oat)) {
        Err(MathverseCliError::ElisionDropped(dropped)) => {
            assert_eq!(
                dropped,
                vec!["a", "m", "z"],
                "dropped names sorted (BTreeSet)"
            );
        }
        other => panic!("expected ElisionDropped, got {other:?}"),
    }
}

#[test]
fn test_elision_gate_missing_file_fails_closed() {
    // from_file on a nonexistent path -> Err (fail-closed via Mathverse #[from]).
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a"]);
    let missing = dir.path().join("nope.json");
    let res = cmd_elision_gate(elision_args(&opaque, &missing));
    assert!(
        res.is_err(),
        "a missing manifest must fail closed, got {res:?}"
    );
}

#[test]
fn test_elision_gate_bad_shape_fails_closed() {
    // Manifest JSON missing kernel_verified_names -> deserialize error -> Err.
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a"]);
    let bad = write_json(dir.path(), "bad.json", "{\"schema_version\": 1}");
    let res = cmd_elision_gate(elision_args(&opaque, &bad));
    assert!(
        res.is_err(),
        "a manifest with the wrong shape must fail closed, got {res:?}"
    );
}

// ---------------------------------------------------------------------------
// fingerprint
// ---------------------------------------------------------------------------

fn sample_fingerprint() -> StampEnvFingerprint {
    StampEnvFingerprint {
        kernel_version: "1.2.3".into(),
        toolchain: "rustc 1.90.0".into(),
        heartbeat: "default".into(),
        elision_policy: "opaque".into(),
        max_closure_modules: 1500,
        prelude_variant: "closure-root".into(),
    }
}

fn write_manifest_with_fingerprint(
    dir: &Path,
    name: &str,
    fp: Option<StampEnvFingerprint>,
) -> std::path::PathBuf {
    let mut m = manifest_with_names(&["x"]);
    m.env_fingerprint = fp;
    let path = dir.join(name);
    m.write_to_file(&path).expect("write manifest");
    path
}

#[test]
fn test_fingerprint_prints_json() {
    let dir = tempfile::tempdir().expect("tmp");
    let fp = sample_fingerprint();
    let path = write_manifest_with_fingerprint(dir.path(), "m.json", Some(fp.clone()));
    let args = FingerprintArgs {
        manifest: path,
        json: true,
    };
    cmd_fingerprint(args).expect("fingerprint with env should succeed (json)");
}

#[test]
fn test_fingerprint_human_lines_ok() {
    let dir = tempfile::tempdir().expect("tmp");
    let path = write_manifest_with_fingerprint(dir.path(), "m.json", Some(sample_fingerprint()));
    let args = FingerprintArgs {
        manifest: path,
        json: false,
    };
    cmd_fingerprint(args).expect("fingerprint with env should succeed (human)");
}

#[test]
fn test_fingerprint_missing_field_fails() {
    // Legacy manifest with env_fingerprint=None -> Err MissingEnvFingerprint.
    let dir = tempfile::tempdir().expect("tmp");
    let path = write_manifest_with_fingerprint(dir.path(), "m.json", None);
    let args = FingerprintArgs {
        manifest: path,
        json: false,
    };
    let res = cmd_fingerprint(args);
    assert!(
        matches!(res, Err(MathverseCliError::MissingEnvFingerprint(_))),
        "a manifest without env_fingerprint must fail, got {res:?}"
    );
}

#[test]
fn test_fingerprint_missing_file_fails() {
    let dir = tempfile::tempdir().expect("tmp");
    let args = FingerprintArgs {
        manifest: dir.path().join("nope.json"),
        json: false,
    };
    let res = cmd_fingerprint(args);
    assert!(
        res.is_err(),
        "a missing manifest file must fail, got {res:?}"
    );
}
