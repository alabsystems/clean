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
use crate::verify::kernel_verified_manifest::{test_run, Elision, KernelVerifiedManifest};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn write_json(dir: &Path, name: &str, body: &str) -> std::path::PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, body).expect("write fixture json");
    path
}

fn write_summary(dir: &Path, accepted: i64, stored: i64, heuristic: i64) -> std::path::PathBuf {
    write_json(
        dir,
        "summary.json",
        &format!(
            "{{\"tier\": \"development\", \"accepted\": {accepted}, \
             \"stored_reference_stamped\": {stored}, \
             \"heuristic_kernel_verified\": {heuristic}, \"unrelated\": \"ignored\"}}"
        ),
    )
}

/// A P6 ratchet file; `reference` is the reference-stamp baseline (`None`:
/// unarmed).
fn write_ratchet(
    dir: &Path,
    accepted_base: i64,
    reference: Option<i64>,
    notes: &str,
) -> std::path::PathBuf {
    let reference = reference.map_or_else(|| "null".to_string(), |b| b.to_string());
    write_json(
        dir,
        "ratchet.json",
        &format!(
            "{{\"last_updated\": \"2026-01-01\", \"development_accepted_baseline\": \
             {accepted_base}, \"reference_stamped_baseline\": {reference}, \
             \"notes\": \"{notes}\"}}"
        ),
    )
}

fn manifest_with_names(names: &[&str], elision: Elision) -> KernelVerifiedManifest {
    KernelVerifiedManifest::from_sharded_worker(
        "test-module",
        names.len(),
        0,
        0,
        0.0,
        names.iter().map(|s| (*s).to_owned()).collect(),
        test_run(elision),
    )
}

fn write_manifest(dir: &Path, name: &str, names: &[&str]) -> std::path::PathBuf {
    let elision = if name.starts_with("opaque") {
        Elision::Opaque
    } else {
        Elision::OpaqueAndTheorem
    };
    let m = manifest_with_names(names, elision);
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
    let ratchet = write_ratchet(dir.path(), 100, None, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(res.is_ok(), "absent summary must SKIP green, got {res:?}");
}

#[test]
fn test_ratchet_check_floor_breach_fails() {
    // soundness_floor_ok: heuristic_kernel_verified != 0 -> fail closed.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 100, 100, 3);
    let ratchet = write_ratchet(dir.path(), 0, None, "n");
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
        "{\"tier\": \"development\", \"accepted\": 5, \"heuristic_kernel_verified\": 0}",
    );
    let ratchet = write_ratchet(dir.path(), 0, None, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetMalformedSummary(_))),
        "missing stored_reference_stamped must fail closed, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_bool_field_fails_closed() {
    // bool-is-not-int parity: JSON `true` deserializes into i64 as an ERROR.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_json(
        dir.path(),
        "summary.json",
        "{\"tier\": \"development\", \"accepted\": true, \
         \"stored_reference_stamped\": 0, \"heuristic_kernel_verified\": 0}",
    );
    let ratchet = write_ratchet(dir.path(), 0, None, "n");
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
    let summary = write_summary(dir.path(), 90, 0, 0);
    let ratchet = write_ratchet(dir.path(), 100, None, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    match res {
        Err(MathverseCliError::RatchetRegressed(violations)) => {
            assert_eq!(violations.len(), 1, "exactly accepted regressed");
            assert!(
                violations[0].contains("accepted"),
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
    let ratchet = write_ratchet(dir.path(), 100, None, "n");

    let equal = write_summary(dir.path(), 100, 0, 0);
    assert!(
        cmd_ratchet_check(check_args(&equal, &ratchet)).is_ok(),
        "equal to baseline must pass"
    );

    let progress = write_summary(dir.path(), 150, 0, 0);
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
    let ratchet = write_ratchet(dir.path(), 0, None, "n");
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
    let summary = write_summary(dir.path(), 42, 0, 0);
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
    let summary = write_summary(dir.path(), 123, 0, 0);
    let ratchet = write_ratchet(dir.path(), 0, None, "operator prose to keep");

    cmd_ratchet_update(update_args(&summary, &ratchet)).expect("update should succeed");

    let written = std::fs::read_to_string(&ratchet).expect("read back");
    let parsed: serde_json::Value = serde_json::from_str(&written).expect("parse back");
    assert_eq!(parsed["development_accepted_baseline"], 123);
    assert_eq!(
        parsed["reference_stamped_baseline"],
        serde_json::Value::Null
    );
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
    let summary = write_summary(dir.path(), 1, 0, 0);
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
// P6 controls: the split ratchet, the elision gate's identity check
// ---------------------------------------------------------------------------

#[test]
fn test_ratchet_check_pre_p6_summary_refused() {
    // A summary written before P6 (`kernel_verified`, no `tier`) is refused,
    // never read as accepted 0.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_json(
        dir.path(),
        "summary.json",
        "{\"kernel_verified\": 686, \"stored_kernel_verified\": 686, \
         \"heuristic_kernel_verified\": 0}",
    );
    let ratchet = write_ratchet(dir.path(), 0, None, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetMalformedSummary(_))),
        "a pre-P6 summary must fail closed, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_pre_p6_baseline_refused() {
    // A pre-P6 ratchet file read through defaults would be a zero floor: refused.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 686, 0, 0);
    let ratchet = write_json(
        dir.path(),
        "ratchet.json",
        "{\"last_updated\": \"2026-10-07\", \"kernel_verified_baseline\": 686, \
         \"stored_kernel_verified_baseline\": 686, \"notes\": \"n\"}",
    );
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetMalformedBaseline(_))),
        "a pre-P6 baseline must fail closed, got {res:?}"
    );
}

#[test]
fn test_ratchet_check_stamp_without_reference_producer_fails() {
    // While the reference-stamp baseline is unarmed, a development run that
    // left any KernelVerified header is a violation, in check and in update.
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 686, 1, 0);
    let ratchet = write_ratchet(dir.path(), 686, None, "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(&res, Err(MathverseCliError::RatchetRegressed(v)) if v[0].contains("no reference producer")),
        "got {res:?}"
    );
    let res = cmd_ratchet_update(update_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetRegressed(_))),
        "got {res:?}"
    );
}

#[test]
fn test_ratchet_check_armed_reference_baseline_regression_fails() {
    let dir = tempfile::tempdir().expect("tmp");
    let summary = write_summary(dir.path(), 686, 5, 0);
    let ratchet = write_ratchet(dir.path(), 686, Some(6), "n");
    let res = cmd_ratchet_check(check_args(&summary, &ratchet));
    assert!(
        matches!(res, Err(MathverseCliError::RatchetRegressed(_))),
        "got {res:?}"
    );
}

#[test]
fn test_elision_gate_wrong_elision_pair_refused() {
    let dir = tempfile::tempdir().expect("tmp");
    let a = dir.path().join("a.json");
    let b = dir.path().join("b.json");
    manifest_with_names(&["a"], Elision::Opaque)
        .write_to_file(&a)
        .expect("write");
    manifest_with_names(&["a"], Elision::Opaque)
        .write_to_file(&b)
        .expect("write");
    let res = cmd_elision_gate(elision_args(&a, &b));
    assert!(
        matches!(res, Err(MathverseCliError::Manifest(_))),
        "got {res:?}"
    );
}

#[test]
fn test_elision_gate_different_checkers_refused() {
    // Same elision pair, but the two runs are not the same checker (another
    // kernel theory): a subset across two theories says nothing about elision.
    let dir = tempfile::tempdir().expect("tmp");
    let opaque = write_manifest(dir.path(), "opaque.json", &["a"]);
    let mut env = clean_kernel::Environment::for_lean_replay();
    env.set_kernel_theory(clean_kernel::env::KernelTheory::Extended);
    let run = crate::verify::kernel_verified_manifest::test_run_in(
        &env,
        crate::verify::kernel_verified_manifest::BaseVariant::LeanReplay,
        Elision::OpaqueAndTheorem,
    );
    let oat = dir.path().join("oat.json");
    KernelVerifiedManifest::from_sharded_worker("m", 1, 0, 0, 0.0, vec!["a".into()], run)
        .write_to_file(&oat)
        .expect("write");
    let res = cmd_elision_gate(elision_args(&opaque, &oat));
    assert!(
        matches!(res, Err(MathverseCliError::Manifest(_))),
        "got {res:?}"
    );
}

// ---------------------------------------------------------------------------
// fingerprint
// ---------------------------------------------------------------------------

#[test]
fn test_fingerprint_prints_identity_json_and_human() {
    let dir = tempfile::tempdir().expect("tmp");
    let path = write_manifest(dir.path(), "m.json", &["x"]);
    for json in [true, false] {
        cmd_fingerprint(FingerprintArgs {
            manifest: path.clone(),
            json,
        })
        .expect("a manifest always carries its identity");
    }
}

#[test]
fn test_fingerprint_schema1_manifest_refused() {
    let dir = tempfile::tempdir().expect("tmp");
    let path = write_json(
        dir.path(),
        "m.json",
        "{\"schema_version\": 1, \"kernel_verified_names\": [\"x\"]}",
    );
    let res = cmd_fingerprint(FingerprintArgs {
        manifest: path,
        json: false,
    });
    assert!(
        matches!(res, Err(MathverseCliError::Mathverse(_))),
        "a manifest without an identity must fail, got {res:?}"
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
