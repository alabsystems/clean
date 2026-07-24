// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the flip-gate registry: parse/roundtrip, drift detection,
//! and the missing-slice fail-soft path. The full add→check end-to-end (which
//! drives the real stream-verify driver) lives in
//! `tests/isabelle_flip_gate_e2e.rs`.

use super::*;

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("isa_flip_gate_{}_{}", tag, std::process::id()));
    std::fs::create_dir_all(&dir).expect("mk scratch dir");
    dir
}

fn sample_gate(slice: &str, pin: &SlicePin) -> FlipGate {
    FlipGate {
        serial: 83_088,
        name: "HOL.eq_ac".to_string(),
        description: "eq_ac — genuinely flips".to_string(),
        slice: slice.to_string(),
        expected: EXPECTED_KERNEL_VERIFIED.to_string(),
        blake3: pin.blake3.clone(),
        lines: pin.lines,
        added: "2026-07-17".to_string(),
        round: "flip-gate-bootstrap".to_string(),
    }
}

#[test]
fn test_registry_roundtrip_preserves_and_sorts_gates() {
    let dir = scratch("roundtrip");
    let reg_path = dir.join("isabelle_flip_gates.json");

    // Two gates deliberately out of serial order — save must sort them.
    // `Default` already carries the current schema version.
    let mut reg = FlipGateRegistry::default();
    reg.gates.push(FlipGate {
        serial: 200,
        name: "b".to_string(),
        description: "second".to_string(),
        slice: "~/isabelle-work/corpora/flip_gates/s200.jsonl".to_string(),
        expected: EXPECTED_KERNEL_VERIFIED.to_string(),
        blake3: "deadbeef".to_string(),
        lines: 3,
        added: "2026-07-17".to_string(),
        round: "r2".to_string(),
    });
    reg.gates.push(FlipGate {
        serial: 100,
        name: "a".to_string(),
        description: "first".to_string(),
        slice: "~/isabelle-work/corpora/flip_gates/s100.jsonl".to_string(),
        expected: EXPECTED_KERNEL_VERIFIED.to_string(),
        blake3: "cafe".to_string(),
        lines: 7,
        added: "2026-07-17".to_string(),
        round: "r1".to_string(),
    });

    reg.save(&reg_path).expect("save registry");
    let loaded = FlipGateRegistry::load(&reg_path).expect("load registry");

    assert_eq!(loaded.version, 1);
    assert_eq!(loaded.gates.len(), 2);
    // Saved serial-ascending.
    assert_eq!(loaded.gates[0].serial, 100, "gates saved serial-ascending");
    assert_eq!(loaded.gates[1].serial, 200);
    assert_eq!(loaded.gate(200).map(|g| g.name.as_str()), Some("b"));
    assert_eq!(loaded.gate(999), None);

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_load_missing_registry_is_empty_not_error() {
    let dir = scratch("missing_reg");
    let reg_path = dir.join("does_not_exist.json");
    let reg =
        FlipGateRegistry::load(&reg_path).expect("missing registry loads empty, never errors");
    assert!(reg.gates.is_empty(), "missing registry yields no gates");
    assert_eq!(reg.version, 1, "empty registry carries the default version");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_parse_literal_registry_json() {
    let json = r#"{
      "version": 1,
      "gates": [
        {
          "serial": 83088,
          "name": "HOL.eq_ac",
          "description": "eq_ac flip",
          "slice": "~/isabelle-work/corpora/flip_gates/s83088.jsonl",
          "expected": "KernelVerified",
          "blake3": "abc123",
          "lines": 42,
          "added": "2026-07-17",
          "round": "bootstrap"
        }
      ]
    }"#;
    let reg: FlipGateRegistry = serde_json::from_str(json).expect("parse literal registry");
    assert_eq!(reg.gates.len(), 1);
    let g = &reg.gates[0];
    assert_eq!(g.serial, 83_088);
    assert_eq!(g.expected, EXPECTED_KERNEL_VERIFIED);
    assert_eq!(g.lines, 42);
}

#[test]
fn test_compute_pin_matches_blake3_and_counts_newlines() {
    let dir = scratch("pin");
    let slice = dir.join("s.jsonl");
    let content = b"line one\nline two\nline three\n";
    std::fs::write(&slice, content).expect("write slice");

    let pin = compute_pin(&slice).expect("compute pin");
    assert_eq!(pin.lines, 3, "three newline-terminated lines");
    assert_eq!(
        pin.blake3,
        blake3::hash(content).to_hex().to_string(),
        "pin blake3 matches a direct hash of the exact bytes"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_drift_detected_when_slice_changes_after_pinning() {
    let dir = scratch("drift");
    let slice = dir.join("s83088.jsonl");
    std::fs::write(&slice, b"original\ncontent\n").expect("write slice");
    let pin = compute_pin(&slice).expect("pin");
    let gate = sample_gate(slice.to_str().expect("utf8 path"), &pin);

    // Mutate the slice out from under the pinned expectation.
    std::fs::write(&slice, b"original\ncontent\nTAMPERED\n").expect("tamper slice");

    let outcome = evaluate_gate(&gate).expect("evaluate never errors on drift");
    match &outcome {
        GateOutcome::Drift { expected, actual } => {
            assert_eq!(expected.lines, 2, "pinned line count");
            assert_eq!(actual.lines, 3, "on-disk line count after tamper");
            assert_ne!(expected.blake3, actual.blake3, "digests differ on drift");
        }
        other => panic!("expected Drift, got {other:?}"),
    }
    assert!(!outcome.is_pass());
    assert!(
        outcome.describe().contains("DRIFT"),
        "drift message is loud: {}",
        outcome.describe()
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_drift_detected_on_wrong_pinned_hash() {
    let dir = scratch("drift_hash");
    let slice = dir.join("s83088.jsonl");
    std::fs::write(&slice, b"exact\nbytes\n").expect("write slice");
    let mut gate = sample_gate(
        slice.to_str().expect("utf8 path"),
        &compute_pin(&slice).expect("pin"),
    );
    // A registry whose pinned hash disagrees with the on-disk slice.
    gate.blake3 = "0000000000000000000000000000000000000000000000000000000000000000".to_string();

    match evaluate_gate(&gate).expect("evaluate") {
        GateOutcome::Drift { .. } => {}
        other => panic!("expected Drift on hash mismatch, got {other:?}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_missing_slice_file_fails_soft_not_crash() {
    let dir = scratch("missing_slice");
    let slice = dir.join("never_created.jsonl");
    let gate = sample_gate(
        slice.to_str().expect("utf8 path"),
        &SlicePin {
            blake3: "abc".to_string(),
            lines: 1,
        },
    );
    let outcome = evaluate_gate(&gate).expect("missing slice returns an outcome, never errors");
    match &outcome {
        GateOutcome::MissingSlice(p) => assert_eq!(p, &slice),
        other => panic!("expected MissingSlice, got {other:?}"),
    }
    assert!(outcome.describe().contains("MISSING SLICE"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_unsupported_expected_verdict() {
    let dir = scratch("unsupported");
    let slice = dir.join("s.jsonl");
    std::fs::write(&slice, b"x\n").expect("write");
    let mut gate = sample_gate(
        slice.to_str().expect("utf8 path"),
        &compute_pin(&slice).expect("pin"),
    );
    gate.expected = "KernelBridged".to_string();
    match evaluate_gate(&gate).expect("evaluate") {
        GateOutcome::UnsupportedExpected(v) => assert_eq!(v, "KernelBridged"),
        other => panic!("expected UnsupportedExpected, got {other:?}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_sanitize_name_and_slice_file_name() {
    assert_eq!(sanitize_name("HOL.eq_ac"), "HOL.eq_ac");
    assert_eq!(sanitize_name("Foo/Bar Baz"), "Foo_Bar_Baz");
    assert_eq!(sanitize_name(""), "");
    assert_eq!(
        slice_file_name(83_088, "HOL.eq_ac"),
        "s83088_HOL.eq_ac.jsonl"
    );
    assert_eq!(slice_file_name(42, ""), "s42.jsonl");
    // Non-ascii / long names collapse and truncate without panicking.
    let long = "x".repeat(200);
    assert!(sanitize_name(&long).len() <= 60);
}

#[test]
fn test_to_portable_rewrites_home_prefix() {
    if let Some(home) = std::env::var_os("HOME") {
        let home = PathBuf::from(home);
        let p = home.join("isabelle-work/corpora/flip_gates/s1.jsonl");
        assert_eq!(
            to_portable(&p),
            "~/isabelle-work/corpora/flip_gates/s1.jsonl"
        );
    }
    // A path outside HOME is returned verbatim.
    assert_eq!(
        to_portable(Path::new("/opt/data/s1.jsonl")),
        "/opt/data/s1.jsonl"
    );
}

#[test]
fn test_ymd_from_epoch_known_dates() {
    assert_eq!(ymd_from_epoch(0), "1970-01-01");
    assert_eq!(ymd_from_epoch(1_782_286_542), "2026-06-24");
    // Leap day.
    assert_eq!(ymd_from_epoch(1_709_209_096), "2024-02-29");
}
