// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end FLIP-GATE test at fixture scale.
//!
//! Drives the whole flip-gate flow — build a closure slice for a target serial,
//! replay it through the REAL library stream-verify driver, pin it, register it,
//! then `--check`-style re-evaluate it — over a tiny committed fixture corpus
//! (`tests/fixtures/isabelle/flip_gate_mini_corpus.jsonl`), NOT the real 51 GB
//! corpus. The fixture holds two `HOL.refl`-backed reflexivity theorems (serials
//! 100/101, which KernelVerify) and one oracle-hole theorem (serial 102, which
//! must be rejected), so it exercises both a genuine flip and a non-flip through
//! the exact routing a grand uses.

use std::path::PathBuf;

use clean_mathverse::hol::isabelle_flip_gate::{
    build_and_pin_gate, evaluate_gate, FlipGateError, FlipGateRegistry, GateOutcome,
    EXPECTED_KERNEL_VERIFIED,
};

fn fixture_corpus() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/isabelle/flip_gate_mini_corpus.jsonl")
}

#[test]
fn flip_gate_add_check_end_to_end() {
    let corpus = fixture_corpus();
    let work = tempfile::tempdir().expect("tempdir");
    let gates_dir = work.path().join("flip_gates");
    let registry_path = work.path().join("isabelle_flip_gates.json");

    let mut registry = FlipGateRegistry::default();

    // --- ADD: serial 100 genuinely flips (Demo.a_eq_a via HOL.refl) ---
    let gate = build_and_pin_gate(
        &registry,
        &corpus,
        100,
        &gates_dir,
        "reflexivity flip (fixture)",
        "fixture-round",
    )
    .expect("serial 100 must KernelVerify and register");

    assert_eq!(gate.serial, 100);
    assert_eq!(
        gate.name, "Demo.a_eq_a",
        "name comes from the verify driver"
    );
    assert_eq!(gate.expected, EXPECTED_KERNEL_VERIFIED);
    assert!(gate.lines >= 1, "the slice has at least the seed line");
    assert!(!gate.blake3.is_empty(), "the slice is pinned by blake3");
    assert!(!gate.added.is_empty(), "the add date is recorded");
    assert_eq!(gate.round, "fixture-round");

    // The durable slice file exists on disk under the gates dir.
    let slice_on_disk =
        clean_mathverse::hol::isabelle_sessions::expand_tilde(std::path::Path::new(&gate.slice));
    assert!(
        slice_on_disk.exists(),
        "durable slice must be written: {}",
        slice_on_disk.display()
    );

    // --- REGISTER + roundtrip through the committed-registry JSON ---
    registry.gates.push(gate.clone());
    registry.save(&registry_path).expect("save registry");
    let reloaded = FlipGateRegistry::load(&registry_path).expect("reload registry");
    assert_eq!(reloaded.gates.len(), 1);
    assert_eq!(reloaded.gate(100), Some(&gate));

    // --- CHECK: the registered gate re-evaluates to PASS ---
    let outcome = evaluate_gate(&gate).expect("evaluate registered gate");
    assert_eq!(
        outcome,
        GateOutcome::Pass,
        "the pinned slice must replay to KernelVerified, got {}",
        outcome.describe()
    );

    // --- DRIFT: mutate the durable slice; the gate must fail loud, not replay ---
    {
        use std::io::Write as _;
        let mut f = std::fs::OpenOptions::new()
            .append(true)
            .open(&slice_on_disk)
            .expect("open slice to tamper");
        writeln!(f, "{{\"tampered\":true}}").expect("append tamper line");
    }
    match evaluate_gate(&gate).expect("evaluate after tamper") {
        GateOutcome::Drift { expected, actual } => {
            assert_ne!(expected.blake3, actual.blake3, "drift changes the digest");
        }
        other => panic!("expected Drift after tampering the slice, got {other:?}"),
    }

    // --- NON-FLIP: serial 102 is an oracle hole; --add must refuse it ---
    match build_and_pin_gate(
        &registry,
        &corpus,
        102,
        &gates_dir,
        "oracle hole (must not register)",
        "fixture-round",
    ) {
        Err(FlipGateError::NotAFlip { serial, reasons }) => {
            assert_eq!(serial, 102);
            assert!(
                reasons.contains("hole"),
                "the non-flip reports the honest reject bucket: {reasons}"
            );
        }
        other => panic!("expected NotAFlip for the oracle hole, got {other:?}"),
    }
    // And it left no durable slice behind.
    assert!(
        !gates_dir.join("s102.jsonl").exists(),
        "a non-flip must not leave a slice behind"
    );

    // --- DUPLICATE: re-adding an already-registered serial is refused ---
    match build_and_pin_gate(&registry, &corpus, 100, &gates_dir, "dup", "fixture-round") {
        Err(FlipGateError::AlreadyRegistered(100)) => {}
        other => panic!("expected AlreadyRegistered(100), got {other:?}"),
    }
}
