// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the actual packaged CLI's independent Alethe checker, not just
//! feature metadata or command registration. The release gate enables the
//! same `clean/carcara-verify` feature as aterm's package recipe.
#![cfg(feature = "carcara-verify")]

use std::process::Command;

fn check(proof: &str) -> std::process::Output {
    let directory = tempfile::tempdir().unwrap();
    let certificate = directory.path().join("certificate.json");
    // The fixtures below contain no JSON-special characters; newline escapes
    // are already encoded in each literal.
    let json = format!(
        r#"{{"type":"alethe_certificate","version":"1.0","problem":"(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n","proof":"{proof}"}}"#,
    );
    std::fs::write(&certificate, json).unwrap();
    Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(["cert", "verify-external"])
        .arg(certificate)
        .arg("--verbose")
        .output()
        .unwrap()
}

#[test]
fn packaged_checker_accepts_a_complete_control_proof() {
    let output = check(
        r"(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n",
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(
        stdout.contains("Proof status: fully verified"),
        "{stdout}\n{stderr}"
    );
}

#[test]
fn packaged_checker_rejects_an_invalid_refutation() {
    // Resolving p against itself cannot derive the empty clause, even though
    // the input problem happens to be UNSAT. The proof must really be checked.
    let output = check(r"(assume t0 p)\n(step t1 (cl) :rule resolution :premises (t0 t0))\n");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "invalid proof accepted: {stdout}\n{stderr}"
    );
    assert!(
        !stdout.contains("Proof status: fully verified"),
        "{stdout}\n{stderr}"
    );
    assert!(
        !stderr.contains("feature required"),
        "missing capability is not a proof rejection: {stderr}"
    );
}
