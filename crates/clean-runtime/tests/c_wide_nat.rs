// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compare the shipped C Nat runtime with recorded official Lean output.

#![cfg(target_pointer_width = "64")]

use std::path::Path;
use std::process::Command;

#[test]
fn wide_nat_matches_lean_and_preserves_ownership() {
    let dir = tempfile::tempdir().expect("temporary C executable");
    let binary = dir.path().join("wide_nat");
    let source = Path::new(env!("CARGO_MANIFEST_DIR"));
    let compiled = Command::new("cc")
        .current_dir(source)
        .args([
            "-std=c11",
            "-O2",
            "-I",
            "include",
            "src/clean_runtime.c",
            "tests/c_wide_nat.c",
            "-o",
        ])
        .arg(&binary)
        .output()
        .expect("C compiler required");
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let output = Command::new(&binary).output().expect("C runtime vectors");
    assert!(output.status.success(), "{:?}", output.stderr);
    assert_eq!(output.stdout, include_bytes!("wide_nat_oracle/stdout"));
    assert!(output.stderr.is_empty());

    for (mode, message) in [
        ("char-wide", "invalid Unicode scalar"),
        ("char-surrogate", "invalid Unicode scalar"),
        ("char-proof", "expected an erased proof"),
        ("narrow", "native Nat does not fit u128"),
        (
            "malformed",
            "native Nat byte extent must contain whole limbs",
        ),
    ] {
        let output = Command::new(&binary)
            .arg(mode)
            .output()
            .expect("C runtime refusal");
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains(message));
    }

    for mode in ["pow-exponent-cutoff", "pow-aliased-oversized"] {
        let output = Command::new(&binary)
            .arg(mode)
            .output()
            .expect("C runtime Nat.pow panic");
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        assert_eq!(
            output.stderr,
            b"INTERNAL PANIC: Nat.pow exponent is too big\n"
        );
    }
}
