// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual elaboration, native compilation, linking and byte-preserving output.
//! argv supplies the prefix at runtime; the repeated result exercises sharing.

use std::path::Path;
use std::process::Command;

const SOURCE: &str = include_str!("fixtures/sized_string_seeded.lean");

fn check(binary: &Path) {
    for prefix in [None, Some(""), Some("suffix7"), Some("é🦀")] {
        let mut command = Command::new(binary);
        if let Some(arg) = prefix {
            command.arg(arg);
        }
        let out = command.output().expect("execute native string program");
        let s = prefix.unwrap_or("");
        let t = format!("{s}\0β\x007");
        let c = char::from_u32(s.chars().count() as u32).expect("small scalar");
        let emoji = char::from_u32(128512 + s.chars().count() as u32).expect("small scalar");
        let expected = format!(
            "a\0b{t}\n{t}\n{t}\n{t}{t}\n{c}\n{t}é€\n{t}{emoji}\n{emoji}\n{}\n\0\0\n\n",
            t.chars().count()
        );
        assert_eq!(out.status.code(), Some(0), "{prefix:?}: {:?}", out.stderr);
        assert_eq!(out.stdout, expected.as_bytes(), "stdout {prefix:?}");
        assert_eq!(out.stderr, format!("{t}\n").as_bytes(), "stderr {prefix:?}");
    }
}

#[test]
fn c_backend_executes_sized_strings() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("strings.lean");
    std::fs::write(&source, SOURCE).expect("fixture");
    for opt in [0, 2] {
        let binary = dir.path().join(format!("strings-{opt}"));
        clean_native::native_build::build_native_executable_with_source_sink(
            &source, "main", opt, &binary, None,
        )
        .unwrap_or_else(|e| panic!("C build opt {opt}: {e:#}"));
        check(&binary);
    }
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn trustcg_backend_executes_sized_strings() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("strings.lean");
    std::fs::write(&source, SOURCE).expect("fixture");
    let (receipt, built) = clean_native::native_trustcg::build_with_receipt(&source, "main", 0);
    let built = built.unwrap_or_else(|e| panic!("trust-cg build: {e}; {receipt:?}"));
    check(built.binary());
}

// The incoming Int.natAbs borrowed domain must still reach the native matcher
// when every ExternCalls module declares the new sized-constructor signature.
fn check_signed_abs(binary: &Path) {
    for (args, expected) in [(&[][..], "0\n1\n"), (&["a", "b"][..], "2\n3\n")] {
        let out = Command::new(binary)
            .args(args)
            .output()
            .expect("execute signed abs");
        assert_eq!(out.status.code(), Some(0), "{:?}", out.stderr);
        assert_eq!(out.stdout, expected.as_bytes());
        assert!(out.stderr.is_empty());
    }
}

#[test]
fn c_backend_keeps_signed_nat_abs_with_sized_runtime() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("abs.lean");
    std::fs::write(&source, include_str!("fixtures/signed_nat_abs.lean")).expect("fixture");
    let binary = dir.path().join("abs");
    clean_native::native_build::build_native_executable_with_source_sink(
        &source, "main", 0, &binary, None,
    )
    .unwrap_or_else(|e| panic!("C signed abs build: {e:#}"));
    check_signed_abs(&binary);
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn trustcg_backend_keeps_signed_nat_abs_with_sized_runtime() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("abs.lean");
    std::fs::write(&source, include_str!("fixtures/signed_nat_abs.lean")).expect("fixture");
    let (receipt, built) = clean_native::native_trustcg::build_with_receipt(&source, "main", 0);
    let built = built.unwrap_or_else(|e| panic!("trust-cg signed abs build: {e}; {receipt:?}"));
    check_signed_abs(built.binary());
}
