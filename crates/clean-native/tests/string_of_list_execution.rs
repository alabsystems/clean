// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute the genuine String.ofList primitive through both native callers.
//! This does not qualify the separate checked byte-backed String source model.

use std::path::Path;
use std::process::Command;

const SOURCE: &str = include_str!("fixtures/string_of_list.lean");

fn check(binary: &Path) {
    for args in [&[][..], &["x", "y", "z"][..]] {
        let output = Command::new(binary).args(args).output().expect("execute");
        let n = args.len() as u32;
        let first = char::from_u32(97 + n).expect("small scalar");
        let emoji = char::from_u32(128512 + n).expect("small scalar");
        let value = format!("{first}\0é€{emoji}");
        let expected = format!("{value}\n{value}\n\n");
        assert_eq!(output.status.code(), Some(0), "{:?}", output.stderr);
        assert_eq!(output.stdout, expected.as_bytes());
        assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    }
}

#[test]
fn c_backend_executes_string_of_list_with_dynamic_nul_and_utf8() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("of-list.lean");
    std::fs::write(&source, SOURCE).expect("fixture");
    for opt in [0, 2] {
        let binary = dir.path().join(format!("of-list-{opt}"));
        clean_native::native_build::build_native_executable_with_source_sink(
            &source, "main", opt, &binary, None,
        )
        .unwrap_or_else(|e| panic!("C build opt {opt}: {e:#}"));
        check(&binary);
    }
}

#[cfg(feature = "trust-ir-backend")]
#[test]
fn trustcg_backend_executes_string_of_list_with_dynamic_nul_and_utf8() {
    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("of-list.lean");
    std::fs::write(&source, SOURCE).expect("fixture");
    let (receipt, built) = clean_native::native_trustcg::build_with_receipt(&source, "main", 0);
    let built = built.unwrap_or_else(|e| panic!("trust-cg build: {e}; {receipt:?}"));
    check(built.binary());
}
