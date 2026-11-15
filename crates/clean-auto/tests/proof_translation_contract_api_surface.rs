// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compile-surface canaries for the proof-translation classifier contract.
//!
//! These tests verify that `proof_translation_contract` is the ONLY public
//! classifier surface visible to cross-crate consumers (e.g. `clean-elab`).
//! The internal `expr_classifier` module MUST remain non-importable.
//!
//! Part of #2810.

#[path = "support/rustc.rs"]
mod rustc_support;

#[path = "support/metadata.rs"]
mod metadata_support;

use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_compile_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "clean_auto_proof_contract_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> std::process::Output {
    let metadata = metadata_support::clean_auto();
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    // TRUST OPT-OUT — use Cargo's selected `RUSTC` so this snippet and the
    // linked crate metadata always share a compiler ABI. When that compiler is
    // Trust, disable obligation checking for this throwaway API-surface probe;
    // the snippet proves only that a public name is reachable.
    // The compiler is Trust (owner directive 2026-09-28); there is no retry
    // without the opt-out.
    let run_rustc = || {
        let mut cmd = Command::new(rustc_support::cargo_rustc());
        cmd.arg("-Ztrust-verify=off");
        cmd.arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_auto={}", metadata.artifact.display()));
        metadata.configure(&mut cmd);
        cmd.output()
    };
    let output = run_rustc().expect("trustc should be runnable from integration tests");

    let _ = fs::remove_dir_all(&compile_dir);
    output
}

fn assert_external_compile_succeeds(test_name: &str, source: &str) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "snippet failed to compile\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

fn assert_external_compile_fails(test_name: &str, source: &str, expected_fragments: &[&str]) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        !output.status.success(),
        "snippet unexpectedly compiled successfully\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    for fragment in expected_fragments {
        assert!(
            stderr.contains(fragment),
            "expected rustc stderr to contain `{fragment}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }
}

/// The `proof_translation_contract` module and its key types are importable
/// cross-crate. This is the public classifier surface that `clean-elab`'s
/// proof-producing translator depends on. Part of #2810.
#[test]
#[file_serial]
fn test_proof_translation_contract_is_importable_cross_crate() {
    assert_external_compile_succeeds(
        "proof_contract_importable",
        r#"
#![allow(dead_code)]
use clean_auto::bridge::proof_translation_contract::{
    SmtLogicalForm, classify_for_proof_translation,
};

fn touch_classify() {
    // Verify both the function and enum are nameable from external crates.
    let _f = classify_for_proof_translation;
    let _match_arm = |form: SmtLogicalForm| match form {
        SmtLogicalForm::And(_, _)
        | SmtLogicalForm::Or(_, _)
        | SmtLogicalForm::Not(_)
        | SmtLogicalForm::Implies(_, _)
        | SmtLogicalForm::Iff(_, _)
        | SmtLogicalForm::Eq { .. }
        | SmtLogicalForm::Neq { .. }
        | SmtLogicalForm::Lt { .. }
        | SmtLogicalForm::Le { .. }
        | SmtLogicalForm::Gt { .. }
        | SmtLogicalForm::Ge { .. }
        | SmtLogicalForm::Add { .. }
        | SmtLogicalForm::Sub { .. }
        | SmtLogicalForm::Mul { .. }
        | SmtLogicalForm::Div { .. }
        | SmtLogicalForm::Mod { .. }
        | SmtLogicalForm::Neg { .. }
        | SmtLogicalForm::Forall { .. }
        | SmtLogicalForm::Exists { .. }
        | SmtLogicalForm::True
        | SmtLogicalForm::False
        | SmtLogicalForm::Atom(_) => true,
        _ => false, // #[non_exhaustive]
    };
}
"#,
    );
}

/// The internal `expr_classifier` module MUST remain non-importable from
/// external crates. Only the `proof_translation_contract` wrapper is public.
/// Part of #2810.
#[test]
#[file_serial]
fn test_expr_classifier_stays_non_importable() {
    assert_external_compile_fails(
        "expr_classifier_hidden",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::expr_classifier::{LogicalForm, classify_expr};
"#,
        &["expr_classifier"],
    );
}

/// The `proof_translation_contract` path must NOT expose internal bridge
/// types beyond `SmtLogicalForm` and `classify_for_proof_translation`.
/// This ensures the cross-crate surface stays auditable and minimal.
/// Part of #2810.
#[test]
#[file_serial]
fn test_proof_translation_contract_does_not_leak_bridge_internals() {
    assert_external_compile_fails(
        "proof_contract_no_leaks",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::proof_translation_contract::LogicalForm;
"#,
        &["LogicalForm"],
    );
}
