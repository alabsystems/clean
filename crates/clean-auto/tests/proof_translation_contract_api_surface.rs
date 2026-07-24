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

use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn clean_auto_metadata_artifact() -> PathBuf {
    let deps_dir = std::env::current_exe()
        .expect("integration test should know its executable path")
        .parent()
        .expect("integration test executable should live under target deps")
        .to_path_buf();
    let mut rlibs = Vec::new();
    let mut rmetas = Vec::new();

    for path in fs::read_dir(&deps_dir)
        .expect("deps directory should be readable")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
    {
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !file_name.starts_with("libclean_auto-") {
            continue;
        }

        match path.extension().and_then(|ext| ext.to_str()) {
            Some("rlib") => rlibs.push(path),
            Some("rmeta") => rmetas.push(path),
            _ => {}
        }
    }

    let sort_by_mtime = |artifacts: &mut Vec<PathBuf>| {
        artifacts.sort_by_key(|path| {
            fs::metadata(path)
                .and_then(|metadata| metadata.modified())
                .unwrap_or(UNIX_EPOCH)
        });
    };
    sort_by_mtime(&mut rlibs);
    sort_by_mtime(&mut rmetas);

    rlibs
        .pop()
        .or_else(|| rmetas.pop())
        .expect("clean_auto metadata artifact should exist in deps dir")
}

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
    let artifact = clean_auto_metadata_artifact();
    let deps_dir = artifact
        .parent()
        .expect("clean_auto artifact should live in deps directory");
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    let output = Command::new("rustc")
        .arg("--crate-type")
        .arg("lib")
        .arg("--edition")
        .arg("2021")
        .arg("--emit")
        .arg("metadata")
        .arg("--out-dir")
        .arg(&compile_dir)
        .arg(&source_path)
        .arg("--extern")
        .arg(format!("clean_auto={}", artifact.display()))
        .arg("-L")
        .arg(format!("dependency={}", deps_dir.display()))
        .output()
        .expect("rustc should be runnable from integration tests");

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
