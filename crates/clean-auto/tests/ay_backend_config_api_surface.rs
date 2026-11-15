// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "support/rustc.rs"]
mod rustc_support;

#[path = "support/metadata.rs"]
mod metadata_support;

use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_compile_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "clean_auto_ay_backend_config_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> Output {
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

fn assert_external_compile_succeeds(test_name: &str, source: &str) {
    let output = compile_external_snippet(test_name, source);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "snippet failed to compile\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
#[file_serial]
fn test_ay_backend_config_fields_stay_private() {
    assert_external_compile_fails(
        "private_ay_backend_config_fields",
        r#"
use clean_auto::bridge::ay_contract::{TriggerPolicy, AyBackendConfig, AyLogic};

fn touch(mut config: AyBackendConfig) {
    let _ = config.logic;
    let _ = config.timeout_ms;
    let _ = config.produce_proofs;
    let _ = config.verbose;
    let _ = &config.proof_profile;
    let _ = config.trigger_policy;
    config.produce_proofs = true;
    config.trigger_policy = TriggerPolicy::UserOnly;
}

fn build() -> AyBackendConfig {
    AyBackendConfig::new(AyLogic::QfLia)
}
"#,
        &[
            "logic",
            "timeout_ms",
            "produce_proofs",
            "verbose",
            "proof_profile",
            "trigger_policy",
            "private",
        ],
    );
}

#[test]
#[file_serial]
fn test_ay_backend_config_builder_and_getters_remain_public() {
    assert_external_compile_succeeds(
        "public_ay_backend_config_getters",
        r#"
use clean_auto::bridge::ay_contract::{ProofProfile, TriggerPolicy, AyBackendConfig, AyLogic};

fn build() {
    let config = AyBackendConfig::new(AyLogic::QfLia)
        .timeout(50)
        .verbose()
        .enable_proofs()
        .proof_profile(ProofProfile::carcara_verified())
        .trigger_policy(TriggerPolicy::UserOnly);
    let _ = config.logic();
    let _ = config.timeout_ms();
    let _ = config.produces_proofs();
    let _ = config.is_verbose();
    let _ = config.profile();
    let _ = config.trigger_policy_value();
}
"#,
    );
}

/// `AyTriggerPattern` is backend-only and no longer externally importable
/// after `ay_backend` became `pub(crate)` (Part of #2774).
#[test]
#[file_serial]
fn test_ay_trigger_pattern_not_externally_importable() {
    assert_external_compile_fails(
        "ay_trigger_pattern_hidden",
        r#"
#![allow(unused_imports)]
use clean_auto::bridge::ay_backend::AyTriggerPattern;
"#,
        &["ay_backend"],
    );
}
