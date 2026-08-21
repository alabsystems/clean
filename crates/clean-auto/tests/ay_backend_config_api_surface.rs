// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use serial_test::file_serial;
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
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
        "clean_auto_ay_backend_config_{test_name}_{}_{}",
        std::process::id(),
        nanos
    ))
}

fn compile_external_snippet(test_name: &str, source: &str) -> Output {
    let artifact = clean_auto_metadata_artifact();
    let deps_dir = artifact
        .parent()
        .expect("clean_auto artifact should live in deps directory");
    let compile_dir = temp_compile_dir(test_name);
    fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

    let source_path = compile_dir.join("snippet.rs");
    fs::write(&source_path, source).expect("snippet source should be writable");

    // TRUST OPT-OUT — see `clean-elab/src/tactic/native_decide_eval.rs` for the
    // full rationale. `rustc` resolves through rustup from this repo's
    // `rust-toolchain.toml`, pinned to `channel = "trust"`, so it ran Trust's
    // obligation checker over this throwaway API-surface SNIPPET and failed the
    // build ("Trust strict verification failed for `snippet::touch`"). The
    // snippet exists only to prove a name is reachable; it is not a
    // verification target. Probe, and fall back when the flag is not understood.
    let run_rustc = |trust_opt_out: bool| {
        let mut cmd = Command::new("rustc");
        if trust_opt_out {
            cmd.arg("-Ztrust-verify=off");
        }
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
            .arg(format!("clean_auto={}", artifact.display()))
            .arg("-L")
            .arg(format!("dependency={}", deps_dir.display()))
            .output()
    };
    let flag_was_rejected = |stderr: &str| {
        stderr.contains("only accepted on the nightly compiler")
            || stderr.contains("unknown unstable option")
            || stderr.contains("unknown debugging option")
            || stderr.contains("incorrect value")
    };
    let mut output = run_rustc(true).expect("rustc should be runnable from integration tests");
    if !output.status.success() && flag_was_rejected(&String::from_utf8_lossy(&output.stderr)) {
        output = run_rustc(false).expect("rustc should be runnable from integration tests");
    }

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
