// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused process-boundary checks for serialized-kernel math pilot obligations.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

use serde_json::Value;

const CLEAN_MATH_CLI_BIN_ENV: &str = "CLEAN_MATH_CLI_BIN";
const CARGO_CLEAN_BIN_ENV: &str = "CARGO_BIN_EXE_clean";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn clean_binary() -> PathBuf {
    static BINARY: OnceLock<PathBuf> = OnceLock::new();
    BINARY.get_or_init(resolve_clean_binary).clone()
}

fn resolve_clean_binary() -> PathBuf {
    if let Some(binary) = env::var_os(CLEAN_MATH_CLI_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_MATH_CLI_BIN_ENV} points to {}, but it is not a file",
            binary.display()
        );
        return binary;
    }

    if let Some(binary) = env::var_os(CARGO_CLEAN_BIN_ENV)
        .map(PathBuf::from)
        .filter(|binary| binary.is_file())
    {
        return binary;
    }

    build_clean_binary()
}

fn build_clean_binary() -> PathBuf {
    let root = workspace_root();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let status = Command::new(cargo)
        .args(["build", "--quiet", "-p", "clean", "--bin", "clean"])
        .current_dir(&root)
        .env("CARGO_TERM_COLOR", "never")
        .status()
        .expect("cargo build -p clean --bin clean should start");
    assert!(status.success(), "failed to build clean binary: {status}");

    let binary = root
        .join("target")
        .join("debug")
        .join(format!("clean{}", env::consts::EXE_SUFFIX));
    assert!(
        binary.is_file(),
        "cargo build succeeded, but {} does not exist",
        binary.display()
    );
    binary
}

fn run_clean(args: &[&str]) -> Output {
    Command::new(clean_binary())
        .args(args)
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
}

fn run_clean_json(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        output.status.success(),
        "clean {args:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn run_clean_json_expect_failure(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        !output.status.success(),
        "clean {args:?} unexpectedly succeeded\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn parse_json(args: &[&str], output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "clean {args:?} did not emit JSON on stdout: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn read_fixture_json(path: &str) -> Value {
    let path = workspace_root().join(path);
    let bytes =
        fs::read(&path).unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|err| panic!("failed to parse {} as JSON: {err}", path.display()))
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn write_temp_obligation(name: &str, obligation: &Value) -> PathBuf {
    let dir = workspace_root()
        .join("target")
        .join("clean-cli-pilot-obligation-tests");
    fs::create_dir_all(&dir)
        .unwrap_or_else(|err| panic!("failed to create {}: {err}", dir.display()));
    let path = dir.join(name);
    let bytes =
        serde_json::to_vec_pretty(obligation).expect("temporary obligation should serialize");
    fs::write(&path, bytes)
        .unwrap_or_else(|err| panic!("failed to write {}: {err}", path.display()));
    path
}

#[test]
fn serialized_kernel_pilot_obligations_validate_and_open() {
    for (project, obligation, project_name, domain) in [
        (
            "tests/fixtures/math_project/sat_pb/project.json",
            "tests/fixtures/math_project/sat_pb/obligations/ay_serialized_kernel_pilot.json",
            "sat-pb-pilot",
            "sat-pb",
        ),
        (
            "tests/fixtures/math_project/nn_verify/project.json",
            "tests/fixtures/math_project/nn_verify/obligations/gamma_crown_serialized_kernel_pilot.json",
            "nn-verify-pilot",
            "nn-verify",
        ),
    ] {
        let validation = run_clean_json(&[
            "math",
            "obligation",
            "validate",
            obligation,
            "--project",
            project,
            "--json",
        ]);
        assert_eq!(validation["schema_version"], "clean-obligation-report-v1");
        assert_eq!(validation["project"], project_name);
        assert_eq!(validation["domain_profile"], domain);
        assert_eq!(validation["status"], "pass");

        let opened = run_clean_json(&[
            "math",
            "proof-state",
            "open-obligation",
            "--project",
            project,
            obligation,
            "--json",
        ]);
        assert_eq!(
            opened["schema_version"],
            "clean-cli-proof-state-open-obligation-v1"
        );
        assert_eq!(opened["operation"], "open-obligation");
        assert_eq!(opened["project"], project_name);
        assert_eq!(opened["domain_profile"], domain);
        assert_eq!(opened["status"], "opened-server-state");
        assert!(opened["state_id"]
            .as_str()
            .expect("state_id")
            .starts_with("ps_"));
    }
}

#[test]
fn proof_state_prove_rejects_untrusted_local_assumption_match() {
    for (project, obligation, project_name, local_name) in [
        (
            "tests/fixtures/math_project/sat_pb/project.json",
            "tests/fixtures/math_project/sat_pb/obligations/ay_serialized_kernel_pilot.json",
            "sat-pb-pilot",
            "h_ay_subsumption_deletion",
        ),
        (
            "tests/fixtures/math_project/nn_verify/project.json",
            "tests/fixtures/math_project/nn_verify/obligations/gamma_crown_serialized_kernel_pilot.json",
            "nn-verify-pilot",
            "h_gamma_crown_certificate_result",
        ),
    ] {
        let proof = run_clean_json_expect_failure(&[
            "math",
            "obligation",
            "prove",
            "--project",
            project,
            obligation,
            "--proof-state",
            "--json",
        ]);

        assert_eq!(proof["schema_version"], "clean-math-proof-attempt-v1");
        assert_eq!(proof["project"], project_name);
        assert_eq!(proof["status"], "blocked-untrusted-local-assumption");
        let expected_detail = format!(
            "local_context[1] `{local_name}` has the same serialized type as the goal, but proof-state `assumption` requires accepted local provenance under trust policy `constructive-only`; add metadata `local_context[1].provenance` or `local_context.{local_name}.provenance` with checked-kernel provenance, or link replay/kernel evidence instead"
        );
        assert_eq!(
            proof["details"][0].as_str().expect("blocker detail"),
            expected_detail.as_str()
        );
        let attempts = proof["tactic_attempts"]
            .as_array()
            .expect("tactic_attempts");
        assert!(attempts
            .iter()
            .all(|attempt| attempt["tactic"].as_str() != Some("assumption")));
    }
}

#[test]
fn sat_pb_serialized_kernel_pilot_documents_no_proof_state_blocker() {
    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "prove",
        "--project",
        "tests/fixtures/math_project/sat_pb/project.json",
        "tests/fixtures/math_project/sat_pb/obligations/ay_serialized_kernel_pilot.json",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["status"], "blocked-no-proof-search-v2");
    assert!(report["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("pass --proof-state")));
}

#[test]
fn pretty_only_obligations_still_fail_closed() {
    for (project, obligation, project_name, domain) in [
        (
            "tests/fixtures/math_project/sat_pb/project.json",
            "tests/fixtures/math_project/sat_pb/obligations/subsumption.json",
            "sat-pb-pilot",
            "sat-pb",
        ),
        (
            "tests/fixtures/math_project/nn_verify/project.json",
            "tests/fixtures/math_project/nn_verify/obligations/farkas.json",
            "nn-verify-pilot",
            "nn-verify",
        ),
    ] {
        let report = run_clean_json_expect_failure(&[
            "math",
            "proof-state",
            "open-obligation",
            "--project",
            project,
            obligation,
            "--json",
        ]);
        assert_eq!(
            report["schema_version"],
            "clean-cli-proof-state-open-obligation-v1"
        );
        assert_eq!(report["operation"], "open-obligation");
        assert_eq!(report["project"], project_name);
        assert_eq!(report["domain_profile"], domain);
        assert_eq!(report["status"], "blocked-pretty-only-obligation");
        assert!(report["state_id"].is_null());
    }
}
