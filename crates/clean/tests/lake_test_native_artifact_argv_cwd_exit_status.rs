// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native executable handoff smoke test for `clean lake test <target> ...args`.
//!
//! The native test artifact is a symlink to `/bin/sh`, so this exercises Lake's
//! process handoff without generating a temporary executable.

#![cfg(unix)]

mod support;

use std::fs;
use std::os::unix::fs::{symlink, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn write_lake_test_project(dir: &Path, test_name: &str) {
    fs::write(
        dir.join("lakefile.lean"),
        format!(
            r#"import Lake
open Lake DSL

package testArgvCwdSmoke where
  version := "0.1.0"

lean_test {test_name} where
  root := `Main
"#
        ),
    )
    .expect("write lakefile.lean");
    fs::write(dir.join("Main.lean"), "def main : IO Unit := pure ()\n").expect("write Main.lean");
}

fn symlink_native_shell_artifact(dir: &Path, test_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(test_name);
    fs::create_dir_all(artifact.parent().expect("artifact parent")).expect("create artifact dir");
    symlink("/bin/sh", &artifact).expect("symlink native shell artifact");
    support::write_fresh_source_closure_sidecar(dir, test_name, &["Main.lean"]);
    artifact
}

fn write_stdio_native_artifact(dir: &Path, test_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(test_name);
    fs::create_dir_all(artifact.parent().expect("artifact parent")).expect("create artifact dir");
    fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'test native stdout line one\n'
printf 'test native stdout line two\n'
printf 'test native stderr line one\n' >&2
printf 'test native stderr line two\n' >&2
"#,
    )
    .expect("write native artifact");
    let mut perms = fs::metadata(&artifact)
        .expect("artifact metadata")
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&artifact, perms).expect("chmod native artifact");
    support::write_fresh_source_closure_sidecar(dir, test_name, &["Main.lean"]);
    artifact
}

fn run_clean(args: &[&str], cwd: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

fn run_clean_with_test_env(args: &[&str], cwd: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .env("CLEAN_LAKE_TEST_ENV_SMOKE", "value with spaces=and=equals")
        .env("CLEAN_LAKE_TEST_EMPTY", "")
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

#[test]
fn lake_test_target_preseeded_native_artifact_preserves_success_stdout_and_stderr() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("test_stdio_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    let test_name = "test_stdio_smoke";
    write_lake_test_project(&project_dir, test_name);
    let artifact = write_stdio_native_artifact(&project_dir, test_name);
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");

    let output = run_clean(
        &["lake", "--dir", project_arg, "test", test_name],
        dir.path(),
    );

    assert!(
        output.status.success(),
        "`clean lake test` should execute the pre-seeded native test artifact at {}; status={:?}; stdout={}; stderr={}",
        artifact.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with("test native stdout line one\ntest native stdout line two\n"),
        "`lake test` should preserve successful native stdout before its summary: {stdout}"
    );
    assert!(
        stdout.contains("Test results: 1 passed, 0 failed"),
        "`lake test` should still print its bounded native-test summary: {stdout}"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "test native stderr line one\ntest native stderr line two\n",
        "`lake test` should preserve successful native stderr exactly"
    );
}

#[test]
fn lake_test_target_preseeded_native_artifact_preserves_argv_cwd_and_exit_status() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("test_argv_cwd_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    let test_name = "test_argv_cwd_smoke";
    write_lake_test_project(&project_dir, test_name);
    let artifact = symlink_native_shell_artifact(&project_dir, test_name);
    let expected_cwd = fs::canonicalize(&project_dir)
        .expect("canonical project dir")
        .display()
        .to_string();
    let expected_stdout =
        format!("cwd={expected_cwd}\narg1=alpha\narg2=two words\narg3=--literal-flag\n");
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let script = "printf 'cwd=%s\narg1=%s\narg2=%s\narg3=%s\n' \"$(pwd)\" \"$1\" \"$2\" \"$3\"; \
                  printf 'stderr arg=%s\n' \"$3\" >&2; \
                  exit \"$4\"";

    let output = run_clean(
        &[
            "lake",
            "--dir",
            project_arg,
            "test",
            test_name,
            "-c",
            script,
            "native-sh",
            "alpha",
            "two words",
            "--literal-flag",
            "9",
        ],
        dir.path(),
    );

    assert_eq!(
        output.status.code(),
        Some(9),
        "`clean lake test` should propagate the pre-seeded native test artifact status at {}; stdout={}; stderr={}",
        artifact.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with(&expected_stdout),
        "`lake test` should preserve native stdout, forwarded argv, and workspace cwd before its summary: {stdout}"
    );
    assert!(
        stdout.contains("Test results: 0 passed, 1 failed"),
        "`lake test` should still print its bounded native-test summary: {stdout}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("stderr arg=--literal-flag\n"),
        "`lake test` should preserve native stderr and forwarded argv before reporting status: {stderr}"
    );
    assert!(
        stderr.contains("Executable exited with status"),
        "`lake test` should still diagnose the native nonzero status: {stderr}"
    );
}

#[test]
fn lake_test_target_preseeded_native_artifact_inherits_parent_environment() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("test_env_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    let test_name = "test_env_smoke";
    write_lake_test_project(&project_dir, test_name);
    let artifact = symlink_native_shell_artifact(&project_dir, test_name);
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let script = "printf 'env=%s\n' \"$CLEAN_LAKE_TEST_ENV_SMOKE\"; \
                  printf 'empty=%s:%s\n' \"${CLEAN_LAKE_TEST_EMPTY+set}\" \"$CLEAN_LAKE_TEST_EMPTY\"; \
                  printf 'stderr-env=%s\n' \"$CLEAN_LAKE_TEST_ENV_SMOKE\" >&2";

    let output = run_clean_with_test_env(
        &[
            "lake",
            "--dir",
            project_arg,
            "test",
            test_name,
            "-c",
            script,
            "native-sh",
        ],
        dir.path(),
    );

    assert!(
        output.status.success(),
        "`clean lake test` should execute the pre-seeded native test artifact at {}; status={:?}; stdout={}; stderr={}",
        artifact.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with("env=value with spaces=and=equals\nempty=set:\n"),
        "`lake test` should preserve inherited environment values, including empty variables: {stdout}"
    );
    assert!(
        stdout.contains("Test results: 1 passed, 0 failed"),
        "`lake test` should still print its bounded native-test summary: {stdout}"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "stderr-env=value with spaces=and=equals\n",
        "`lake test` should not strip inherited env before native stderr is emitted"
    );
}
