// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Command handoff smoke tests for `clean lake env`.
//!
//! The command is a stable system shell, so this isolates Lake's process
//! cwd/env/argv behavior without generating a temporary executable.

#![cfg(unix)]

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn write_lake_project(dir: &Path) {
    fs::write(
        dir.join("lakefile.lean"),
        r#"import Lake
open Lake DSL

package envSmoke where
  version := "0.1.0"
"#,
    )
    .expect("write lakefile.lean");
}

fn run_clean(args: &[&str], cwd: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .env("CLEAN_LAKE_ENV_SMOKE", "from-parent-env")
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

fn run_clean_with_path(args: &[&str], cwd: &Path, path: OsString) -> Output {
    Command::new(clean_path())
        .args(args)
        .env("PATH", &path)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

#[test]
fn lake_env_command_runs_from_workspace_root_with_inherited_env_and_forwarded_args() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("env_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    write_lake_project(&project_dir);

    let expected_cwd = fs::canonicalize(&project_dir)
        .expect("canonical project dir")
        .display()
        .to_string();
    let expected_stdout =
        format!("cwd={expected_cwd}\nenv=from-parent-env\narg1=alpha\narg2=--literal-flag\n");
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let script = "printf 'cwd=%s\nenv=%s\narg1=%s\narg2=%s\n' \"$(pwd)\" \"$CLEAN_LAKE_ENV_SMOKE\" \"$1\" \"$2\"";

    let output = run_clean(
        &[
            "lake",
            "--dir",
            project_arg,
            "env",
            "/bin/sh",
            "-c",
            script,
            "native-sh",
            "alpha",
            "--literal-flag",
        ],
        dir.path(),
    );

    assert!(
        output.status.success(),
        "`clean lake env <command>` should execute the command from the workspace root; status={:?}; stdout={}; stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        expected_stdout,
        "`lake env <command>` should preserve workspace cwd, inherited env, and trailing args"
    );
}

#[test]
fn lake_env_command_forwards_child_exit_status() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("env_exit_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    write_lake_project(&project_dir);
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");

    let output = run_clean(
        &[
            "lake",
            "--dir",
            project_arg,
            "env",
            "/bin/sh",
            "-c",
            "exit 7",
        ],
        dir.path(),
    );

    assert_eq!(
        output.status.code(),
        Some(7),
        "`lake env <command>` should forward the child exit status; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn lake_env_command_preserves_parent_path_for_child_process() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("env_path_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    write_lake_project(&project_dir);

    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let inherited_path = std::env::join_paths([
        dir.path().join("first path entry"),
        PathBuf::from("/usr/bin"),
        PathBuf::from("/bin"),
    ])
    .expect("join inherited PATH");

    let output = run_clean_with_path(
        &[
            "lake",
            "--dir",
            project_arg,
            "env",
            "/bin/sh",
            "-c",
            "printf 'PATH=%s\n' \"$PATH\"",
        ],
        dir.path(),
        inherited_path.clone(),
    );

    assert!(
        output.status.success(),
        "`clean lake env <command>` should execute with inherited PATH; status={:?}; stdout={}; stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!("PATH={}\n", inherited_path.to_string_lossy()),
        "`lake env <command>` should preserve the parent PATH for the child process"
    );
}

#[test]
fn lake_env_missing_command_diagnostic_names_command_and_workspace() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("env_missing_command_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    write_lake_project(&project_dir);

    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let workspace = fs::canonicalize(&project_dir)
        .expect("canonical project dir")
        .display()
        .to_string();
    let missing_command = "clean-lake-env-command-that-should-not-exist";

    let output = run_clean(
        &["lake", "--dir", project_arg, "env", missing_command],
        dir.path(),
    );

    assert!(
        !output.status.success(),
        "`lake env <missing-command>` should fail closed; stdout={}; stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("clean lake env is fail-closed"),
        "diagnostic should identify fail-closed Lake env behavior: {stderr}"
    );
    assert!(
        stderr.contains(missing_command),
        "diagnostic should name the failed command: {stderr}"
    );
    assert!(
        stderr.contains(&workspace),
        "diagnostic should name the workspace path: {stderr}"
    );
}
