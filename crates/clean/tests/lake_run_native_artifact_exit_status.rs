// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exit-status and stdio handoff smoke test for `clean lake run`.
//!
//! These pre-seed native artifacts at Lake's handoff path so the tests only
//! exercise process handoff, not Lean-level executable generation.

#![cfg(unix)]

mod support;

use std::fs;
use std::os::unix::fs::symlink;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn write_lake_exe_project(dir: &Path, exe_name: &str) {
    fs::write(
        dir.join("lakefile.lean"),
        format!(
            r#"import Lake
open Lake DSL

package runExitStatusSmoke where
  version := "0.1.0"

lean_exe {exe_name} where
  root := `Main
"#
        ),
    )
    .expect("write lakefile.lean");
    fs::write(dir.join("Main.lean"), "def main : IO Unit := pure ()\n").expect("write Main.lean");
}

fn symlink_native_shell_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    fs::create_dir_all(artifact.parent().expect("artifact parent")).expect("create artifact dir");
    symlink("/bin/sh", &artifact).expect("symlink native shell artifact");
    support::write_fresh_source_closure_sidecar(dir, exe_name, &["Main.lean"]);
    artifact
}

fn write_stdio_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    fs::create_dir_all(artifact.parent().expect("artifact parent")).expect("create artifact dir");
    fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'run native stdout line one\n'
printf 'run native stdout line two\n'
printf 'run native stderr line one\n' >&2
printf 'run native stderr line two\n' >&2
"#,
    )
    .expect("write native artifact");
    let mut perms = fs::metadata(&artifact)
        .expect("artifact metadata")
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&artifact, perms).expect("chmod native artifact");
    support::write_fresh_source_closure_sidecar(dir, exe_name, &["Main.lean"]);
    artifact
}

fn run_clean(args: &[&str], project_dir: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .current_dir(project_dir)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

#[test]
fn lake_run_preseeded_native_artifact_preserves_nonzero_status_stdio_and_forwarded_args() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "run_exit_status_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = symlink_native_shell_artifact(dir.path(), exe_name);
    let script = "printf 'run stdout arg=%s\\n' \"$1\"; \
                  printf 'run stderr arg=%s\\n' \"$2\" >&2; \
                  exit \"$3\"";

    let output = run_clean(
        &[
            "lake",
            "run",
            exe_name,
            "-c",
            script,
            "native-sh",
            "two words",
            "--literal-flag",
            "9",
        ],
        dir.path(),
    );

    assert_eq!(
        output.status.code(),
        Some(9),
        "`clean lake run` should propagate the pre-seeded native artifact status at {}; stdout={}; stderr={}",
        artifact.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "run stdout arg=two words\n",
        "`lake run` should preserve native stdout and forwarded argv before a nonzero exit"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("run stderr arg=--literal-flag\n"),
        "`lake run` should preserve native stderr and forwarded argv before reporting status: {stderr}"
    );
    assert!(
        stderr.contains("Executable exited with status"),
        "`lake run` should still diagnose the native nonzero status: {stderr}"
    );
}

#[test]
fn lake_run_preseeded_native_artifact_preserves_success_stdout_and_stderr() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "run_stdio_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = write_stdio_native_artifact(dir.path(), exe_name);

    let output = run_clean(&["lake", "run", exe_name], dir.path());

    assert!(
        output.status.success(),
        "`clean lake run` should execute the pre-seeded native artifact at {}; status={:?}; stdout={}; stderr={}",
        artifact.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "run native stdout line one\nrun native stdout line two\n",
        "`lake run` should preserve successful native stdout exactly"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "run native stderr line one\nrun native stderr line two\n",
        "`lake run` should preserve successful native stderr exactly"
    );
}
