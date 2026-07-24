// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exit-status handoff smoke test for `clean lake exe`.
//!
//! This pre-seeds the native artifact at Lake's handoff path so the test only
//! exercises process status forwarding, not Lean-level exit lowering.

#![cfg(unix)]

mod support;

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn write_lake_exe_project(dir: &Path, exe_name: &str) {
    std::fs::write(
        dir.join("lakefile.lean"),
        format!(
            r#"import Lake
open Lake DSL

package exitStatusSmoke where
  version := "0.1.0"

lean_exe {exe_name} where
  root := `Main
"#
        ),
    )
    .expect("write lakefile.lean");
    std::fs::write(dir.join("Main.lean"), "def main : IO Unit := pure ()\n")
        .expect("write Main.lean");
}

fn write_failing_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'before failure\n'
printf 'native stderr before failure\n' >&2
exit 7
"#,
    )
    .expect("write native artifact");
    let mut perms = std::fs::metadata(&artifact)
        .expect("artifact metadata")
        .permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&artifact, perms).expect("chmod native artifact");
    support::write_fresh_source_closure_sidecar(dir, exe_name, &["Main.lean"]);
    artifact
}

fn write_stdio_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'native stdout line one\n'
printf 'native stdout line two\n'
printf 'native stderr line one\n' >&2
printf 'native stderr line two\n' >&2
"#,
    )
    .expect("write native artifact");
    let mut perms = std::fs::metadata(&artifact)
        .expect("artifact metadata")
        .permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&artifact, perms).expect("chmod native artifact");
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
fn lake_exe_preseeded_native_artifact_propagates_nonzero_exit_status_without_lean_exit_lowering() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "exit_status_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = write_failing_native_artifact(dir.path(), exe_name);

    let output = run_clean(&["lake", "exe", exe_name], dir.path());

    assert_eq!(
        output.status.code(),
        Some(7),
        "`clean lake exe` should propagate the pre-seeded native artifact status at {}; stdout={}; stderr={}",
        artifact.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "before failure\n",
        "`lake exe` should preserve native stdout before a nonzero exit"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("native stderr before failure\n"),
        "`lake exe` should preserve native stderr before reporting status: {stderr}"
    );
    assert!(
        stderr.contains("Executable exited with status"),
        "`lake exe` should still diagnose the native nonzero status: {stderr}"
    );
}

#[test]
fn lake_exe_preseeded_native_artifact_preserves_success_stdout_and_stderr() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "stdio_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = write_stdio_native_artifact(dir.path(), exe_name);

    let output = run_clean(&["lake", "exe", exe_name], dir.path());

    assert!(
        output.status.success(),
        "`clean lake exe` should execute the pre-seeded native artifact at {}; status={:?}; stdout={}; stderr={}",
        artifact.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "native stdout line one\nnative stdout line two\n",
        "`lake exe` should preserve successful native stdout exactly"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "native stderr line one\nnative stderr line two\n",
        "`lake exe` should preserve successful native stderr exactly"
    );
}
