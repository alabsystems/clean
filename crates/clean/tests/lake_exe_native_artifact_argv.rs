// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Executable handoff smoke tests for `clean lake exe`.
//!
//! These tests intentionally pre-seed the native artifact at Lake's handoff
//! path. That isolates CLI/runtime process behavior from the still-incomplete
//! Lean-level `IO.getArgs` lowering.

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

package argvSmoke where
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

fn write_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'argc=%s\n' "$#"
i=1
for arg in "$@"; do
  printf 'arg%s=%s\n' "$i" "$arg"
  i=$((i + 1))
done
printf 'env=%s\n' "$CLEAN_LAKE_ARGV_SMOKE"
printf 'stderr=%s\n' "$2" >&2
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

fn write_env_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    std::fs::create_dir_all(artifact.parent().expect("artifact parent"))
        .expect("create artifact dir");
    std::fs::write(
        &artifact,
        r#"#!/bin/sh
printf 'env=%s\n' "$CLEAN_LAKE_EXE_ENV_SMOKE"
printf 'empty=%s:%s\n' "${CLEAN_LAKE_EXE_EMPTY+set}" "$CLEAN_LAKE_EXE_EMPTY"
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
        .env("CLEAN_LAKE_ARGV_SMOKE", "from-parent-env")
        .current_dir(project_dir)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

#[test]
fn lake_exe_preseeded_native_artifact_forwards_argv_env_and_stdio_without_lean_getargs() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "argv_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = write_native_artifact(dir.path(), exe_name);

    let output = run_clean(
        &[
            "lake",
            "exe",
            exe_name,
            "alpha",
            "two words",
            "--literal-flag",
        ],
        dir.path(),
    );

    assert!(
        output.status.success(),
        "`clean lake exe` should execute the pre-seeded native artifact at {}; status={:?}; stderr={}",
        artifact.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "argc=3\narg1=alpha\narg2=two words\narg3=--literal-flag\nenv=from-parent-env\n",
        "`lake exe` must preserve argv order, whitespace, flag-like arguments, and inherited env"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "stderr=two words\n",
        "`lake exe` should not swallow or reroute native stderr"
    );
}

#[test]
fn lake_exe_preseeded_native_artifact_inherits_parent_environment() {
    let dir = tempfile::tempdir().expect("tempdir");
    let exe_name = "exe_env_smoke";
    write_lake_exe_project(dir.path(), exe_name);
    let artifact = write_env_native_artifact(dir.path(), exe_name);

    let output = Command::new(clean_path())
        .args(["lake", "exe", exe_name])
        .env("CLEAN_LAKE_EXE_ENV_SMOKE", "value with spaces=and=equals")
        .env("CLEAN_LAKE_EXE_EMPTY", "")
        .current_dir(dir.path())
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean lake exe {exe_name}: {err}"));

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
        "env=value with spaces=and=equals\nempty=set:\n",
        "`lake exe` should preserve inherited environment values, including empty variables"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "",
        "`lake exe` env smoke artifact should not emit stderr"
    );
}
