// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native executable argv/cwd handoff smoke tests for `clean lake run`.
//!
//! The native artifact is a symlink to `/bin/sh` so the test exercises
//! Lake's process handoff without generating a temporary executable.

#![cfg(unix)]

mod support;

use std::fs;
use std::os::unix::fs::symlink;
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

package argvCwdSmoke where
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
    symlink("/bin/sh", &artifact).expect("symlink signed native artifact");
    support::write_fresh_source_closure_sidecar(dir, exe_name, &["Main.lean"]);
    artifact
}

fn run_clean(args: &[&str], cwd: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean with args {args:?}: {err}"))
}

#[test]
fn lake_run_and_exe_with_dir_preserve_native_artifact_argv_and_workspace_cwd() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("argv_cwd_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    let exe_name = "argv_cwd_smoke";
    write_lake_exe_project(&project_dir, exe_name);
    let artifact = symlink_native_shell_artifact(&project_dir, exe_name);
    let expected_cwd = fs::canonicalize(&project_dir)
        .expect("canonical project dir")
        .display()
        .to_string();
    let expected_stdout =
        format!("cwd={expected_cwd}\narg1=alpha\narg2=two words\narg3=--literal-flag\n");
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");
    let script = "printf 'cwd=%s\narg1=%s\narg2=%s\narg3=%s\n' \"$(pwd)\" \"$1\" \"$2\" \"$3\"";

    for (label, args) in [
        (
            "exe",
            [
                "lake",
                "--dir",
                project_arg,
                "exe",
                exe_name,
                "-c",
                script,
                "native-sh",
                "alpha",
                "two words",
                "--literal-flag",
            ],
        ),
        (
            "run",
            [
                "lake",
                "--dir",
                project_arg,
                "run",
                exe_name,
                "-c",
                script,
                "native-sh",
                "alpha",
                "two words",
                "--literal-flag",
            ],
        ),
    ] {
        let output = run_clean(&args, dir.path());
        assert!(
            output.status.success(),
            "`clean lake {label}` should execute {} with forwarded argv from the workspace root; status={:?}; stdout={}; stderr={}",
            artifact.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            expected_stdout,
            "`lake {label}` should preserve native argv and workspace cwd"
        );
    }
}
