// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native executable smoke for target-local Lake `srcDir`.
//!
//! The native artifact is pre-seeded so the test isolates Lake workspace
//! module lookup from Lean-level native code generation.

#![cfg(unix)]

mod support;

use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn write_target_src_dir_project(dir: &Path, exe_name: &str) {
    fs::write(
        dir.join("lakefile.lean"),
        format!(
            r#"import Lake
open Lake DSL

package targetSrcDirSmoke where
  version := "0.1.0"

lean_exe {exe_name} where
  root := `Main
  srcDir := "exe_src"
"#
        ),
    )
    .expect("write lakefile.lean");

    let src_dir = dir.join("exe_src");
    fs::create_dir(&src_dir).expect("create executable srcDir");
    fs::write(src_dir.join("Main.lean"), "def main : IO Unit := pure ()\n")
        .expect("write target-local Main.lean");
}

fn write_native_artifact(dir: &Path, exe_name: &str) -> PathBuf {
    let artifact = dir.join(".lake/build/bin").join(exe_name);
    fs::create_dir_all(artifact.parent().expect("artifact parent")).expect("create artifact dir");
    symlink("/bin/pwd", &artifact).expect("symlink signed native artifact");
    support::write_fresh_source_closure_sidecar(dir, exe_name, &["exe_src/Main.lean"]);
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
fn lake_exe_and_run_resolve_root_module_from_target_src_dir_before_native_handoff() {
    let dir = tempfile::tempdir().expect("tempdir");
    let project_dir = dir.path().join("target_srcdir_smoke");
    fs::create_dir(&project_dir).expect("create project dir");
    let exe_name = "target_srcdir_smoke";
    write_target_src_dir_project(&project_dir, exe_name);
    let artifact = write_native_artifact(&project_dir, exe_name);
    let expected_cwd = format!(
        "{}\n",
        fs::canonicalize(&project_dir)
            .expect("canonical project dir")
            .display()
    );
    let project_arg = project_dir
        .to_str()
        .expect("temp project path should be valid UTF-8");

    for (label, args) in [
        ("exe", vec!["lake", "--dir", project_arg, "exe", exe_name]),
        ("run", vec!["lake", "--dir", project_arg, "run", exe_name]),
    ] {
        let output = run_clean(&args, dir.path());
        assert!(
            output.status.success(),
            "`clean lake {label}` should find root module Main under executable srcDir before executing {}; status={:?}; stdout={}; stderr={}",
            artifact.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            expected_cwd,
            "`lake {label}` should execute the pre-seeded native artifact after resolving target srcDir"
        );
    }
}
