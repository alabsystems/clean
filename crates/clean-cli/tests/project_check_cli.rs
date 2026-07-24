// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-boundary checks for `clean project check`.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

use serde_json::Value;

const CLEAN_PROJECT_CHECK_BIN_ENV: &str = "CLEAN_PROJECT_CHECK_BIN";
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
    if let Some(binary) = env::var_os(CLEAN_PROJECT_CHECK_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_PROJECT_CHECK_BIN_ENV} points to {}, but it is not a file",
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
        .unwrap_or_else(|err| panic!("failed to run Clean {args:?}: {err}"))
}

fn parse_json(args: &[&str], output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "Clean {args:?} did not emit JSON on stdout: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[test]
fn project_check_json_aggregates_project_local_imports() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("Good.lean"),
        "def project_check_id (x : Nat) : Nat := x\n\
         theorem project_check_true : True := True.intro\n",
    )
    .expect("write good fixture");
    fs::write(
        dir.path().join("UsesGood.lean"),
        "import Good\n\
         theorem project_check_uses_good : True := True.intro\n",
    )
    .expect("write uses-good fixture");
    // Build artifacts under .lake/ must be skipped by the source scan.
    fs::create_dir_all(dir.path().join(".lake/build/lib/lean")).expect("build dir");
    fs::write(
        dir.path().join(".lake/build/lib/lean/Ignored.lean"),
        "theorem ignored : False := by\n  rfl\n",
    )
    .expect("write ignored build fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    let report = parse_json(&args, &output);

    assert_eq!(report["schema_version"], "Clean-project-check-report-v1");
    assert_eq!(report["semantic_authority"]["engine"], "Clean");
    assert_eq!(report["semantic_authority"]["external_olean"], false);
    assert_eq!(report["summary"]["modules_found"], 2);

    let modules = report["modules"].as_array().expect("modules");
    let uses_good = modules
        .iter()
        .find(|module| module["module"] == "UsesGood")
        .expect("UsesGood module report");
    assert_eq!(uses_good["imports"][0]["module"], "Good");
    assert_eq!(uses_good["imports"][0]["project_local"], true);
}

#[test]
fn project_check_blocks_project_local_import_cycles() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("A.lean"),
        "import B\n\
         theorem cycle_a : True := True.intro\n",
    )
    .expect("write A fixture");
    fs::write(
        dir.path().join("B.lean"),
        "import A\n\
         theorem cycle_b : True := True.intro\n",
    )
    .expect("write B fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    assert!(
        !output.status.success(),
        "import cycle should block project authority\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = parse_json(&args, &output);
    assert_eq!(report["status"], "fail");
    let cycle_blocker_count = report["authority_blockers"]
        .as_array()
        .expect("authority blockers")
        .iter()
        .filter(|blocker| blocker["kind"] == "project_import_cycle")
        .count();
    assert!(
        cycle_blocker_count >= 2,
        "expected both cycle members to be reported; got {cycle_blocker_count}"
    );
}

#[test]
fn project_check_blocks_external_imports_instead_of_using_lean_authority() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("UsesExternal.lean"),
        "import Mathlib\n\
         theorem project_external_import_ok : True := True.intro\n",
    )
    .expect("write fixture");

    let project = dir.path().to_str().expect("utf8 tempdir");
    let args = ["project", "check", project, "--json"];
    let output = run_clean(&args);
    assert!(
        !output.status.success(),
        "external import should block project authority\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report = parse_json(&args, &output);

    assert_eq!(report["status"], "fail");
    assert_eq!(report["semantic_authority"]["lean4"], false);
    assert_eq!(report["semantic_authority"]["lake"], false);
    assert_eq!(report["semantic_authority"]["mathlib"], false);
    assert!(report["authority_blockers"]
        .as_array()
        .expect("authority blockers")
        .iter()
        .any(|blocker| blocker["kind"] == "external_import"
            && blocker["message"]
                .as_str()
                .expect("message")
                .contains("Mathlib")));
}
