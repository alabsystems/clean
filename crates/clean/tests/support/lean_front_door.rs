// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for the `clean lean` front-door suites: run the real
//! `clean` binary as `lean` would be run, and read its exact bytes.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// Lean 4.8.0, as `CLEAN_LEAN_VERSION` names it.
pub const V4_8_0: &str = "4.8.0";
/// Lean 4.30.0-rc2.
pub const V4_30_0_RC2: &str = "4.30.0-rc2";

/// The `clean` binary under test.
pub fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// The repository's `tests/fixtures/lean_front_door`.
pub fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/lean_front_door")
}

/// A fresh scratch directory for one test (no `lean-toolchain` above it is
/// assumed: every call names the release explicitly).
pub fn scratch(test: &str) -> PathBuf {
    // Repeated labels can overlap across parallel tests (for example version-probe).
    // Give each call its own directory, retaining the existing PathBuf lifetime.
    let prefix = format!("clean-lean-front-door-{}-{test}-", std::process::id());
    tempfile::Builder::new()
        .prefix(&prefix)
        .tempdir()
        .expect("create scratch dir")
        .keep()
}

/// `clean lean <args>` in `dir`, modelling `release`, with no stdin.
pub fn lean(dir: &Path, release: &str, args: &[&str]) -> Output {
    lean_with_stdin(dir, release, args, None)
}

/// `clean lean <args>` with `stdin` piped in.
pub fn lean_with_stdin(dir: &Path, release: &str, args: &[&str], stdin: Option<&str>) -> Output {
    let mut command = Command::new(clean_path());
    command
        .arg("lean")
        .args(args)
        .current_dir(dir)
        .env("CLEAN_LEAN_VERSION", release)
        .env_remove("LEAN_PATH")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    match stdin {
        None => {
            command.stdin(Stdio::null());
            command.output().expect("spawn clean lean")
        }
        Some(text) => {
            use std::io::Write;
            command.stdin(Stdio::piped());
            let mut child = command.spawn().expect("spawn clean lean");
            child
                .stdin
                .take()
                .expect("stdin")
                .write_all(text.as_bytes())
                .expect("write stdin");
            child.wait_with_output().expect("wait clean lean")
        }
    }
}

/// The run's stdout as text.
pub fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

/// The run's stderr as text.
pub fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Assert the exact exit status and bytes of a run.
pub fn assert_run(output: &Output, code: i32, out: &str, err: &str) {
    assert_eq!(
        (output.status.code(), stdout(output), stderr(output)),
        (Some(code), out.to_owned(), err.to_owned()),
        "exit status, stdout, stderr"
    );
}

/// Write `source` to `dir/name`.
pub fn write(dir: &Path, name: &str, source: &str) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write fixture");
    path
}
