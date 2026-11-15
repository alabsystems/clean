// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `lake env <cmd>` refuses a Lean toolchain program before spawning it (plan
//! item `devsurface-lake-env-no-silent-lean`, part (a)).
//!
//! Each case names a FAKE program by its explicit path, so nothing here looks
//! anything up on PATH and nothing real can run. The fake appends to a
//! sentinel file, so "it did not run" is measured. The controls run fakes
//! with other names through the same handoff, so the sentinel can show a run.

use super::lake_env_command;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

/// A temp dir holding one fake program and the sentinel it writes.
struct Fake {
    dir: tempfile::TempDir,
    program: PathBuf,
    sentinel: PathBuf,
}

impl Fake {
    /// One temp dir per fake: on a case-insensitive filesystem `LEAN` and
    /// `lean` are one file.
    fn new(file_name: &str) -> Self {
        let dir = tempfile::tempdir().expect("tempdir");
        let program = dir.path().join(file_name);
        let sentinel = dir.path().join("sentinel");
        fs::write(
            &program,
            format!(
                "#!/bin/sh\nprintf '%s\\n' \"$*\" >> '{}'\n",
                sentinel.display()
            ),
        )
        .expect("write fake program");
        fs::set_permissions(&program, fs::Permissions::from_mode(0o755)).expect("chmod fake");
        Self {
            dir,
            program,
            sentinel,
        }
    }

    fn run(&self) -> anyhow::Result<()> {
        let program = self.program.to_str().expect("utf-8 temp path").to_string();
        lake_env_command(&[program, "--version".to_string()], self.dir.path(), false)
    }
}

fn sentinel_text(sentinel: &Path) -> String {
    fs::read_to_string(sentinel).unwrap_or_default()
}

#[test]
fn test_lake_env_command_refuses_lean_toolchain_programs_by_basename() {
    for (file_name, name, verb) in [
        ("lean", "lean", "`clean lean <FILE>`"),
        ("LEAN", "lean", "`clean lean <FILE>`"),
        ("Lean.exe", "lean", "`clean lean <FILE>`"),
        ("lake", "lake", "`clean lake <verb>`"),
        (
            "leanchecker",
            "leanchecker",
            "`clean olean replay <MODULE>`",
        ),
        ("leanexport", "leanexport", "`clean olean replay <MODULE>`"),
        (
            "lean4export",
            "lean4export",
            "`clean olean replay <MODULE>`",
        ),
        ("leanc", "leanc", "`clean run <FILE> --decl main`"),
        ("LEANC.EXE", "leanc", "`clean run <FILE> --decl main`"),
        ("leanmake", "leanmake", "`clean lake build`"),
        ("leanpkg", "leanpkg", "`clean lake <verb>`"),
        (
            "leanir",
            "leanir",
            "`clean compile <FILE> --decl <NAME> --emit c`",
        ),
        (
            "LEANIR.exe",
            "leanir",
            "`clean compile <FILE> --decl <NAME> --emit c`",
        ),
    ] {
        let fake = Fake::new(file_name);
        let result = fake.run();
        assert!(
            !fake.sentinel.exists(),
            "`lake env {file_name}` ran the fake: {:?}",
            sentinel_text(&fake.sentinel)
        );
        let err = result.expect_err("a Lean toolchain program must be refused");
        let message = err.to_string();
        let expected_head = format!(
            "clean lake env refuses to run `{}`: `{name}` is a Lean toolchain program, so it \
             could run real Lean or a stale reroute rather than Clean. ",
            fake.program.display()
        );
        assert!(
            message.starts_with(&expected_head),
            "`{file_name}`: the refusal names the program\n got: {message}\nwant: {expected_head}…"
        );
        assert!(
            message.contains(verb),
            "`{file_name}`: the refusal names {verb}: {message}"
        );
    }
}

#[test]
fn test_lake_env_command_runs_other_programs_through_the_same_handoff() {
    for file_name in ["lean4", "fake-tool", "elan-like"] {
        let fake = Fake::new(file_name);
        fake.run()
            .unwrap_or_else(|err| panic!("`lake env {file_name}` must run: {err:#}"));
        assert_eq!(
            sentinel_text(&fake.sentinel),
            "--version\n",
            "the control `{file_name}` ran with its argument"
        );
    }
}
