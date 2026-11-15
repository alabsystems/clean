// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake` never silently hands a Lean toolchain program to real Lean
//! (plan item `devsurface-lake-env-no-silent-lean`).
//!
//! Part (a): `clean lake env <program>` used to spawn whatever `lean`, `lake`,
//! `leanchecker`, `leanexport`, `leanc` (or another name in [`REFUSED`]) PATH
//! resolved: real Lean through elan, or inside aterm a reroute to a stale
//! Clean. An agent reading the output would report "checked by Clean". Each
//! test here puts a FAKE program of that name first on an explicit PATH; the
//! fake appends to a sentinel file, so "it did not run" is measured rather
//! than assumed. A control program with an ordinary name runs through the same
//! harness, so the harness can see a run.
//!
//! Part (b): `clean lake new` and `clean lake init` write a `lean-toolchain`
//! that elan cannot resolve to a leanprover toolchain. What elan does with it
//! is measured by `scripts/probe_lake_new_elan_toolchain.py`; this file pins
//! the bytes the binary writes. Nothing here executes elan or Lean.

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// Every Lean toolchain program `clean lake env` refuses, with what its
/// refusal ends with: Clean's own verb for `lean` (`clean lean`, decision
/// R74) and `lake` (`clean lake`), and for the rest that Clean ships none and
/// the verb to use instead.
const REFUSED: &[(&str, &str)] = &[
    (
        "lean",
        "Clean's own `lean` is `clean lean <FILE>`, with `lean`'s command line and exit rule; \
         run it directly. It reads `LEAN_PATH` as `lean` does, and `clean lake env` with no \
         command prints this workspace's.",
    ),
    (
        "lake",
        "Clean's own Lake is `clean lake <verb>`, for example `clean lake build`.",
    ),
    (
        "leanchecker",
        "Clean ships no `leanchecker`; use `clean olean replay <MODULE>` to re-check `.olean` \
         files with Clean's kernel.",
    ),
    (
        "leanexport",
        "Clean ships no `leanexport` and writes no lean4export exports; `clean olean replay \
         <MODULE>` re-checks the `.olean` files an export is made from, and `clean olean replay \
         --from-export <FILE>` checks an export.",
    ),
    (
        "lean4export",
        "Clean ships no `lean4export` and writes no lean4export exports; `clean olean replay \
         <MODULE>` re-checks the `.olean` files an export is made from, and `clean olean replay \
         --from-export <FILE>` checks an export.",
    ),
    (
        "leanc",
        "Clean ships no `leanc`; use `clean run <FILE> --decl main` to compile, link and run a \
         program with Clean.",
    ),
    (
        "leanmake",
        "Clean ships no `leanmake`; use `clean lake build`.",
    ),
    (
        "leanpkg",
        "Clean ships no `leanpkg`; use `clean lake <verb>`, for example `clean lake build`.",
    ),
    (
        "leanir",
        "Clean ships no `leanir`; use `clean compile <FILE> --decl <NAME> --emit c` to emit C \
         for a declaration with Clean, or `clean lake build` to build a package's modules.",
    ),
];

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// The exact refusal `clean lake env` prints for `given` (the program as the
/// caller spelled it) whose basename is the toolchain program `name`.
fn expected_refusal(given: &str, name: &str, hint: &str) -> String {
    format!(
        "Error: clean lake env refuses to run `{given}`: `{name}` is a Lean toolchain \
         program, so it could run real Lean or a stale reroute rather than Clean. {hint}\n"
    )
}

struct Harness {
    _root: tempfile::TempDir,
    bin: PathBuf,
    project: PathBuf,
    sentinel: PathBuf,
}

impl Harness {
    fn new() -> Self {
        let root = tempfile::tempdir().expect("tempdir");
        let bin = root.path().join("fakebin");
        let project = root.path().join("project");
        fs::create_dir(&bin).expect("create fake bin dir");
        fs::create_dir(&project).expect("create project dir");
        fs::write(
            project.join("lakefile.lean"),
            "import Lake\nopen Lake DSL\n\npackage noSilentLean where\n  version := \"0.1.0\"\n",
        )
        .expect("write lakefile.lean");
        let sentinel = root.path().join("sentinel");
        Self {
            _root: root,
            bin,
            project,
            sentinel,
        }
    }

    /// A fake program on the harness PATH that appends to the sentinel.
    fn install_fake(&self, name: &str) -> PathBuf {
        let path = self.bin.join(name);
        fs::write(
            &path,
            format!(
                "#!/bin/sh\nprintf '%s %s\\n' \"$0\" \"$*\" >> '{}'\necho 'FAKE {name} ran'\n",
                self.sentinel.display()
            ),
        )
        .expect("write fake program");
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).expect("chmod fake");
        path
    }

    fn path_var(&self) -> String {
        format!("{}:/usr/bin:/bin", self.bin.display())
    }

    fn lake_env(&self, dir: &Path, command: &[&str]) -> Output {
        let dir = dir.to_str().expect("utf-8 temp path");
        let mut args = vec!["lake", "--dir", dir, "env"];
        args.extend_from_slice(command);
        Command::new(clean_path())
            .args(&args)
            .env("PATH", self.path_var())
            .current_dir(&self.project)
            .output()
            .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
    }
}

fn describe(output: &Output) -> String {
    format!(
        "status={:?}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

#[test]
fn test_lake_env_lean_toolchain_program_on_path_is_refused_by_name_and_never_runs() {
    for (name, hint) in REFUSED {
        let harness = Harness::new();
        harness.install_fake(name);
        let output = harness.lake_env(&harness.project, &[name, "--version"]);

        assert!(
            !harness.sentinel.exists(),
            "`clean lake env {name} --version` ran the fake `{name}` first on PATH \
             (sentinel: {:?}); {}",
            fs::read_to_string(&harness.sentinel).unwrap_or_default(),
            describe(&output)
        );
        assert_eq!(
            output.status.code(),
            Some(1),
            "`clean lake env {name}` must refuse; {}",
            describe(&output)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "",
            "a refusal prints nothing on stdout; {}",
            describe(&output)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            expected_refusal(name, name, hint),
            "`clean lake env {name}` must refuse by name, naming the Clean verb"
        );
    }
}

#[test]
fn test_lake_env_lean_toolchain_program_by_explicit_path_is_refused() {
    for (name, hint) in REFUSED {
        let harness = Harness::new();
        let fake = harness.install_fake(name);
        let given = fake.to_str().expect("utf-8 temp path");
        let output = harness.lake_env(&harness.project, &[given, "--version"]);

        assert!(
            !harness.sentinel.exists(),
            "`clean lake env {given}` ran the fake by its path; {}",
            describe(&output)
        );
        assert_eq!(output.status.code(), Some(1), "{}", describe(&output));
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            expected_refusal(given, name, hint),
            "the refusal keys on the program's basename, wherever it lives"
        );
    }
}

#[test]
fn test_lake_env_lean_toolchain_program_outside_a_workspace_is_refused() {
    // `lake env` also runs tools outside a Lake project; the refusal does not
    // depend on a workspace loading.
    let harness = Harness::new();
    harness.install_fake("lean");
    let outside = harness
        .bin
        .parent()
        .expect("temp root")
        .join("not-a-project");
    fs::create_dir(&outside).expect("create non-project dir");
    let output = harness.lake_env(&outside, &["lean", "--version"]);

    assert!(!harness.sentinel.exists(), "{}", describe(&output));
    assert_eq!(output.status.code(), Some(1), "{}", describe(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        expected_refusal("lean", "lean", REFUSED[0].1),
    );
}

#[test]
fn test_lake_env_control_program_on_the_same_path_runs() {
    // The control: an ordinary program name on the same PATH runs, so the
    // harness above can see a run and its "sentinel absent" is not vacuous.
    let harness = Harness::new();
    harness.install_fake("fake-tool");
    let output = harness.lake_env(&harness.project, &["fake-tool", "--version"]);

    assert!(output.status.success(), "{}", describe(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "FAKE fake-tool ran\n"
    );
    let sentinel = fs::read_to_string(&harness.sentinel).expect("the control fake ran");
    assert_eq!(
        sentinel,
        format!("{} --version\n", harness.bin.join("fake-tool").display())
    );
}

/// The `lean-toolchain` the scaffolds write. A bare name: elan reads it as a
/// custom toolchain called `clean` when one is linked, and otherwise as the
/// release `leanprover/lean4:clean`, which does not exist, so it refuses
/// loudly instead of falling back to its default. See
/// `scripts/probe_lake_new_elan_toolchain.py` and its committed report.
const SCAFFOLD_TOOLCHAIN: &str = "clean\n";

#[test]
fn test_lake_new_writes_a_toolchain_elan_cannot_resolve_to_lean() {
    let root = tempfile::tempdir().expect("tempdir");
    let output = Command::new(clean_path())
        .args(["lake", "new", "probe_proj"])
        .env("PATH", "/usr/bin:/bin")
        .current_dir(root.path())
        .output()
        .expect("run clean lake new");
    assert!(output.status.success(), "{}", describe(&output));

    let toolchain = fs::read_to_string(root.path().join("probe_proj/lean-toolchain"))
        .expect("`clean lake new` writes lean-toolchain");
    assert_eq!(toolchain, SCAFFOLD_TOOLCHAIN);
}

#[test]
fn test_lake_init_writes_a_toolchain_elan_cannot_resolve_to_lean() {
    let root = tempfile::tempdir().expect("tempdir");
    let dir = root.path().to_str().expect("utf-8 temp path");
    let output = Command::new(clean_path())
        .args(["lake", "--dir", dir, "init", "probe_init"])
        .env("PATH", "/usr/bin:/bin")
        .current_dir(root.path())
        .output()
        .expect("run clean lake init");
    assert!(output.status.success(), "{}", describe(&output));

    let toolchain = fs::read_to_string(root.path().join("lean-toolchain"))
        .expect("`clean lake init` writes lean-toolchain");
    assert_eq!(toolchain, SCAFFOLD_TOOLCHAIN);
}
