// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean extract --backend rust` compiles its differential battery only with
//! an admitted Trust compiler -- the `trustc` beside the running `clean`, or
//! the one `CLEAN_NATIVE_DECIDE_TRUSTC` names -- and refuses with
//! `E_RUST_TOOLCHAIN`, writing nothing, without one.
//!
//! This drives the REAL `clean` binary, because the production entry point
//! (`handle_extract_command`, which resolves the process-wide oracle compiler)
//! is the one caller the in-crate tests cannot reach: they all hand the
//! compiler in. Before the fix this lane ran the bare name `trustc` from PATH,
//! or whatever `CLEAN_RUSTC` / `$RUSTC` named. Every run below puts
//! `trustc`/`rustc` impostors first on PATH and names one through `RUSTC` and
//! `CLEAN_RUSTC`, with `RUSTUP_TOOLCHAIN=stable`; the impostors log every
//! invocation, so a run of any of them is seen from outside the process.

#![cfg(unix)]

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The variable that names the oracle compiler
/// (`clean_elab::oracle_compiler::TRUSTC_ENV`). Spelled out, with no import of
/// the resolver's API, so this file also builds -- and fails -- against a
/// `clean` from before the resolver existed.
const TRUSTC_ENV: &str = "CLEAN_NATIVE_DECIDE_TRUSTC";

/// A declaration the Rust lane extracts (the in-crate Rust-backend tests use
/// the same one).
const SOURCE: &str = "def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b\n";

/// A scratch directory: the `clean` binary to run (a hard link of this
/// build's, optionally beside a `trustc`), the impostors, the source and the
/// output directory the extraction would install.
struct Scratch {
    dir: tempfile::TempDir,
}

impl Scratch {
    /// A hard link of this build's `clean` in a directory of its own, with a
    /// `trustc` symlink beside it when `sibling` names one.
    fn new(sibling: Option<&Path>) -> Self {
        let dir = tempfile::tempdir_in(env!("CARGO_TARGET_TMPDIR")).expect("scratch dir");
        let bin = dir.path().join("bin");
        std::fs::create_dir(&bin).expect("bin dir");
        let clean = Path::new(env!("CARGO_BIN_EXE_clean"));
        if std::fs::hard_link(clean, bin.join("clean")).is_err() {
            std::fs::copy(clean, bin.join("clean")).expect("copy clean");
        }
        if let Some(trustc) = sibling {
            std::os::unix::fs::symlink(trustc, bin.join("trustc")).expect("sibling trustc");
        }
        let impostors = dir.path().join("impostors");
        std::fs::create_dir(&impostors).expect("impostor dir");
        let log = dir.path().join("impostors.log");
        for name in ["trustc", "rustc"] {
            let script = impostors.join(name);
            std::fs::write(
                &script,
                format!(
                    "#!/bin/sh\n\
                     printf '%s %s\\n' \"$0\" \"$*\" >> '{}'\n\
                     printf 'binary: trustc\\ncommit-hash: {}\\ntrust: 0.1.0\\n'\n",
                    log.display(),
                    "0".repeat(40)
                ),
            )
            .expect("write impostor");
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755))
                .expect("chmod +x");
        }
        std::fs::write(dir.path().join("affine.lean"), SOURCE).expect("write source");
        Self { dir }
    }

    fn impostor(&self) -> PathBuf {
        self.dir.path().join("impostors/trustc")
    }

    fn out(&self) -> PathBuf {
        self.dir.path().join("out")
    }

    /// Every impostor invocation, one per line; empty when none ran.
    fn impostor_runs(&self) -> String {
        std::fs::read_to_string(self.dir.path().join("impostors.log")).unwrap_or_default()
    }

    /// `clean extract affine.lean --decl affineU --backend rust`, in the
    /// hostile environment above plus `extra`.
    fn extract(&self, extra: &[(&str, OsString)]) -> Output {
        let mut path = self.dir.path().join("impostors").into_os_string();
        path.push(":/usr/bin:/bin");
        let mut command = Command::new(self.dir.path().join("bin/clean"));
        command
            .arg("extract")
            .arg(self.dir.path().join("affine.lean"))
            .args(["--decl", "affineU", "--backend", "rust", "--out"])
            .arg(self.out())
            .env_remove(TRUSTC_ENV)
            .env("PATH", path)
            .env("RUSTC", self.impostor())
            .env("CLEAN_RUSTC", self.impostor())
            .env("RUSTUP_TOOLCHAIN", "stable");
        for (key, value) in extra {
            command.env(key, value);
        }
        command.output().expect("launch clean")
    }
}

/// This toolchain's `trustc`: the one beside `$CARGO` (Targo exports it to
/// tests), else beside the Targo that built this test. `clean` admits it by
/// what it is; this test only needs to find it.
fn toolchain_trustc() -> PathBuf {
    let cargo =
        std::env::var_os("CARGO").map_or_else(|| PathBuf::from(env!("CARGO")), PathBuf::from);
    let trustc = cargo
        .canonicalize()
        .unwrap_or_else(|err| panic!("{cargo:?}: {err}"))
        .with_file_name("trustc");
    assert!(
        trustc.is_file(),
        "these tests need the Trust toolchain's trustc beside {cargo:?}"
    );
    trustc
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// A refused extraction: nonzero, `E_RUST_TOOLCHAIN` naming the variable and
/// `reason`, nothing installed, and no impostor run.
fn assert_refused(scratch: &Scratch, output: &Output, reason: &str) {
    let err = stderr(output);
    assert!(!output.status.success(), "extraction succeeded:\n{err}");
    for needle in ["E_RUST_TOOLCHAIN", TRUSTC_ENV, reason] {
        assert!(err.contains(needle), "missing {needle:?} in:\n{err}");
    }
    assert!(
        !scratch.out().exists(),
        "a refused extraction wrote its output"
    );
    assert_eq!(scratch.impostor_runs(), "", "an impostor compiler ran");
}

/// NEGATIVE CONTROL: a `clean` with no `trustc` beside it and no setting
/// refuses -- it does not fall back to PATH, `$RUSTC` or `CLEAN_RUSTC`.
#[test]
fn without_an_admitted_trustc_extraction_refuses() {
    let scratch = Scratch::new(None);
    let output = scratch.extract(&[]);
    assert_refused(&scratch, &output, "no oracle compiler");
}

/// NEGATIVE CONTROL: a named compiler is admitted by what it is: a script
/// that prints Trust's identity is refused unrun, and nothing else is tried.
#[test]
fn a_named_script_is_refused_and_extraction_refuses() {
    let scratch = Scratch::new(None);
    let output = scratch.extract(&[(TRUSTC_ENV, scratch.impostor().into_os_string())]);
    assert_refused(&scratch, &output, "not a native executable");
}

/// POSITIVE: the `trustc` beside the running `clean` compiles the battery,
/// and the extraction installs a module whose differential PASSED -- with the
/// impostors still first on PATH and named by `RUSTC` / `CLEAN_RUSTC`.
#[test]
fn the_sibling_trustc_compiles_the_battery() {
    let toolchain = toolchain_trustc();
    let scratch = Scratch::new(Some(&toolchain));
    let output = scratch.extract(&[]);
    assert!(
        output.status.success(),
        "extraction beside {} failed:\n{}",
        toolchain.display(),
        stderr(&output)
    );
    let manifest = std::fs::read_to_string(scratch.out().join("manifest.json")).expect("manifest");
    for field in ["\"backend\": \"rust\"", "\"differential\": \"PASSED"] {
        assert!(
            manifest.contains(field),
            "no {field} in the manifest:\n{manifest}"
        );
    }
    assert!(scratch.out().join("affineU.rs").is_file(), "no module");
    assert_eq!(scratch.impostor_runs(), "", "an impostor compiler ran");
}
