// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Access to a Lean toolchain OTHER than the workspace pin, for tests that
//! measure Clean against a Lean version it supports as a second target
//! (trust-ir's operational semantics are Lean 4.8.0 + lake; Trust's default-on
//! Lean↔Clean bridge gate replays them through Clean's kernel). Included with
//! `#[path]` by the tests that need it.
//!
//! The pinned toolchain is a hard requirement
//! (`clean_olean::test_support::PINNED_LEAN_REQUIRED`): a checkout builds
//! against it. A secondary toolchain is not, so a test that needs one and
//! cannot find it must neither pass nor fail silently. It [`skip_unmeasured`]s:
//! one verdict line `<GATE>_GATE=skipped:<reason>` written straight to the
//! process's stderr, which libtest does not capture, and which
//! `scripts/verify_runner.py` (`_SKIPPED_VERDICT_RE`) records as SKIPPED —
//! UNKNOWN, never GREEN. The fail-closed switch named with it turns the skip
//! into a failure, for the lanes that must measure.
//!
//! Resolution is `clean_olean::installed_lean_lib_path`: the toolchain's exact
//! elan directory under `$ELAN_HOME` or `~/.elan`, never another version, and
//! never an `elan` invocation (which would install it).

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

/// An installed Lean toolchain, resolved by its exact name.
#[derive(Debug, Clone)]
pub struct InstalledLean {
    /// The version half of the name (`v4.8.0`): the fixture directory
    /// `tests/fixtures/lean/<version>` and the canonical-fold world
    /// `lean-<version>` are named by it.
    pub version: String,
    /// `<toolchain>/lib/lean`, holding `Init/Prelude.olean`.
    pub lib: PathBuf,
    /// `<toolchain>/bin/lean`.
    pub bin: PathBuf,
}

/// Resolve `toolchain` (`leanprover/lean4:v4.8.0`) when it is installed with
/// both its standard library and its `lean` binary; `None` otherwise.
pub fn installed_lean(toolchain: &str) -> Option<InstalledLean> {
    let lib = clean_olean::installed_lean_lib_path(toolchain)?;
    let bin = lib.parent()?.parent()?.join("bin").join("lean");
    if !bin.is_file() {
        return None;
    }
    let version = toolchain
        .rsplit_once(':')
        .map_or(toolchain, |(_, version)| version)
        .to_string();
    Some(InstalledLean { version, lib, bin })
}

/// Report that a test measured nothing because a prerequisite is absent.
///
/// Writes `\n<gate>_GATE=skipped:<reason>\n` to the real stderr (bypassing
/// libtest's capture, so the line survives a passing test) and returns, so the
/// caller returns without asserting anything. When the environment variable
/// `require_env` is set, PANICS instead: the lane asked for a measurement.
///
/// `gate` must be an upper-case identifier and `reason` must not contain
/// whitespace — the shape `scripts/verify_runner.py` parses.
pub fn skip_unmeasured(gate: &str, reason: &str, require_env: &str) {
    assert!(
        gate.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            && !reason.is_empty()
            && !reason.contains(char::is_whitespace),
        "malformed skip verdict `{gate}` / `{reason}`"
    );
    if std::env::var_os(require_env).is_some() {
        panic!("{gate}: prerequisite absent ({reason}) and {require_env} demands a measurement");
    }
    // One `write_all` of the whole line: an unbuffered `writeln!` issues one
    // write per format fragment, and libtest's own stdout lines (other test
    // threads) interleave between them in a shared log — measured, it split a
    // verdict line in two.
    let line = format!("\n{gate}_GATE=skipped:{reason}\n");
    let mut stderr = std::io::stderr().lock();
    let _ = stderr.write_all(line.as_bytes());
    let _ = stderr.flush();
}

/// Compile the one-module fixture `tests/fixtures/lean/<version>/<family>/
/// <module>.lean` with `lean`'s own binary into a fresh temporary directory
/// (`lean --root . -o <module>.olean <module>.lean`, the pinned fixture
/// recipe's compile step, with the directory as cwd and `LEAN_PATH`) and
/// return it; the `.olean` is a build product, never checked in. Panics with
/// Lean's output when the compile fails.
pub fn compile_fixture(lean: &InstalledLean, family: &str, module: &str) -> tempfile::TempDir {
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(&lean.version)
        .join(family)
        .join(format!("{module}.lean"));
    let dir = tempfile::tempdir().expect("temporary fixture directory");
    let lean_file = format!("{module}.lean");
    let olean_file = format!("{module}.olean");
    std::fs::copy(&source, dir.path().join(&lean_file))
        .unwrap_or_else(|e| panic!("copy {}: {e}", source.display()));
    let output = Command::new(&lean.bin)
        .current_dir(dir.path())
        .env("LEAN_PATH", dir.path())
        .args(["--root", ".", "-o", olean_file.as_str(), lean_file.as_str()])
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.bin.display()));
    assert!(
        output.status.success(),
        "`{} -o {olean_file} {lean_file}` failed with {}\n--- stdout ---\n{}\n--- stderr ---\n{}",
        lean.bin.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    dir
}
