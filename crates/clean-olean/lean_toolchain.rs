// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deterministic discovery of Clean's repository-pinned Lean toolchain.
//!
//! This file is shared by `build.rs` and the `clean-olean` library. Resolution
//! is anchored at `CARGO_MANIFEST_DIR`, never the caller's current directory,
//! and never selects an arbitrary entry from `~/.elan/toolchains`.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

pub(crate) const PINNED_LEAN_LIB_ENV: &str = "CLEAN_OLEAN_PINNED_LEAN_LIB";
pub(crate) const PINNED_LEAN_TOOLCHAIN_ENV: &str = "CLEAN_OLEAN_PINNED_LEAN_TOOLCHAIN";

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PinnedLean {
    pub(crate) toolchain: String,
    pub(crate) lib_path: PathBuf,
}

fn workspace_root(manifest_dir: &Path) -> Result<PathBuf, String> {
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            format!(
                "clean-olean manifest directory has no workspace root: {}",
                manifest_dir.display()
            )
        })
}

fn read_toolchain(manifest_dir: &Path) -> Result<(PathBuf, String), String> {
    let toolchain_file = workspace_root(manifest_dir)?.join("lean-toolchain");
    let raw = std::fs::read_to_string(&toolchain_file).map_err(|error| {
        format!(
            "cannot read pinned Lean toolchain file {}: {error}",
            toolchain_file.display()
        )
    })?;
    let toolchain = raw.trim();
    if toolchain.is_empty() || toolchain.chars().any(char::is_whitespace) {
        return Err(format!(
            "invalid pinned Lean toolchain in {}",
            toolchain_file.display()
        ));
    }
    Ok((toolchain_file, toolchain.to_string()))
}

fn elan_directory_name(toolchain: &str) -> Result<String, String> {
    if !toolchain.contains('/') || !toolchain.contains(':') {
        return Err(format!(
            "unsupported fully-qualified Lean toolchain name: {toolchain}"
        ));
    }
    Ok(toolchain.replace('/', "--").replacen(':', "---", 1))
}

fn valid_lean_lib(path: &Path) -> bool {
    path.join("Init/Prelude.olean").is_file()
}

fn direct_elan_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Some(root) = std::env::var_os("ELAN_HOME") {
        roots.push(PathBuf::from(root));
    }
    for home_var in ["HOME", "USERPROFILE"] {
        if let Some(home) = std::env::var_os(home_var) {
            let root = PathBuf::from(home).join(".elan");
            if !roots.contains(&root) {
                roots.push(root);
            }
        }
    }
    roots
}

fn resolve_via_elan(toolchain: &str) -> Result<PathBuf, String> {
    let elan: OsString = std::env::var_os("ELAN").unwrap_or_else(|| OsString::from("elan"));
    let output = Command::new(&elan)
        .args(["run", toolchain, "lean", "--print-prefix"])
        .output()
        .map_err(|error| format!("cannot execute {:?}: {error}", elan))?;
    if !output.status.success() {
        return Err(format!(
            "`elan run {toolchain} lean --print-prefix` failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let prefix = String::from_utf8(output.stdout)
        .map_err(|error| format!("Lean prefix is not UTF-8: {error}"))?;
    let lib_path = PathBuf::from(prefix.trim()).join("lib/lean");
    if !valid_lean_lib(&lib_path) {
        return Err(format!(
            "pinned Lean prefix has no Init/Prelude.olean: {}",
            lib_path.display()
        ));
    }
    Ok(lib_path)
}

pub(crate) fn resolve_pinned_lean(manifest_dir: &Path) -> Result<PinnedLean, String> {
    let (_, toolchain) = read_toolchain(manifest_dir)?;
    let directory_name = elan_directory_name(&toolchain)?;

    if let Some(explicit) = std::env::var_os(PINNED_LEAN_LIB_ENV) {
        let lib_path = PathBuf::from(explicit);
        let exact_directory = lib_path
            .parent()
            .and_then(Path::parent)
            .and_then(Path::file_name)
            .is_some_and(|name| name == directory_name.as_str());
        if exact_directory && valid_lean_lib(&lib_path) {
            return Ok(PinnedLean {
                toolchain,
                lib_path,
            });
        }
        return Err(format!(
            "{PINNED_LEAN_LIB_ENV} is not the pinned {directory_name} stdlib: {}",
            lib_path.display()
        ));
    }

    for root in direct_elan_roots() {
        let lib_path = root
            .join("toolchains")
            .join(&directory_name)
            .join("lib/lean");
        if valid_lean_lib(&lib_path) {
            return Ok(PinnedLean {
                toolchain,
                lib_path,
            });
        }
    }

    let lib_path = resolve_via_elan(&toolchain)?;
    Ok(PinnedLean {
        toolchain,
        lib_path,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const CHILD_ENV: &str = "CLEAN_OLEAN_EXTERNAL_CWD_PROBE";
    const MANIFEST_ENV: &str = "CLEAN_OLEAN_PROBE_MANIFEST_DIR";
    const EXPECTED_ENV: &str = "CLEAN_OLEAN_PROBE_EXPECTED_LIB";

    #[test]
    fn pinned_resolution_is_independent_of_external_caller_cwd() {
        if let Some(mode) = std::env::var_os(CHILD_ENV) {
            let manifest_dir =
                PathBuf::from(std::env::var_os(MANIFEST_ENV).expect("child manifest directory"));
            let expected =
                PathBuf::from(std::env::var_os(EXPECTED_ENV).expect("child expected library"));
            if mode == "wrong-explicit" {
                let error = resolve_pinned_lean(&manifest_dir)
                    .expect_err("wrong explicit ABI must not override the repository pin");
                assert!(
                    error.contains("is not the pinned"),
                    "unexpected rejection: {error}"
                );
            } else {
                let resolved = resolve_pinned_lean(&manifest_dir)
                    .expect("resolve pinned Lean from external cwd");
                assert_eq!(resolved.lib_path, expected);
            }
            return;
        }

        let temp = tempfile::tempdir().expect("temporary probe root");
        let workspace = temp.path().join("checkout");
        let manifest_dir = workspace.join("crates/clean-olean");
        let external_cwd = temp.path().join("external-caller");
        let elan_home = temp.path().join("elan");
        let expected = elan_home.join("toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean");
        let wrong = elan_home.join("toolchains/leanprover--lean4---v4.8.0/lib/lean");
        std::fs::create_dir_all(&manifest_dir).expect("fake manifest directory");
        std::fs::create_dir_all(expected.join("Init")).expect("fake pinned stdlib");
        std::fs::create_dir_all(wrong.join("Init")).expect("fake wrong-version stdlib");
        std::fs::create_dir_all(&external_cwd).expect("external caller directory");
        std::fs::write(
            workspace.join("lean-toolchain"),
            "leanprover/lean4:v4.30.0-rc2\n",
        )
        .expect("fake toolchain pin");
        std::fs::write(expected.join("Init/Prelude.olean"), b"fixture").expect("fake Prelude");
        std::fs::write(wrong.join("Init/Prelude.olean"), b"wrong fixture")
            .expect("fake wrong-version Prelude");

        let executable = std::env::current_exe().expect("current test executable");
        let output = Command::new(&executable)
            .args([
                "--exact",
                "lean_toolchain::tests::pinned_resolution_is_independent_of_external_caller_cwd",
                "--nocapture",
            ])
            .current_dir(&external_cwd)
            .env(CHILD_ENV, "1")
            .env(MANIFEST_ENV, &manifest_dir)
            .env(EXPECTED_ENV, &expected)
            .env("ELAN_HOME", &elan_home)
            .env_remove(PINNED_LEAN_LIB_ENV)
            .output()
            .expect("spawn external-cwd probe");
        assert!(
            output.status.success(),
            "external-cwd probe failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let wrong_output = Command::new(executable)
            .args([
                "--exact",
                "lean_toolchain::tests::pinned_resolution_is_independent_of_external_caller_cwd",
                "--nocapture",
            ])
            .current_dir(external_cwd)
            .env(CHILD_ENV, "wrong-explicit")
            .env(MANIFEST_ENV, manifest_dir)
            .env(EXPECTED_ENV, expected)
            .env("ELAN_HOME", elan_home)
            .env(PINNED_LEAN_LIB_ENV, wrong)
            .output()
            .expect("spawn wrong-explicit-path probe");
        assert!(
            wrong_output.status.success(),
            "wrong-explicit-path probe failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&wrong_output.stdout),
            String::from_utf8_lossy(&wrong_output.stderr)
        );
    }

    #[test]
    fn fully_qualified_pin_maps_to_exact_elan_directory() {
        assert_eq!(
            elan_directory_name("leanprover/lean4:v4.30.0-rc2").unwrap(),
            "leanprover--lean4---v4.30.0-rc2"
        );
    }
}
