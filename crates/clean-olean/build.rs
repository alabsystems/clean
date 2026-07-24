// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for clean-olean.
//!
//! Checks for a Lean 4 installation at compile time and emits a visible
//! warning when one is not found. Without Lean 4, 168 of 195 integration
//! tests silently skip (they return early and report `ok` with zero
//! assertions). This build-time warning makes the skip behavior visible.
//!
//! See: <https://github.com/alabsystems/clean/issues/1257>

use std::path::{Path, PathBuf};

fn find_lean_lib_path() -> Option<PathBuf> {
    // Check LEAN_PATH environment variable
    if let Ok(val) = std::env::var("LEAN_PATH") {
        for path in std::env::split_paths(&val) {
            if path.join("Init/Prelude.olean").exists() {
                return Some(path);
            }
        }
    }

    // Check elan toolchains
    for var in ["HOME", "USERPROFILE"] {
        let Ok(home) = std::env::var(var) else {
            continue;
        };

        let elan_path = Path::new(&home).join(".elan/toolchains");
        let Ok(entries) = std::fs::read_dir(&elan_path) else {
            continue;
        };

        for entry in entries.flatten() {
            let name = entry.file_name();
            if name.to_string_lossy().contains("lean4") {
                let lib_path = entry.path().join("lib/lean");
                if lib_path.join("Init/Prelude.olean").exists() {
                    return Some(lib_path);
                }
            }
        }
    }

    None
}

fn main() {
    // Re-run when relevant environment changes
    println!("cargo:rerun-if-env-changed=LEAN_PATH");
    println!("cargo:rerun-if-env-changed=MATHLIB_PATH");
    println!("cargo:rerun-if-env-changed=HOME");

    if find_lean_lib_path().is_none() {
        println!(
            "cargo:warning=Lean 4 not found: 168 of 195 olean integration tests will silently \
             skip (86% of test suite). Install via `curl -sSf https://raw.githubusercontent.com/\
             leanprover/elan/master/elan-init.sh | sh` or set LEAN_PATH. See issue #1257."
        );
    }
}
