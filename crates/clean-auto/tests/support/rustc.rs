// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Command;

/// Resolve the compiler selected for the enclosing Cargo/Targo invocation.
///
/// Targo does not export `RUSTC` to test processes on every platform. Asking
/// rustup from the workspace preserves its toolchain override and avoids
/// feeding Trust-built metadata to an ABI-incompatible host `rustc` on PATH.
pub fn cargo_rustc() -> PathBuf {
    if let Some(rustc) = std::env::var_os("RUSTC") {
        return rustc.into();
    }

    let rustup_name = format!("rustup{}", std::env::consts::EXE_SUFFIX);
    let mut rustup_candidates = Vec::<OsString>::new();
    if let Some(cargo_home) = std::env::var_os("CARGO_HOME") {
        rustup_candidates.push(
            PathBuf::from(cargo_home)
                .join("bin")
                .join(&rustup_name)
                .into_os_string(),
        );
    }
    if let Some(home) = std::env::var_os("HOME") {
        rustup_candidates.push(
            PathBuf::from(home)
                .join(".cargo/bin")
                .join(&rustup_name)
                .into_os_string(),
        );
    }
    if let Some(home) = std::env::var_os("USERPROFILE") {
        rustup_candidates.push(
            PathBuf::from(home)
                .join(".cargo/bin")
                .join(&rustup_name)
                .into_os_string(),
        );
    }
    rustup_candidates.push(rustup_name.into());

    for rustup in rustup_candidates {
        let Ok(output) = Command::new(rustup).args(["which", "rustc"]).output() else {
            continue;
        };
        if !output.status.success() {
            continue;
        }

        let compiler = String::from_utf8_lossy(&output.stdout);
        let compiler = compiler.trim();
        if !compiler.is_empty() {
            return compiler.into();
        }
    }

    panic!("unable to resolve Cargo/Targo's selected rustc through RUSTC or rustup")
}
