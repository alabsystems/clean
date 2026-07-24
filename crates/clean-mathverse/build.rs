// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for clean-mathverse.
//!
//! Captures the building rustc/toolchain version into
//! `CLEAN_MATHVERSE_TOOLCHAIN_VERSION` so the
//! PARAGON incremental-import cache (`StampEnvFingerprint::toolchain`, folded
//! into every module's closure hash via `cache_key`) RE-KEYS on a toolchain
//! bump. Without this, `option_env!("CLEAN_MATHVERSE_TOOLCHAIN_VERSION")`
//! resolved to `None`
//! ("unknown") and a toolchain change did not invalidate cached verdicts — a
//! stale-reuse risk for a cache that is hit repeatedly across builds.
//!
//! Cargo sets `RUSTC` to the rustc the crate is compiled with; we query it for
//! its version string. If the query fails for any reason we leave the var unset
//! (the consumer falls back to "unknown", exactly as before).

fn main() {
    // Re-run when the toolchain changes.
    println!("cargo:rerun-if-env-changed=RUSTC");

    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    if let Ok(output) = std::process::Command::new(rustc).arg("--version").output() {
        if output.status.success() {
            let version = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !version.is_empty() {
                // e.g. "rustc 1.86.0 (05f9846f8 2025-03-31)"
                println!("cargo:rustc-env=CLEAN_MATHVERSE_TOOLCHAIN_VERSION={version}");
            }
        }
    }
}
