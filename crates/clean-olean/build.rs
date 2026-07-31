// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for clean-olean.
//!
//! Resolves the exact Lean toolchain pinned by the workspace at compile time
//! and emits a visible warning when it is unavailable. Discovery is anchored
//! at `CARGO_MANIFEST_DIR`, so an external Cargo caller cannot accidentally
//! select a different toolchain through its current working directory.
//!
//! See: <https://github.com/alabsystems/clean/issues/1257>

#[path = "lean_toolchain.rs"]
mod lean_toolchain;

fn main() {
    let manifest_dir = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("Cargo sets CARGO_MANIFEST_DIR"),
    );
    let toolchain_file = manifest_dir
        .parent()
        .and_then(std::path::Path::parent)
        .expect("clean-olean is inside the Clean workspace")
        .join("lean-toolchain");

    println!("cargo:rerun-if-changed={}", toolchain_file.display());
    println!("cargo:rerun-if-changed=lean_toolchain.rs");
    println!("cargo:rerun-if-env-changed=ELAN");
    println!("cargo:rerun-if-env-changed=ELAN_HOME");
    println!("cargo:rerun-if-env-changed=HOME");
    println!("cargo:rerun-if-env-changed=USERPROFILE");
    println!(
        "cargo:rerun-if-env-changed={}",
        lean_toolchain::PINNED_LEAN_LIB_ENV
    );
    println!("cargo:rerun-if-env-changed=CLEAN_OLEAN_REQUIRE_PINNED_LEAN");

    match lean_toolchain::resolve_pinned_lean(&manifest_dir) {
        Ok(resolved) => {
            println!(
                "cargo:rustc-env={}={}",
                lean_toolchain::PINNED_LEAN_LIB_ENV,
                resolved.lib_path.display()
            );
            println!(
                "cargo:rustc-env={}={}",
                lean_toolchain::PINNED_LEAN_TOOLCHAIN_ENV,
                resolved.toolchain
            );
        }
        Err(error) => {
            println!(
                "cargo:warning=repository-pinned Lean unavailable: {error}. Real-.olean tests \
                 cannot carry toolchain authority; install the toolchain named by {}.",
                toolchain_file.display()
            );
            if std::env::var_os("CLEAN_OLEAN_REQUIRE_PINNED_LEAN").is_some() {
                panic!("CLEAN_OLEAN_REQUIRE_PINNED_LEAN is set: {error}");
            }
        }
    }
}
