// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Build script for `trust-ir`: resolve the source identity embedded in
//! `trust_ir::BUILD_IDENTITY` (roadmap WS8.4). The rule lives in
//! `build_identity.rs` so the CLI tests exercise the same code; this script
//! only prints its directives, or fails the build with its error.

mod build_identity;

fn main() {
    let crate_dir = std::path::PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"),
    );
    let env = |key: &str| build_identity::env_value(std::env::var_os(key));
    match build_identity::build_directives(&env, &crate_dir, std::ffi::OsStr::new("git")) {
        Ok(lines) => {
            for line in lines {
                println!("{line}");
            }
        }
        Err(error) => panic!("trust-ir build identity: {error}"),
    }
}
