// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build script for clean-sys.
//!
//! Generates the C header file using cbindgen.

use std::env;
use std::path::PathBuf;

fn main() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let header_path = PathBuf::from(&crate_dir).join("include").join("clean.h");

    // Only run cbindgen when explicitly requested or when the header doesn't exist.
    // cbindgen hangs indefinitely when parsing the crate source in normal builds (#3172).
    // Regenerate with: CLEAN_GENERATE_HEADERS=1 cargo build -p clean-sys
    let should_generate = env::var("CLEAN_GENERATE_HEADERS").is_ok() || !header_path.exists();

    if should_generate {
        let out_dir = header_path
            .parent()
            .expect("invariant: header path has parent");

        // Create include directory if it doesn't exist
        std::fs::create_dir_all(out_dir).ok();

        // Generate C header
        let config = cbindgen::Config::from_file(PathBuf::from(&crate_dir).join("cbindgen.toml"))
            .unwrap_or_default();

        if let Ok(bindings) = cbindgen::Builder::new()
            .with_crate(&crate_dir)
            .with_config(config)
            .generate()
        {
            bindings.write_to_file(&header_path);
        }
    }

    // Re-run if source changes or if the env var changes
    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=cbindgen.toml");
    println!("cargo:rerun-if-env-changed=CLEAN_GENERATE_HEADERS");
}
