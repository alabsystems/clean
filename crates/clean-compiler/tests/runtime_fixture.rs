// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The clean C runtime for tests that hand `cc` a header and a
//! `clean_runtime.c`, materialized from the copies EMBEDDED in the
//! `clean_runtime` crate — never from a path baked in at compile time.
//!
//! Why: `env!("CARGO_MANIFEST_DIR")` names the directory a crate was compiled
//! FROM, and that directory can be gone by the time the test binary runs.
//! Measured 2026-09-15: the shared `target/debug` held a `libclean_runtime`
//! rlib compiled from a since-deleted gate-demonstration sandbox — Cargo
//! names a path dependency's artifacts by its workspace-RELATIVE path, so a
//! sandbox build at another absolute root overwrites the real tree's units —
//! and every `-I<that path>/include` failed with
//! `fatal error: 'clean_runtime.h' file not found`. The header and
//! `clean_runtime.c` travel INSIDE the crate (`runtime_header()` /
//! `runtime_source()`), so writing them out makes a test hermetic wherever
//! its binary was built. This is the same materialization `clean run`
//! performs (`crates/clean-native/src/native_build.rs`, `materialize_build`).
//!
//! Shared the way `test_helpers.rs` is: `mod runtime_fixture;` from each
//! integration test that needs it. Every item here is used by every
//! includer, so no includer carries a dead-code warning.

use std::path::PathBuf;

use tempfile::TempDir;

/// The crate-relative include the shipped `clean_runtime.c` opens with
/// (`crates/clean-runtime/src/clean_runtime.c:11`); flat layouts rewrite it.
const CRATE_RELATIVE_INCLUDE: &str = "../include/clean_runtime.h";

/// A temporary directory holding `clean_runtime.h` and a flat-layout
/// `clean_runtime.c`. Keep it alive until the C compiler has finished.
pub struct MaterializedRuntime {
    root: TempDir,
}

impl MaterializedRuntime {
    /// Write the embedded header and runtime source into a fresh temp dir.
    pub fn materialize() -> Self {
        let root = tempfile::tempdir().expect("create runtime temp dir");
        std::fs::write(
            root.path().join("clean_runtime.h"),
            clean_runtime::runtime_header(),
        )
        .expect("write clean_runtime.h");

        let source = clean_runtime::runtime_source();
        assert!(
            source.contains(CRATE_RELATIVE_INCLUDE),
            "clean_runtime.c no longer includes {CRATE_RELATIVE_INCLUDE}; \
             update runtime_fixture.rs to match its new layout"
        );
        std::fs::write(
            root.path().join("clean_runtime.c"),
            source.replacen(CRATE_RELATIVE_INCLUDE, "clean_runtime.h", 1),
        )
        .expect("write clean_runtime.c");

        Self { root }
    }

    /// Directory to pass to the C compiler as `-I`.
    pub fn include_dir(&self) -> PathBuf {
        self.root.path().to_path_buf()
    }

    /// The runtime translation unit to compile beside the emitted program.
    pub fn c_source(&self) -> PathBuf {
        self.root.path().join("clean_runtime.c")
    }
}
