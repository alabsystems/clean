// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A second Lean world fails `clean lake build`, permissive or not.
//!
//! Moved here from `src/build_admission_tests.rs` on 2026-11-15, its subject
//! unchanged. It puts a root `Init.olean`, the pinned build's leaf fixture,
//! on `LEAN_PATH`. Since `clean lake build` elaborates every module over
//! genuine Init (`docs/DECISIONS.md`, 2026-11-15 K1 entry), every concurrent
//! build in the same process resolves Init through that variable. In the
//! unit-test binary those builds then loaded the leaf fixture as Init and
//! failed ("Unknown identifier: Eq"). This file is its own test binary, so
//! setting `LEAN_PATH` here touches no other test.

use clean_lake::build::{BuildContext, BuildOptions};
use clean_lake::workspace::Workspace;
use std::fs;
use std::path::Path;

/// `--permissive-imports` warns past an import that does not load, but not
/// past one of a second Lean world (docs/DECISIONS.md R81): the pinned
/// build's `Init` and v4.13.0's `Minimal`, each readable alone, imported by
/// one module. Until 2026-10-17 both loaded into its environment, and the
/// build succeeded.
#[test]
fn a_second_lean_world_fails_the_build_even_with_permissive_imports() {
    let tmp = tempfile::tempdir().expect("tmp");
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean");
    let lib = tmp.path().join("lib");
    fs::create_dir_all(lib.join("Mathlib")).expect("lib dir");
    fs::copy(
        fixtures.join("v4.30.0/closure_cache/Init.olean"),
        lib.join("Init.olean"),
    )
    .expect("the pinned build's leaf Init");
    fs::copy(
        fixtures.join("v4.13.0/custom/Minimal.olean"),
        lib.join("Mathlib/Minimal.olean"),
    )
    .expect("v4.13.0's Minimal");
    let dir = tmp.path().join("u");
    fs::create_dir_all(&dir).expect("consumer dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"usr\"\ndefaultTargets = [\"U\"]\n\n[[lean_lib]]\nname = \"U\"\nroots = [\"U\"]\n",
    )
    .expect("consumer lakefile");
    fs::write(dir.join("U.lean"), "import Init\nimport Mathlib.Minimal\n").expect("source");

    // Its own test binary: no other test reads this process's environment.
    #[allow(unknown_lints, env_mutation)]
    std::env::set_var("LEAN_PATH", &lib);
    let result = BuildContext::new(Workspace::load(&dir).expect("consumer workspace"))
        .with_options(BuildOptions::new().with_permissive_imports(true))
        .build_all()
        .expect("the build runs");
    assert!(
        result
            .failed
            .iter()
            .any(|(module, why)| module == "U" && why.contains("mixed Lean worlds")),
        "{result:?}"
    );
}
