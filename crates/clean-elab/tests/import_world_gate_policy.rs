// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `--permissive-imports` stands nothing in for an `.olean` of a refused
//! Lean world (`formats-import-world-gate`, docs/DECISIONS.md R81).
//!
//! The import is the pinned build's `Target` (tracked, closure-cache pair)
//! with header bytes 7..80 rewritten to Lean v4.33.1's, reached through
//! `LEAN_PATH`. Until 2026-10-17 it loaded, under either policy, as if
//! pinned Lean had written it. This file is its own test binary, so setting
//! `LEAN_PATH` here touches no other test.

use clean_elab::{process_imports_with_policy, ElabError, ImportPolicy};
use clean_kernel::Environment;
use clean_parser::SurfaceName;
use std::fs;
use std::path::Path;

const V4_33_1_GITHASH: &[u8; 40] = b"819816b2e0a3bf405af45ae5c7af2491d8f5bee6";

#[test]
fn permissive_imports_refuse_an_olean_of_a_foreign_lean_world() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.30.0/closure_cache");
    let dir = tempfile::tempdir().expect("tmp");
    fs::copy(fixtures.join("Init.olean"), dir.path().join("Init.olean")).expect("Init");
    let mut target = fs::read(fixtures.join("Target.olean")).expect("Target");
    let mut version = [0u8; 33];
    version[..6].copy_from_slice(b"4.33.1");
    target[7..40].copy_from_slice(&version);
    target[40..80].copy_from_slice(V4_33_1_GITHASH);
    fs::write(dir.path().join("Target.olean"), target).expect("rewritten Target");
    std::env::set_var("LEAN_PATH", dir.path());
    std::env::remove_var("MATHLIB_PATH");

    for policy in [ImportPolicy::FailClosed, ImportPolicy::Permissive] {
        let result = process_imports_with_policy(
            &mut Environment::new(),
            &[SurfaceName::generated_path("Target")],
            policy,
        );
        match result {
            Err(ElabError::UnresolvedImport { module, reason }) => {
                assert_eq!(module, "Target");
                assert!(
                    reason.contains("unsupported Lean world")
                        && reason.contains(std::str::from_utf8(V4_33_1_GITHASH).expect("ascii")),
                    "{policy:?}: refused by its Lean world: {reason}"
                );
            }
            other => panic!("{policy:?}: a foreign-world import must be refused: {other:?}"),
        }
    }
}
