// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole B3 (`docs/DECISIONS.md` R113) through the `.olean` LOADER, the path every
//! import takes (`load_parse.rs`'s `reject_foreign_payload_trailer`), which the
//! review found no test reached (findings P6, P9): every earlier trailer test was
//! refused first by the `ParsedModule` reader (`module/readers.rs`).
//!
//! The fixture is minted at test time from the honest module-system
//! `ReplayHonestDep` and its non-module user `ReplayHonestDepUser` (README):
//! a `CLEANENV` trailer appended to the dependency's `.olean`, or to its
//! `.olean.private` alone, and the USER loaded, so the trailer is met as an
//! import. The untouched pair is the control.

use super::*;
use clean_olean::{encode_clean_payload, CleanPayload};

/// A copy of `ReplayHonestDep` (all parts and its `.ir`) and `ReplayHonestDepUser`,
/// with a trailer appended to the dependency part `trailer_on` (`None`: no trailer).
fn dep_pair(trailer_on: Option<&str>) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = compiled_fixture_dir(FAMILY);
    for file in [
        "ReplayHonestDep.olean",
        "ReplayHonestDep.olean.server",
        "ReplayHonestDep.olean.private",
        "ReplayHonestDep.ir",
        "ReplayHonestDepUser.olean",
    ] {
        let mut bytes = std::fs::read(src.join(file)).expect("read fixture part");
        if trailer_on == Some(file) {
            bytes.extend(encode_clean_payload(&CleanPayload::default()).expect("encode trailer"));
        }
        std::fs::write(dir.path().join(file), &bytes).expect("write part");
    }
    dir
}

fn load_user(dir: &std::path::Path) -> Result<(), String> {
    let mut env = Environment::for_lean_replay();
    let mut search = vec![dir.to_path_buf()];
    search.extend(default_search_paths());
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        "ReplayHonestDepUser",
        &search,
        &mut visited,
        OleanImportPolicy::default(),
    )
    .map(|_| ())
    .map_err(|e| e.to_string())
}

#[test]
fn test_loader_refuses_a_payload_trailer_on_an_imported_lean_part() {
    // Control: the honest pair loads.
    load_user(dep_pair(None).path()).expect("the honest pair loads");
    // The base part of the import (`parse_load_module`) and its private part
    // (`parse_load_module_incremental`).
    for part in ["ReplayHonestDep.olean", "ReplayHonestDep.olean.private"] {
        let dir = dep_pair(Some(part));
        let error =
            load_user(dir.path()).expect_err("a trailer on an imported Lean part is refused");
        assert!(
            error.contains("payload trailer") && error.contains("Lean-written"),
            "{part}: the refusal must name the foreign trailer: {error}"
        );
    }
}
