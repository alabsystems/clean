// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hole B3 (`docs/DECISIONS.md` R113): a Clean payload trailer appended to a
//! part Lean's own compiler wrote. Only Clean's exporter appends a `CLEANENV`
//! trailer, and only to its own layout; `lean` never reads a trailer on a
//! Lean-written `.olean`, so a re-check that trusted the trailer's declarations
//! would admit constants `leanchecker` never sees (the per-constant lane loaded
//! a target's trailer through `load_inductive_families`, making its families
//! resident though they were never replay rows). The `.olean` loader now
//! refuses a trailer on a Lean part at decode (`ImportError::PayloadOnLeanPart`
//! / `OleanError::PayloadOnLeanPart`), so every lane and every import is
//! refused by it.
//!
//! The fixture is minted at test time: the honest Lean-built `ReplayHonest`
//! `.olean` with a `CLEANENV` trailer appended, in a tempdir. The honest
//! `ReplayHonest` with no trailer is the control.

use super::*;
use crate::cli::kv_cache::FingerprintMode;
use crate::cli::per_constant_load::{per_constant_verify, PerConstantResult};
use crate::cli::MathverseCliError;
use clean_kernel::env::ProofValueElision;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::{encode_clean_payload, CleanPayload};
use std::path::{Path, PathBuf};

/// Copy `ReplayHonest.olean` into a fresh dir, optionally appending a trailer.
/// Returns the dir (kept alive by the caller) and the target path. Like the
/// rest of this battery it reaches the fixture through `compiled_fixture_dir`,
/// which needs the repository-pinned Lean toolchain and panics without it, so
/// the test fails loudly rather than skipping its own subject.
fn honest_with_optional_trailer(with_trailer: bool) -> (tempfile::TempDir, PathBuf) {
    let src = fixtures().join("ReplayHonest.olean");
    let mut bytes = std::fs::read(&src).expect("read ReplayHonest.olean fixture");
    if with_trailer {
        bytes.extend(encode_clean_payload(&CleanPayload::default()).expect("encode trailer"));
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("ReplayHonest.olean");
    std::fs::write(&path, &bytes).expect("write target");
    (dir, path)
}

fn search_with(dir: &Path) -> Vec<PathBuf> {
    let mut search = vec![dir.to_path_buf()];
    search.extend(clean_olean::default_search_paths());
    search
}

fn per_constant_at(path: &Path, root: &Path) -> Result<PerConstantResult, MathverseCliError> {
    per_constant_verify(
        path,
        root,
        &[],
        DEFAULT_HEARTBEAT_LIMIT,
        None,
        FingerprintMode::Metadata,
        false,
        false,
        true,
        ProofValueElision::None,
        64,
        None,
    )
}

#[test]
fn test_per_constant_verify_refuses_a_payload_trailer_on_a_lean_part() {
    let (dir, path) = honest_with_optional_trailer(true);
    let err = per_constant_at(&path, dir.path())
        .expect_err("a trailer on a Lean part must refuse the run");
    let msg = err.to_string();
    assert!(
        msg.contains("payload trailer") && msg.contains("Lean-written"),
        "the refusal must name the foreign trailer: {msg}"
    );

    // Control: the same artifact with no trailer verifies its theorems.
    let (cdir, cpath) = honest_with_optional_trailer(false);
    let r = per_constant_at(&cpath, cdir.path()).expect("the honest control runs");
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert!(r.kernel_verified >= 1, "{:?}", r.errors);
}

/// A copy of the module-system `ReplayHonestDep` (every part, and its `.ir`)
/// with a trailer appended to its `.olean.private` only, so a reader that parses
/// the `.olean` first does not meet it: the loader's incremental parse of the
/// private part is what must refuse it (`load_parse.rs`).
fn honest_dep_with_private_trailer() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    for ext in ["olean", "olean.server", "olean.private", "ir"] {
        let name = format!("ReplayHonestDep.{ext}");
        let mut bytes = std::fs::read(fixtures().join(&name)).expect("read ReplayHonestDep part");
        if ext == "olean.private" {
            bytes.extend(encode_clean_payload(&CleanPayload::default()).expect("encode trailer"));
        }
        std::fs::write(dir.path().join(&name), &bytes).expect("write part");
    }
    dir
}

/// The sharded worker parses the module's `.olean` itself, then loads every part
/// through the `.olean` loader: a trailer on the `.olean.private` is refused by
/// the loader's incremental parse, by name, as a load error.
#[test]
fn test_sharded_verify_refuses_a_payload_trailer_on_a_lean_private_part() {
    let dir = honest_dep_with_private_trailer();
    let search = search_with(dir.path());
    match crate::verify::sharded::verify_module("ReplayHonestDep", &search, 64) {
        Err(crate::verify::sharded::ShardedVerifyError::LoadDeps { reason, .. }) => {
            assert!(
                reason.contains("payload trailer") && reason.contains("Lean-written"),
                "the refusal must name the foreign trailer: {reason}"
            );
        }
        Err(e) => panic!("sharded verify refused for another reason: {e}"),
        Ok(r) => panic!(
            "sharded verify was not refused: verified {:?}",
            r.kernel_verified_names
        ),
    }
}

/// `per-constant-verify` reads the target through the one artifact reader, whose
/// parse of the `.olean.private` refuses the trailer.
#[test]
fn test_per_constant_verify_refuses_a_payload_trailer_on_a_lean_private_part() {
    let dir = honest_dep_with_private_trailer();
    let err = per_constant_at(&dir.path().join("ReplayHonestDep.olean"), dir.path())
        .expect_err("a trailer on a Lean private part must refuse the run");
    let msg = err.to_string();
    assert!(
        msg.contains("payload trailer") && msg.contains("Lean-written"),
        "the refusal must name the foreign trailer: {msg}"
    );
}
