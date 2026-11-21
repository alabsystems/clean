// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An artifact Lean wrote, beside its source and without one
//! (`formats-import-world-gate`, docs/DECISIONS.md R81).
//!
//! The artifact is the tracked pinned-Lean (v4.30.0-rc2) build of the
//! closure-cache leaf's dependent (`tests/fixtures/olean/v4.30.0/closure_cache`),
//! so these tests need no installed toolchain.

use super::{ArtifactBinder, ArtifactSourceBinding, ImportAdmission, ImportAdmitter};
use crate::workspace::Workspace;
use clean_kernel::LeanWorld;
use std::fs;
use std::path::{Path, PathBuf};

/// The githash of the Lean v4.33.1 release (its `Init/Prelude.olean`
/// header): a world no row of `lean_worlds.tsv` names.
const FOREIGN_GITHASH: &str = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6";

fn pinned_lean_target() -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.30.0/closure_cache/Target.olean");
    fs::read(&path).unwrap_or_else(|e| panic!("fixture {}: {e}", path.display()))
}

/// The githash the v2 header of `bytes` carries (bytes 40..80).
fn header_githash(bytes: &[u8]) -> String {
    String::from_utf8(bytes[40..80].to_vec()).expect("an ASCII githash")
}

/// `bytes` with its v2 header's version string and githash rewritten.
fn in_foreign_world(mut bytes: Vec<u8>) -> Vec<u8> {
    let mut version = [0u8; 33];
    version[..6].copy_from_slice(b"4.33.1");
    bytes[7..40].copy_from_slice(&version);
    bytes[40..80].copy_from_slice(FOREIGN_GITHASH.as_bytes());
    bytes
}

/// A Lake workspace at `dir` whose library `Target` has its source
/// (`prelude` + `import Init`) and, in its build directory, `artifact`.
fn workspace_with_artifact(dir: &Path, artifact: &[u8]) -> PathBuf {
    fs::create_dir_all(dir).expect("workspace dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"w\"\ndefaultTargets = [\"Target\"]\n\n[[lean_lib]]\nname = \"Target\"\nroots = [\"Target\"]\n",
    )
    .expect("lakefile");
    fs::write(dir.join("Target.lean"), "prelude\nimport Init\n").expect("source");
    let olean = Workspace::load(dir)
        .expect("workspace loads")
        .olean_path("Target")
        .expect("Target's artifact path");
    fs::create_dir_all(olean.parent().expect("build dir")).expect("build dir");
    fs::write(&olean, artifact).expect("artifact");
    olean
}

/// Exit (c): pinned Lean's v2 artifact beside its source is foreign-built
/// and disclosed under its githash. Until 2026-10-17 its header was read
/// 56 bytes short, so it was "unreadable" and refused.
#[test]
fn a_pinned_lean_v2_artifact_beside_its_source_is_disclosed_with_its_githash() {
    let tmp = tempfile::tempdir().expect("tmp");
    let bytes = pinned_lean_target();
    let githash = header_githash(&bytes);
    assert!(
        githash.starts_with("3dc1a088"),
        "the pinned build: {githash}"
    );
    let olean = workspace_with_artifact(tmp.path(), &bytes);

    assert_eq!(
        ArtifactBinder::default().bind("Target", &olean),
        ArtifactSourceBinding::ForeignBuilt {
            git_hash: githash.clone()
        }
    );
    match ImportAdmitter::new().admit_in_world("Target", &olean, None) {
        ImportAdmission::Disclosed(row) => {
            assert!(row.contains(&githash), "the row names the githash: {row}");
        }
        other => panic!("a pinned-Lean artifact beside its source is disclosed: {other:?}"),
    }
}

/// Brief (6): an artifact of a Lean world this build does not read is
/// refused, by its identity, whether or not its source is beside it. Until
/// 2026-10-17 the bare one was disclosed (no source) and the one beside its
/// source refused only as "unreadable artifact header".
#[test]
fn a_foreign_world_artifact_is_refused_with_or_without_its_source() {
    let tmp = tempfile::tempdir().expect("tmp");
    let bytes = in_foreign_world(pinned_lean_target());
    let bare = tmp.path().join("bare/Target.olean");
    fs::create_dir_all(bare.parent().expect("dir")).expect("dir");
    fs::write(&bare, &bytes).expect("bare artifact");
    let beside = workspace_with_artifact(&tmp.path().join("ws"), &bytes);

    for olean in [&bare, &beside] {
        match ImportAdmitter::new().admit_in_world("Target", olean, None) {
            ImportAdmission::Refused(row) => {
                assert!(row.contains(FOREIGN_GITHASH), "names its githash: {row}");
                assert!(row.contains("v4.30.0-rc2"), "names the world read: {row}");
            }
            other => panic!(
                "{}: a foreign-world artifact is refused: {other:?}",
                olean.display()
            ),
        }
    }
}

#[test]
fn a_measured_lean_artifact_is_admitted_only_with_its_own_declaration() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact = dir.path().join("StablePlain.olean");
    fs::copy(fixture, &artifact).expect("stable Lean fixture");
    let mut admitter = ImportAdmitter::new();
    let unresolved = admitter.admit_in_world("StablePlain", &artifact, None);
    assert!(matches!(unresolved, ImportAdmission::Refused(_)));
    let selected = admitter.admit_in_world("StablePlain", &artifact, Some(LeanWorld::Lean436));
    assert!(matches!(selected, ImportAdmission::Disclosed(_)));
    let other = admitter.admit_in_world("StablePlain", &artifact, Some(LeanWorld::Lean436Rc2));
    assert!(matches!(other, ImportAdmission::Refused(row) if row.contains("v4.36.0-rc2")));
    assert_eq!(
        admitter.admit_in_world("StablePlain", &artifact, None),
        unresolved
    );
}
