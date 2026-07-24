// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `clean mathverse build-closure-shards` (the first-class closure
//! shard builder) and the co-located cache helpers used by auto-discovery.
//!
//! Seeded by the committed `tests/fixtures/olean/v4.13.0/custom/Minimal.olean`
//! (the same fixture the v3 closure-binding tests use), so they run with no
//! Mathlib checkout. `Minimal.olean` imports exactly `Init`, so copying it to
//! `<root>/Init.olean` gives a single-module, fully-resolvable import closure to
//! build over.
//!
//! `#[path]`-included submodule of `closure_shards_dispatch`, so `super::*`
//! resolves to that module's private items.

use super::*;
use crate::cli::ClosureElide;
use crate::shard::ShardReader;

/// Path to the committed `Minimal.olean` fixture (def identity + theorem id_id),
/// which imports exactly `Init`.
fn minimal_olean() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("workspace root")
}

/// Lay out a resolvable single-module closure: `<root>/Init.olean` (a copy of
/// the fixture) is the one import of the target `<root>/Target.olean` (another
/// copy, whose only import is `Init`). Returns `(target_path, root_dir)`.
fn layout_minimal_closure(root: &Path) -> PathBuf {
    std::fs::create_dir_all(root).unwrap();
    let init = root.join("Init.olean");
    std::fs::copy(minimal_olean(), &init).expect("copy Init.olean");
    let target = root.join("Target.olean");
    std::fs::copy(minimal_olean(), &target).expect("copy Target.olean");
    target
}

// -- default_closure_cache_dir -------------------------------------------------

#[test]
fn test_default_cache_dir_is_sibling_of_out_dir() {
    let out = PathBuf::from("/tmp/run/stamped");
    let cache = default_closure_cache_dir(&out);
    assert_eq!(cache, PathBuf::from("/tmp/run").join(CLOSURE_CACHE_DIRNAME));
}

#[test]
fn test_default_cache_dir_bare_name_nests_inside() {
    // A bare relative name with no directory component -> nest the cache inside.
    let out = PathBuf::from("stamped");
    let cache = default_closure_cache_dir(&out);
    assert_eq!(cache, PathBuf::from("stamped").join(CLOSURE_CACHE_DIRNAME));
}

// -- cache_dir_is_populated ----------------------------------------------------

#[test]
fn test_cache_populated_false_when_missing() {
    assert!(!cache_dir_is_populated(Path::new(
        "/nonexistent/closure/cache/path"
    )));
}

#[test]
fn test_cache_populated_false_when_empty() {
    let dir = tempfile::tempdir().unwrap();
    assert!(
        !cache_dir_is_populated(dir.path()),
        "an empty dir is NOT a usable cache (must force eager)"
    );
    // A non-`.mathverse` file does not count either.
    std::fs::write(dir.path().join("README.txt"), b"hi").unwrap();
    assert!(!cache_dir_is_populated(dir.path()));
}

#[test]
fn test_cache_populated_true_with_shard() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("Foo.mathverse"), b"\x00\x01").unwrap();
    assert!(cache_dir_is_populated(dir.path()));
}

// -- build-closure-shards (the subcommand) -------------------------------------

/// The `build-closure-shards` subcommand produces v3 fail-closed shards over the
/// Minimal fixture's import closure: at least one shard is written, and every
/// shard read back is a v3 shard whose fail-closed gate passed and whose source
/// `.olean` is bound (non-zero blake3).
#[test]
fn test_build_closure_shards_subcommand_produces_v3_shards() {
    let root = tempfile::tempdir().unwrap();
    let out = tempfile::tempdir().unwrap();
    let target = layout_minimal_closure(root.path());

    let args = BuildClosureShardsArgs {
        target,
        closure_root: root.path().to_path_buf(),
        out: out.path().to_path_buf(),
        closure_elide: ClosureElide::Opaque,
    };
    cmd_build_closure_shards(args).expect("build-closure-shards");

    // The closure of `Target` is exactly `Init` (one module, target excluded).
    let shards: Vec<PathBuf> = std::fs::read_dir(out.path())
        .unwrap()
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "mathverse"))
        .collect();
    assert!(
        !shards.is_empty(),
        "build-closure-shards must produce at least one shard"
    );
    // The target module must NOT be in the cache (it is re-minted by the replay).
    assert!(
        !out.path().join("Target.mathverse").exists(),
        "target module must be excluded from the closure cache"
    );

    for shard in &shards {
        let bytes = std::fs::read(shard).unwrap();
        let reader = ShardReader::from_bytes(&bytes).expect("read v3 shard");
        assert_eq!(
            reader.header.version,
            crate::shard::SHARD_VERSION,
            "{}: must be the current v3 shard version",
            shard.display()
        );
        assert_eq!(
            reader.header.fail_closed_verified,
            1,
            "{}: v3 fail-closed gate must have passed",
            shard.display()
        );
        assert_ne!(
            reader.header.source_olean_blake3,
            [0u8; 32],
            "{}: source .olean must be digest-bound",
            shard.display()
        );
    }
}

/// `cmd_build_closure_shards` is best-effort and never aborts on a per-module
/// resolve/convert miss: a module that does not resolve under ANY search path is
/// reported and SKIPPED rather than erroring (a partial/empty cache simply forces
/// the eager fallback when later served). Here the only import (`Init`) resolves
/// via the toolchain's default search paths, so the command succeeds with a
/// non-empty cache; a module unresolvable everywhere would be skipped the same
/// way without erroring. The empty-cache → eager invariant itself is covered by
/// `test_cache_populated_false_when_empty` and the closure-serve precedence
/// tests.
#[test]
fn test_build_closure_shards_is_best_effort_and_does_not_error() {
    let out = tempfile::tempdir().unwrap();
    let root = tempfile::tempdir().unwrap();
    let target = root.path().join("Target.olean");
    std::fs::copy(minimal_olean(), &target).expect("copy target");

    let args = BuildClosureShardsArgs {
        target,
        closure_root: root.path().to_path_buf(),
        out: out.path().to_path_buf(),
        closure_elide: ClosureElide::Opaque,
    };
    // Best-effort builder: never errors on per-module skips.
    cmd_build_closure_shards(args).expect("best-effort build must not error");
}
