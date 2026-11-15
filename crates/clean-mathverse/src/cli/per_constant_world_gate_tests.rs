// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The import world gate (docs/DECISIONS.md R38, R81) on the mathverse lanes
//! that read `.olean` parts themselves rather than through
//! `clean_olean::load_module_with_deps*`: `per-constant-verify`'s demand walk,
//! and the closure-shard builder and verifier its `--closure-shards` leg and
//! `stamp-verified` serve from.
//!
//! `stamp-verified` loads only a target's imports through those loaders (the
//! target's own declarations are re-minted from its shard), so its target's
//! header is checked here too.
//!
//! Measured 2026-10-17 at c4e3e388f, where only those loaders were gated:
//! `per-constant-verify` kernel-verified `targetVal` in a pinned `Target`
//! whose header names Lean v4.33.1, and over a v4.33.1 `Init`; it ran a
//! pinned `Target` over a v4.8.0 `Init` and a triple whose `.olean.private`
//! names v4.33.1; the shard builder converted a closure over a v4.33.1
//! `Init`; the verifier marked a v4.13.0 and a v4.8.0 shard servable from one
//! directory; and `stamp-verified`'s closure loader loaded the imports of a
//! v4.33.1 `Target`. `load_module_with_deps` refuses each by its Lean world.
//!
//! Every fixture is tracked and every foreign identity is a rewrite of one,
//! as in `crates/clean-olean/tests/olean_world_gate.rs`.

use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::env::ProofValueElision;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;

use clean_kernel::Name;
use clean_olean::LeanWorldScope;

use super::{per_constant_verify, vstamp_path, LazyLane, PerConstantResult};
use crate::cli::closure_load::{
    build_closure_shards_for_targets_with_search_paths, load_targets_closure,
    verify_closure_shards_against_oleans, ClosureShardBuild,
};
use crate::cli::kv_cache::FingerprintMode;
use crate::cli::MathverseCliError;
use crate::closure_source::ShardConstantSource;

/// The Lean v4.33.1 release's githash (its `Init/Prelude.olean` header).
const V4_33_1_GITHASH: &[u8; 40] = b"819816b2e0a3bf405af45ae5c7af2491d8f5bee6";

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean")
}

fn read(rel: &str) -> Vec<u8> {
    let path = fixtures().join(rel);
    fs::read(&path).unwrap_or_else(|e| panic!("fixture {}: {e}", path.display()))
}

fn v4_33_1() -> &'static str {
    std::str::from_utf8(V4_33_1_GITHASH).expect("ascii")
}

/// `bytes` (a v2 header) as Lean v4.33.1 wrote it: header bytes 7..80, the
/// version string and the githash, rewritten.
fn as_v4_33_1(mut bytes: Vec<u8>) -> Vec<u8> {
    let mut version = [0u8; 33];
    version[..6].copy_from_slice(b"4.33.1");
    bytes[7..40].copy_from_slice(&version);
    bytes[40..80].copy_from_slice(V4_33_1_GITHASH);
    bytes
}

/// The pinned build's leaf `Init` (`inductive Leaf`, `def Leaf.same`).
fn pinned_init() -> Vec<u8> {
    read("v4.30.0/closure_cache/Init.olean")
}

/// The pinned build's `Target` (`import Init`, `def targetVal`).
fn pinned_target() -> Vec<u8> {
    read("v4.30.0/closure_cache/Target.olean")
}

/// v4.8.0's `FactLib` (a Frontend-only world's leaf, `def Fact`).
fn v4_8_0_leaf() -> Vec<u8> {
    read("v4.8.0/witness/FactLib.olean")
}

/// A closure root holding `parts` as `<name>.olean`.
fn root_with(parts: &[(&str, Vec<u8>)]) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tmp");
    for (name, bytes) in parts {
        fs::write(dir.path().join(format!("{name}.olean")), bytes).expect("part");
    }
    dir
}

/// `per-constant-verify --all-declared` on `module` of `root`, as the CLI
/// calls it.
fn per_constant(root: &Path, module: &str) -> Result<PerConstantResult, MathverseCliError> {
    per_constant_verify(
        &root.join(format!("{module}.olean")),
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

/// The closure-shard builder over `targets` of `root`, its own shards
/// included (`stamp-verified --parallel`'s call).
fn build_shards(
    root: &Path,
    targets: &[&str],
    out: &Path,
) -> Result<ClosureShardBuild, MathverseCliError> {
    let targets: Vec<PathBuf> = targets
        .iter()
        .map(|t| root.join(format!("{t}.olean")))
        .collect();
    build_closure_shards_for_targets_with_search_paths(
        &targets,
        root,
        &[root.to_path_buf()],
        out,
        false,
    )
}

/// `result` is refused by a Lean world (`kind`: `unsupported Lean world` or
/// `mixed Lean worlds`), and its message names every one of `names`.
fn assert_world_refusal<T: std::fmt::Debug>(
    what: &str,
    result: Result<T, MathverseCliError>,
    kind: &str,
    names: &[&str],
) {
    let message = match result {
        Ok(done) => panic!("{what}: ran, but must be refused by its Lean world: {done:?}"),
        Err(e) => e.to_string(),
    };
    assert!(
        message.contains(kind),
        "{what}: refused as `{kind}`, not by: {message}"
    );
    for name in names {
        assert!(message.contains(name), "{what}: names {name}: {message}");
    }
}

/// The control: the pinned build's own closure verifies its one target.
#[test]
fn test_per_constant_world_gate_pinned_closure_verifies() {
    let root = root_with(&[("Init", pinned_init()), ("Target", pinned_target())]);
    let r = per_constant(root.path(), "Target").expect("the pinned closure runs");
    assert_eq!((r.kernel_verified, r.failed), (1, 0), "{:?}", r.errors);
}

/// A target whose header names Lean v4.33.1 is refused by its world before a
/// verdict is minted.
#[test]
fn test_per_constant_world_gate_foreign_target_is_refused() {
    let root = root_with(&[
        ("Init", pinned_init()),
        ("Target", as_v4_33_1(pinned_target())),
    ]);
    assert_world_refusal(
        "per-constant-verify over a v4.33.1 Target",
        per_constant(root.path(), "Target"),
        "unsupported Lean world",
        &["`Target`", v4_33_1(), "v4.30.0-rc2"],
    );
}

/// A module of the target's closure whose header names Lean v4.33.1 is
/// refused by its world, though the target is the pinned build's.
#[test]
fn test_per_constant_world_gate_foreign_import_is_refused() {
    let root = root_with(&[
        ("Init", as_v4_33_1(pinned_init())),
        ("Target", pinned_target()),
    ]);
    assert_world_refusal(
        "per-constant-verify over a v4.33.1 Init",
        per_constant(root.path(), "Target"),
        "unsupported Lean world",
        &["`Init`", v4_33_1()],
    );
}

/// Two readable worlds in one closure: the pinned `Target` over v4.8.0's
/// leaf standing as its `Init`.
#[test]
fn test_per_constant_world_gate_second_world_is_mixed() {
    let root = root_with(&[("Init", v4_8_0_leaf()), ("Target", pinned_target())]);
    assert_world_refusal(
        "per-constant-verify over a v4.8.0 Init",
        per_constant(root.path(), "Target"),
        "mixed Lean worlds",
        &["`Init` is of Lean v4.8.0", "`Target`", "v4.30.0-rc2"],
    );
}

/// A pinned module-system triple whose `.olean.private` alone names Lean
/// v4.33.1: the demand walk merges that companion into the target, so it is
/// refused by its world.
#[test]
fn test_per_constant_world_gate_foreign_companion_is_refused() {
    let root = tempfile::tempdir().expect("tmp");
    for part in ["Sigma.olean", "Sigma.olean.server", "Sigma.olean.private"] {
        let bytes = read(&format!("v4.30.0/module-system/{part}"));
        let bytes = if part.ends_with(".private") {
            as_v4_33_1(bytes)
        } else {
            bytes
        };
        fs::write(root.path().join(part), bytes).expect("part");
    }
    assert_world_refusal(
        "per-constant-verify over a v4.33.1 Sigma.olean.private",
        per_constant(root.path(), "Sigma"),
        "unsupported Lean world",
        &["`Sigma._private`", v4_33_1()],
    );
}

/// The shard builder converts a closure of one readable world, and refuses a
/// foreign-world module and a second world by name.
#[test]
fn test_closure_shard_builder_world_gate() {
    let out = tempfile::tempdir().expect("out");
    let root = root_with(&[("Init", pinned_init()), ("Target", pinned_target())]);
    let built = build_shards(root.path(), &["Target"], out.path()).expect("pinned closure");
    assert_eq!(
        (built.converted, built.skipped_modules.len()),
        (2, 0),
        "{built:?}"
    );

    let root = root_with(&[
        ("Init", as_v4_33_1(pinned_init())),
        ("Target", pinned_target()),
    ]);
    assert_world_refusal(
        "build-closure-shards over a v4.33.1 Init",
        build_shards(root.path(), &["Target"], out.path()),
        "unsupported Lean world",
        &["`Init`", v4_33_1()],
    );

    let root = root_with(&[("Init", v4_8_0_leaf()), ("Target", pinned_target())]);
    assert_world_refusal(
        "build-closure-shards over a v4.8.0 Init",
        build_shards(root.path(), &["Target"], out.path()),
        "mixed Lean worlds",
        &["`Init` is of Lean v4.8.0", "`Target`"],
    );
}

/// One shard directory holding a v4.13.0 shard and a v4.8.0 shard, each
/// bound to its own on-disk `.olean`: the verifier marks one world's shard
/// servable, never both.
#[test]
fn test_closure_shard_verifier_serves_one_world() {
    let out = tempfile::tempdir().expect("out");
    let root = root_with(&[
        ("Minimal", read("v4.13.0/custom/Minimal.olean")),
        ("FactLib", v4_8_0_leaf()),
    ]);
    for leaf in ["Minimal", "FactLib"] {
        let built = build_shards(root.path(), &[leaf], out.path())
            .unwrap_or_else(|e| panic!("{leaf} alone is one world: {e}"));
        assert_eq!(built.converted, 1, "{leaf}: {built:?}");
    }
    let mut source = ShardConstantSource::from_dir(out.path()).expect("shards");
    assert_eq!(source.shard_count(), 2);
    let (any_v3, verified) =
        verify_closure_shards_against_oleans(&mut source, root.path(), &mut LeanWorldScope::new());
    assert!(any_v3, "both shards are v3 fail-closed-bound");
    assert_eq!(verified, 1, "one world's shard is servable, not both");
}

/// `stamp-verified`'s closure loader reads a target's imports through the
/// gated loaders but never the target itself: the target is held to the
/// world of its imports.
#[test]
fn test_stamp_closure_world_gate_holds_the_target() {
    let root = root_with(&[("Init", pinned_init()), ("Target", pinned_target())]);
    let target = [root.path().join("Target.olean")];
    let closure = load_targets_closure(&target, root.path(), ProofValueElision::None)
        .unwrap_or_else(|e| panic!("the pinned closure loads: {e}"));
    assert_eq!(closure.modules_loaded, 1);

    let root = root_with(&[
        ("Init", pinned_init()),
        ("Target", as_v4_33_1(pinned_target())),
    ]);
    let target = [root.path().join("Target.olean")];
    assert_world_refusal(
        "stamp-verified closure of a v4.33.1 Target",
        load_targets_closure(&target, root.path(), ProofValueElision::None)
            .map(|c| c.modules_loaded),
        "unsupported Lean world",
        &["`Target`", v4_33_1()],
    );

    let root = root_with(&[("Init", v4_8_0_leaf()), ("Target", pinned_target())]);
    let target = [root.path().join("Target.olean")];
    assert_world_refusal(
        "stamp-verified closure of a pinned Target over a v4.8.0 Init",
        load_targets_closure(&target, root.path(), ProofValueElision::None)
            .map(|c| c.modules_loaded),
        "mixed Lean worlds",
        &["`Init`", "`Target`"],
    );
}

/// A pinned-world scope, as the index leaves it over the pinned closure.
fn pinned_scope() -> LeanWorldScope {
    let mut scope = LeanWorldScope::new();
    scope
        .admit_part("Init", &pinned_init())
        .expect("the pinned leaf");
    scope
}

/// The `--closure-shards` leg admits a shard's source `.olean` before its
/// stamp and its structural gates: a v4.13.0 shard is never served to a
/// pinned closure, not even once a stamp records that its digests matched.
#[test]
fn test_per_constant_lazy_lane_serves_only_the_closure_world() {
    let out = tempfile::tempdir().expect("out");
    let root = root_with(&[("Minimal", read("v4.13.0/custom/Minimal.olean"))]);
    let built = build_shards(root.path(), &["Minimal"], out.path()).expect("v4.13.0 alone");
    assert_eq!(built.converted, 1, "{built:?}");
    let search_paths = [root.path().to_path_buf()];
    let name = Name::from_string("identity");
    let lane = || {
        LazyLane::new(
            ShardConstantSource::from_dir(out.path()).expect("shards"),
            out.path().to_path_buf(),
        )
    };

    let mut refused = lane();
    assert!(!refused.try_serve(&name, &search_paths, &mut pinned_scope()));
    assert_eq!((refused.shards_verified, refused.shards_failed), (0, 1));

    let mut own = LeanWorldScope::new();
    let mut served = lane();
    assert!(
        served.try_serve(&name, &search_paths, &mut own),
        "the shard is served to its own world"
    );
    assert_eq!(own.world(), Some("v4.13.0"));
    assert!(
        vstamp_path(&out.path().join("Minimal.mathverse")).exists(),
        "a full pass stamps the shard"
    );

    let mut stamped = lane();
    assert!(
        !stamped.try_serve(&name, &search_paths, &mut pinned_scope()),
        "a stamp records digests, never a world"
    );
}

/// `stamp-verified`'s verifier seeded with the closure's world: a shard of
/// another readable world is left unverified.
#[test]
fn test_closure_shard_verifier_refuses_a_shard_outside_its_seeded_world() {
    let out = tempfile::tempdir().expect("out");
    let root = root_with(&[("Minimal", read("v4.13.0/custom/Minimal.olean"))]);
    build_shards(root.path(), &["Minimal"], out.path()).expect("v4.13.0 alone");
    let mut source = ShardConstantSource::from_dir(out.path()).expect("shards");
    let mut world = pinned_scope();
    let (any_v3, verified) =
        verify_closure_shards_against_oleans(&mut source, root.path(), &mut world);
    assert!(any_v3);
    assert_eq!(
        verified, 0,
        "a v4.13.0 shard is not served to a pinned closure"
    );
}
