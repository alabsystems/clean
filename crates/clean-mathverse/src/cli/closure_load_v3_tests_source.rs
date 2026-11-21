// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ALWAYS-ON tests of the LOAD-TIME SOURCE-OLEAN BINDING of a v3 closure
//! shard (`verify_one_closure_shard`: the blake3 and length recomputed from
//! the on-disk `.olean` and its companions against the ones the shard header
//! records). Each tamper is aimed at one gate, and each test asserts which
//! [`ClosureShardRefusal`] refused it, not only that something did: the
//! `kv_invariance_gate` row's first arm disables this binding and needs a test
//! that ONLY the binding can turn red. Seeded by the committed
//! `tests/fixtures/olean/v4.13.0/custom/Minimal.olean`, like the other
//! `v3_closure_binding_tests*` modules (the gate's seed filter).
//!
//! This is a `#[path]`-included submodule of `closure_load`, so `super::*`
//! resolves to the parent module's (private) items.

use super::v3_closure_binding_tests_binding::build_minimal_v3_shard;
use super::*;
use crate::closure_source::ShardConstantSource;
use crate::shard::{ShardHeader, ShardReader, HEADER_SIZE};
use clean_kernel::env::ConstantSource as KernelConstantSource;

/// `pristine` with its header re-serialized after `edit`: every byte past the
/// header (the arena, the recon digests, the footer) stays as built. The lazy
/// open path skips the footer checksum, so the result still opens there.
fn with_header(pristine: &[u8], edit: impl FnOnce(&mut ShardHeader)) -> Vec<u8> {
    let mut header = ShardReader::from_bytes(pristine)
        .expect("the pristine shard parses")
        .header;
    assert_eq!(
        header.to_bytes()[..],
        pristine[..HEADER_SIZE],
        "the header re-serializes byte-identically, so an edit moves only the field it names"
    );
    edit(&mut header);
    let mut out = pristine.to_vec();
    out[..HEADER_SIZE].copy_from_slice(&header.to_bytes());
    out
}

/// The load-time gates over the one shard in `shards`, nothing marked.
fn gates_of(root: &Path, shards: &Path) -> Option<Result<(), ClosureShardRefusal>> {
    let source = ShardConstantSource::from_dir(shards)
        .expect("the lazy open path opens the shard (it skips the footer checksum)");
    assert_eq!(source.shard_count(), 1, "one shard under test");
    closure_shard_binding(
        &source,
        0,
        &build_closure_search_paths(root),
        &mut LeanWorldScope::new(),
    )
}

/// The refusal the gates must return for the shard in `shards`.
fn refusal_of(root: &Path, shards: &Path, what: &str) -> ClosureShardRefusal {
    match gates_of(root, shards) {
        Some(Err(refusal)) => refusal,
        other => panic!("{what}: a load-time gate must refuse the shard; got {other:?}"),
    }
}

/// Through the whole load-time pass the shard is v3-bound, NOT verified, and
/// serves none of the names it indexes.
fn assert_unverified_and_serves_nothing(root: &Path, shards: &Path, what: &str) {
    let mut source = ShardConstantSource::from_dir(shards).expect("source");
    let (any_v3, verified) =
        verify_closure_shards_against_oleans(&mut source, root, &mut LeanWorldScope::new());
    assert!(any_v3, "{what}: still a v3 fail-closed shard");
    assert_eq!(verified, 0, "{what}: must NOT verify");
    let names = source.servable_names_for_test();
    assert!(
        !names.is_empty(),
        "{what}: the shard indexes names, so `serves nothing` is not vacuous"
    );
    for name in names {
        assert!(
            KernelConstantSource::get(&source, &name).is_none(),
            "{what}: an unverified shard must refuse to serve {name}"
        );
    }
}

/// TEST 7: the SOURCE-OLEAN BINDING, isolated. The shard header's recorded
/// source-olean blake3 (then, separately, its recorded length) is edited; the
/// `.olean`, the arena and the stamped recon digests are left as built, so
/// the subset check, the arena recon_digest check and the Lean-world check all
/// accept the shard and the binding is the only gate that can refuse it. The
/// positive control and the refusal's variant and text pin that it did.
#[test]
fn test_load_time_hash_mismatch_refuses() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    let pristine = build_minimal_v3_shard(root.path(), shards.path());
    let shard_file = shards.path().join("Minimal.mathverse");
    let olean = root.path().join("Minimal.olean");
    let olean_bytes = std::fs::read(&olean).unwrap();

    // POSITIVE CONTROL: as built, the shard passes every load-time gate, so a
    // refusal below is the edit's.
    match gates_of(root.path(), shards.path()) {
        Some(Ok(())) => {}
        other => panic!("the pristine shard must pass every load-time gate; got {other:?}"),
    }

    let edits: [(&str, fn(&mut ShardHeader)); 2] = [
        ("recorded source-olean blake3 edited", |h| {
            h.source_olean_blake3[0] ^= 0x01;
        }),
        ("recorded source-olean length edited", |h| {
            h.source_olean_len ^= 0x01;
        }),
    ];
    for (what, edit) in edits {
        std::fs::write(&shard_file, with_header(&pristine, edit)).unwrap();
        let refusal = refusal_of(root.path(), shards.path(), what);
        assert!(
            matches!(&refusal, ClosureShardRefusal::SourceOleanMismatch { module } if module == "Minimal"),
            "{what}: the source-olean binding must be the gate that refuses; got: {refusal}"
        );
        assert_eq!(
            refusal.to_string(),
            "source-olean MISMATCH for module `Minimal` (shard is stale/swapped vs on-disk \
             .olean) — UNVERIFIED (=> eager).",
            "{what}: the binding's own message"
        );
        assert_unverified_and_serves_nothing(root.path(), shards.path(), what);
    }
    assert_eq!(
        std::fs::read(&olean).unwrap(),
        olean_bytes,
        "the source .olean was never touched"
    );
}

/// TEST 7b: one byte of the on-disk source `.olean` flipped at its middle (the
/// tamper TEST 7 used until 2026-11-17). The flip does two things, each
/// refused by its own gate. It moves the olean's digest, so with the shard as
/// built the BINDING refuses it, before the subset check runs. And it leaves
/// the olean unparseable (measured 2026-11-17: `region error: unsupported typed
/// Name layout`), so once the header records the flipped bytes' own digest and
/// the binding accepts, the SUBSET CHECK's parse refuses it. Either way the
/// shard is not verified and serves nothing.
#[test]
fn test_load_time_unparseable_olean_flip_refuses() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    let pristine = build_minimal_v3_shard(root.path(), shards.path());

    let olean = root.path().join("Minimal.olean");
    let mut data = std::fs::read(&olean).unwrap();
    let mid = data.len() / 2;
    data[mid] ^= 0xFF;
    std::fs::write(&olean, &data).unwrap();

    // As built: the header records the pristine olean, so the binding refuses.
    let what = "olean byte flipped, shard as built";
    let refusal = refusal_of(root.path(), shards.path(), what);
    assert!(
        matches!(&refusal, ClosureShardRefusal::SourceOleanMismatch { module } if module == "Minimal"),
        "{what}: the binding runs first and must refuse; got: {refusal}"
    );
    assert_unverified_and_serves_nothing(root.path(), shards.path(), what);

    // Header re-bound to the flipped bytes: the binding accepts, the parse refuses.
    let what = "olean byte flipped, header re-bound to the flipped bytes";
    let (hash, len) = source_olean_digest(&olean).unwrap();
    let rebound = with_header(&pristine, |h| {
        h.source_olean_blake3 = hash;
        h.source_olean_len = len;
    });
    std::fs::write(shards.path().join("Minimal.mathverse"), rebound).unwrap();
    let refusal = refusal_of(root.path(), shards.path(), what);
    assert!(
        matches!(&refusal, ClosureShardRefusal::OleanUnparseable { path, .. } if path.ends_with("Minimal.olean")),
        "{what}: the subset check's parse must be the gate that refuses; got: {refusal}"
    );
    assert!(
        refusal.to_string().contains("for the subset check failed"),
        "{what}: the parse refusal's own message; got: {refusal}"
    );
    assert_unverified_and_serves_nothing(root.path(), shards.path(), what);
}
