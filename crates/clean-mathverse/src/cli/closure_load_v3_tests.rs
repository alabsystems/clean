// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ALWAYS-ON tests for the v3 closure-binding fail-closed hardening — the
//! BUILD-TIME oracle + digest + source-binding half (CLEAN_LAZY_CLOSURE
//! strictly-no-weaker). The LOAD-TIME content/arena binding + serving half lives
//! in `closure_load_v3_tests_binding.rs` (split to keep each file under the
//! 500-line paragon). Seeded by the committed
//! `tests/fixtures/olean/v4.13.0/custom/Minimal.olean` so they run with no
//! Mathlib checkout. See the no-weaker certificate in
//! `docs/SOUNDNESS_CERTIFICATE.md`.
//!
//! This is a `#[path]`-included submodule of `closure_load`, so `super::*`
//! resolves to the parent module's (private) items.

use super::*;
use crate::shard::{ShardMmapReader, ShardReader, ShardWriter};

/// Path to the committed `Minimal.olean` fixture (def identity + theorem id_id).
fn minimal_olean() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("workspace root")
}

/// TEST 3: `source_olean_digest` is byte-identical build-vs-load for the SAME
/// inputs; tampering ONLY `.olean.private` flips the hash; an absent companion
/// (len 0) is unambiguous.
#[test]
fn test_source_olean_digest_binds_companions() {
    let dir = tempfile::tempdir().unwrap();
    let base = dir.path().join("M.olean");
    std::fs::write(&base, b"BASE-OLEAN-BYTES").unwrap();

    // No companions: build == load, and the length is base+8.
    let (h0, l0) = source_olean_digest(&base).unwrap();
    let (h0b, l0b) = source_olean_digest(&base).unwrap();
    assert_eq!(h0, h0b);
    assert_eq!(l0, l0b);
    assert_eq!(l0, 8 + b"BASE-OLEAN-BYTES".len() as u64 + 8 + 8); // base + 2 absent

    // Adding a `.private` companion changes the digest (companions are bound).
    let priv_path = dir.path().join("M.olean.private");
    std::fs::write(&priv_path, b"PROOF-PRIVATE").unwrap();
    let (h1, l1) = source_olean_digest(&base).unwrap();
    assert_ne!(h0, h1, "present .private must change the digest");
    assert_ne!(l0, l1);

    // Tampering ONLY the `.private` flips the hash while base is unchanged.
    std::fs::write(&priv_path, b"PROOF-PRIVATE-TAMPERED").unwrap();
    let (h2, _l2) = source_olean_digest(&base).unwrap();
    assert_ne!(
        h1, h2,
        "tampering .private flips the hash (proves it is bound)"
    );
}

/// TEST 4: builder fail-closed POSITIVE on the committed Minimal.olean:
/// the build succeeds, the header carries the recomputed source digest,
/// fail_closed_verified==1, every served constant has a recorded reducibility
/// and a recon_digest, and the served set is non-empty.
#[test]
fn test_builder_fail_closed_positive_minimal() {
    let (bytes, _dropped) =
        build_kernel_faithful_shard(&minimal_olean(), "Minimal").expect("build");
    let reader = ShardReader::from_bytes(&bytes).expect("read v3 shard");
    assert_eq!(reader.header.version, crate::shard::SHARD_VERSION);
    assert_eq!(reader.header.fail_closed_verified, 1, "gate must pass");
    assert_ne!(reader.header.source_olean_blake3, [0u8; 32], "source bound");

    // The header digest equals a fresh recompute over the SAME olean.
    let (h, l) = source_olean_digest(&minimal_olean()).unwrap();
    assert_eq!(reader.header.source_olean_blake3, h);
    assert_eq!(reader.header.source_olean_len, l);

    // module_name_idx resolves to "Minimal".
    let mod_name = reader
        .strings
        .get(reader.header.module_name_idx as usize)
        .cloned()
        .unwrap_or_default();
    assert_eq!(mod_name, "Minimal");

    // Every served constant carries reducibility + recon_digest, set non-empty.
    let mut served = 0usize;
    for c in &reader.constants {
        if crate::closure_source::servable_kind(c.decl_kind) {
            served += 1;
            assert!(c.reducibility().is_some(), "recorded reducibility");
            assert!(c.recon_digest().is_some(), "recon digest stamped");
        }
    }
    assert!(served > 0, "served set must be non-empty (non-vacuous)");
}

/// TEST 5 (builder fail-closed NEGATIVE): the round-trip oracle's verdict
/// check `verify_round_trip_equal` REFUSES a reconstruction that diverges on
/// any guarded axis — reducibility CATEGORY, an FVar (not FVar-free),
/// structural type/value divergence, kind, or level_params — so a constant
/// that fails is NOT emitted (the builder would return StampClosure).
#[test]
fn test_round_trip_oracle_refuses_divergence() {
    use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
    use clean_kernel::expr::{Expr, FVarId};
    use clean_kernel::level::Level;

    let mk =
        |ty: Expr, value: Option<Expr>, red: Reducibility, kind: ConstantKind, lp: Vec<Name>| {
            ConstantInfo::new_with_reducibility(Name::from_string("X"), lp, ty, value, red, kind)
        };
    let sort0 = || Expr::sort(Level::zero());

    // Identical => accepted (the positive control).
    let base = mk(
        sort0(),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Definition,
        vec![],
    );
    assert!(verify_round_trip_equal(&base, &base).is_ok());

    // Reducibility CATEGORY divergence (Regular vs Opaque) => refused.
    let opaque = mk(
        sort0(),
        Some(sort0()),
        Reducibility::Opaque,
        ConstantKind::Definition,
        vec![],
    );
    assert!(
        verify_round_trip_equal(&base, &opaque).is_err(),
        "category divergence refused"
    );

    // FVar present => refused (not FVar-free).
    let with_fvar = mk(
        Expr::fvar(FVarId::new(7)),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Definition,
        vec![],
    );
    assert!(
        verify_round_trip_equal(&base, &with_fvar).is_err(),
        "FVar refused"
    );

    // Structural type divergence (Sort vs Pi) => refused.
    let pi_ty = mk(
        Expr::pi(clean_kernel::expr::BinderInfo::Default, sort0(), sort0()),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Definition,
        vec![],
    );
    assert!(
        verify_round_trip_equal(&base, &pi_ty).is_err(),
        "structural type divergence refused"
    );

    // Kind divergence => refused.
    let thm = mk(
        sort0(),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Theorem,
        vec![],
    );
    assert!(
        verify_round_trip_equal(&base, &thm).is_err(),
        "kind divergence refused"
    );

    // level_params divergence => refused.
    let lp = mk(
        sort0(),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Definition,
        vec![Name::from_string("u")],
    );
    assert!(
        verify_round_trip_equal(&base, &lp).is_err(),
        "level_params divergence refused"
    );

    // value presence divergence => refused.
    let no_val = mk(
        sort0(),
        None,
        Reducibility::Regular(0),
        ConstantKind::Definition,
        vec![],
    );
    assert!(
        verify_round_trip_equal(&base, &no_val).is_err(),
        "value-presence divergence refused"
    );
}

/// TEST 5b (the MData fix): the round-trip oracle MUST treat an `MData`-bearing
/// source constant as EQUAL to its MData-stripped reconstruction. The eager
/// `convert_expr` import RETAINS `MData` while the shard `FlatBuilder` STRIPS it,
/// so without the `fold_mdata`-peel in `types_equal_ignoring_binder_info` every
/// MData-bearing served constant would FAIL `verify_round_trip_equal`,
/// StampClosure the whole module, and force it off the lazy path — killing the
/// speedup on real Mathlib. `Minimal.olean` has ZERO MData, so this is invisible
/// without a SYNTHETIC MData-bearing constant; we build one and assert:
///   (1) src (MData-on type+value) vs rc (MData-stripped) => oracle ACCEPTS;
///   (2) the MData genuinely differs structurally (raw `==` is FALSE), so the
///       accept is the peel doing its job, not a vacuous identity.
#[test]
fn test_mdata_bearing_constant_passes_oracle() {
    use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
    use clean_kernel::expr::Expr;
    use clean_kernel::level::Level;

    let sort0 = || Expr::sort(Level::zero());
    // An MData wrapper with one annotation (content is irrelevant — the kernel
    // ignores it; we only need a non-empty map so the node is a real MData).
    let mdata_wrap = |e: Expr| -> Expr {
        let meta: clean_kernel::expr::MDataMap = vec![(
            Name::from_string("pp"),
            clean_kernel::expr::MDataValue::Bool(true),
        )];
        Expr::mdata(meta, e)
    };

    // SRC: the eager-shaped constant — MData on BOTH type and value.
    let src = ConstantInfo::new_with_reducibility(
        Name::from_string("MDataConst"),
        vec![],
        mdata_wrap(sort0()),
        Some(mdata_wrap(sort0())),
        Reducibility::Regular(0),
        ConstantKind::Definition,
    );
    // RC: the shard-reconstructed constant — SAME logical content, MData STRIPPED
    // (exactly what the FlatBuilder encoder produces).
    let rc = ConstantInfo::new_with_reducibility(
        Name::from_string("MDataConst"),
        vec![],
        sort0(),
        Some(sort0()),
        Reducibility::Regular(0),
        ConstantKind::Definition,
    );

    // PRECONDITION: the two are NOT raw-equal (the MData genuinely differs), so a
    // pass below is the MData-peel, not a trivial identity.
    assert_ne!(
        src.type_, rc.type_,
        "the MData wrapper must make the raw types differ (else the test is vacuous)"
    );
    assert!(
        crate::inductive_replay::types_equal_ignoring_binder_info(&src.type_, &rc.type_),
        "MData-peel must make the wrapped and unwrapped types compare equal"
    );

    // THE FIX: the build-time oracle accepts the MData-bearing src vs the
    // MData-stripped reconstruction.
    assert!(
        verify_round_trip_equal(&src, &rc).is_ok(),
        "MData-bearing source must pass the round-trip oracle against its \
         MData-stripped reconstruction (the 'modulo MData' claim)"
    );
}

/// TEST 8 (footer-skip gap): patch one expr-arena byte of the SHARD keeping
/// section lengths constant. The source-olean hash still mismatches (shard
/// bytes changed, olean did not is irrelevant — the binding is to the olean,
/// which the arena patch does NOT change), but the shard's OWN content no
/// longer matches what was verified. We assert the recon_digest tripwire fires
/// for the patched constant on re-materialize (documented as tripwire-only).
#[test]
fn test_arena_tamper_tripwire() {
    let (bytes, _dropped) =
        build_kernel_faithful_shard(&minimal_olean(), "Minimal").expect("build");
    // Re-open and find a served constant + its recon_digest.
    let reader = ShardMmapReader::open_lazy_from_bytes(&bytes).expect("reopen");
    let mut served_idx = None;
    for (i, c) in reader.constants.iter().enumerate() {
        if crate::closure_source::servable_kind(c.decl_kind) && c.recon_digest().is_some() {
            served_idx = Some(i as u32);
            break;
        }
    }
    let idx = served_idx.expect("a served constant");
    let stamped = reader.constants[idx as usize].recon_digest().unwrap();
    let rc =
        crate::closure_source::materialize_constant_from_reader(&reader, idx).expect("materialize");
    // The recon_digest of the faithful reconstruction matches the stamped one.
    assert_eq!(
        recon_digest_of(&rc),
        stamped,
        "tripwire matches on faithful bytes"
    );
    drop(reader);

    // Length-preserving corruption: flip ONE byte at a series of positions
    // across the file body (the raw FlatExpr arena + constant headers live in
    // the back half). The recon_digest is a CORRUPTION TRIPWIRE (NOT a tamper
    // boundary — an adversary editing the arena also edits `_pad2`): we assert
    // that SOME single-byte corruption is caught (digest mismatch, failed
    // reconstruct, or refused open). The SOUNDNESS boundary is the load-time
    // olean hash, not this digest — see the no-weaker certificate.
    let detects_corruption = |pos: usize| -> bool {
        let mut tampered = bytes.clone();
        tampered[pos] ^= 0x01;
        match ShardMmapReader::open_lazy_from_bytes(&tampered) {
            Err(_) => true, // refused open (bounds/format) — corruption caught
            Ok(treader) => treader.constants.iter().enumerate().any(|(i, c)| {
                if !crate::closure_source::servable_kind(c.decl_kind) {
                    return false;
                }
                let Some(stamp) = c.recon_digest() else {
                    return false;
                };
                match crate::closure_source::materialize_constant_from_reader(&treader, i as u32) {
                    Some(rc2) => recon_digest_of(&rc2) != stamp,
                    None => true, // could not reconstruct => corruption
                }
            }),
        }
    };
    // Target the FlatExpr ARENA + CONSTANT-HEADERS region precisely (computed
    // from the public header fields), NOT the 256KB bloom filter that
    // dominates the tiny fixture shard. Arena starts after the header + zstd
    // string table + raw level pool; constant headers follow the arena.
    let hdr = ShardReader::from_bytes(&bytes).expect("header").header;
    let level_pool = hdr.level_count as usize * clean_kernel::flat::FlatLevel::SIZE;
    let arena = hdr.expr_count as usize * clean_kernel::flat::FlatExpr::SIZE;
    let const_hdrs = hdr.constant_count as usize * crate::types::MathverseConstantHeader::SIZE;
    let arena_start = crate::shard::HEADER_SIZE + hdr.string_data_len as usize + level_pool;
    let region_end = arena_start + arena + const_hdrs;
    let any_caught = (arena_start..region_end).any(detects_corruption);
    assert!(
        any_caught,
        "the recon_digest tripwire must catch SOME single-byte arena/header corruption"
    );
}

/// TEST 12: KV-stamp restamp threading. Round-trip a v3 fail-closed shard
/// through `ShardWriter::from_reader` -> `write` and assert the source hash,
/// module name, and fail_closed_verified SURVIVE (are not zeroed).
#[test]
fn test_restamp_preserves_v3_binding() {
    let (bytes, _dropped) =
        build_kernel_faithful_shard(&minimal_olean(), "Minimal").expect("build");
    let reader = ShardReader::from_bytes(&bytes).expect("read");
    assert_eq!(reader.header.fail_closed_verified, 1);
    let orig_hash = reader.header.source_olean_blake3;
    let orig_len = reader.header.source_olean_len;

    // Restamp: from_reader -> write (the KV-stamp rewrite path).
    let writer = ShardWriter::from_reader(&reader);
    let mut out = Vec::new();
    writer.write(&mut out).expect("rewrite");
    let restamped = ShardReader::from_bytes(&out).expect("read restamped");

    assert_eq!(
        restamped.header.fail_closed_verified, 1,
        "flag survived restamp"
    );
    assert_eq!(
        restamped.header.source_olean_blake3, orig_hash,
        "hash survived"
    );
    assert_eq!(restamped.header.source_olean_len, orig_len, "len survived");
    let mod_name = restamped
        .strings
        .get(restamped.header.module_name_idx as usize)
        .cloned()
        .unwrap_or_default();
    assert_eq!(mod_name, "Minimal", "module name survived restamp");
}

/// TEST 13: synthetic `from_merged_parts` readers (no source olean,
/// fail_closed_verified=0) are SKIPPED by the load-time check (never marked,
/// never spuriously block).
#[test]
fn test_synthetic_merged_reader_skipped() {
    // A `from_merged_parts` reader is synthetic; round-trip an empty one
    // through to bytes to confirm its header has the zero binding.
    let synthetic = ShardReader::from_merged_parts(
        vec![String::new()],
        vec![clean_kernel::flat::FlatLevel::zero()],
        vec![],
        vec![],
        vec![],
    );
    assert_eq!(synthetic.header.source_olean_blake3, [0u8; 32]);
    assert_eq!(synthetic.header.fail_closed_verified, 0);
    // Through the writer/reader round-trip the binding stays zero (synthetic).
    let w = ShardWriter::from_reader(&synthetic);
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    let rd = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(
        rd.header.fail_closed_verified, 0,
        "synthetic stays un-served"
    );
    assert_eq!(rd.header.source_olean_blake3, [0u8; 32]);
}
