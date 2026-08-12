// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ALWAYS-ON tests for the v3 closure-binding fail-closed hardening — the
//! LOAD-TIME content/arena binding + serving half (split from
//! `closure_load_v3_tests.rs` to keep each file under the 500-line paragon).
//! Seeded by the committed `tests/fixtures/olean/v4.13.0/custom/Minimal.olean`
//! so they run with no Mathlib checkout. See the no-weaker certificate in
//! `docs/SOUNDNESS_CERTIFICATE.md`.
//!
//! This is a `#[path]`-included submodule of `closure_load`, so `super::*`
//! resolves to the parent module's (private) items.

use super::*;
use crate::closure_source::ShardConstantSource;
use crate::shard::{ShardReader, ShardWriter};
use clean_kernel::env::ConstantSource as KernelConstantSource;

/// Path to the committed `Minimal.olean` fixture (def identity + theorem id_id).
fn minimal_olean() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .map(|root| root.join("tests/fixtures/olean/v4.13.0/custom/Minimal.olean"))
        .expect("workspace root")
}

/// Copy `Minimal.olean` into `<root>/Minimal.olean` so the closure resolver
/// finds it for module name "Minimal", and build the v3 fail-closed shard
/// into `<shards>/Minimal.mathverse`. Returns the shard bytes.
fn build_minimal_v3_shard(root: &Path, shards: &Path) -> Vec<u8> {
    std::fs::create_dir_all(shards).unwrap();
    let olean = root.join("Minimal.olean");
    std::fs::copy(minimal_olean(), &olean).expect("copy fixture olean");
    let (bytes, _dropped) = build_kernel_faithful_shard(&olean, "Minimal").expect("build v3 shard");
    std::fs::write(shards.join("Minimal.mathverse"), &bytes).unwrap();
    bytes
}

/// TEST 6 (independent parity): the lazy materialize of every served constant
/// equals the INDEPENDENT eager clean-olean conversion (NOT derived from the
/// lazy source), modulo binder-info; and `add_decl` agrees. This catches an
/// encoder divergence the existing `lazy_closure_verdict_matches_eager`
/// (both legs from the lazy source) cannot.
#[test]
fn test_independent_eager_vs_lazy_parity_minimal() {
    use clean_kernel::env::{Environment, TrustedEnvExt};

    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    build_minimal_v3_shard(root.path(), shards.path());

    // Build the lazy source and run the EXACT load-time verification.
    let mut source = ShardConstantSource::from_dir(shards.path()).expect("source");
    let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
    assert!(any_v3, "the v3 fail-closed shard must be recognized");
    assert_eq!(
        verified, 1,
        "the Minimal shard must verify against its olean"
    );

    // INDEPENDENT eager leg: clean-olean convert_expr from the .olean.
    let parsed =
        crate::lean4::olean::olean_bridge::parse_target_module_with_proofs(&minimal_olean())
            .expect("parse");
    let mut eager_infos: std::collections::HashMap<Name, clean_kernel::env::ConstantInfo> =
        std::collections::HashMap::new();
    for c in &parsed.constants {
        if let Ok(Some(ci)) = clean_olean::convert_parsed_constant_to_const_info(c) {
            eager_infos.insert(ci.name.clone(), ci);
        }
    }

    // Every served name's lazy materialize must match the independent eager.
    let served_names = source.servable_names_for_test();
    assert!(!served_names.is_empty(), "served set non-empty");
    let mut checked = 0usize;
    for name in &served_names {
        let lazy = KernelConstantSource::get(&source, name).expect("lazy serves");
        let eager = eager_infos.get(name).expect("eager has it too");
        assert_eq!(lazy.kind, eager.kind, "{name}: kind parity");
        assert_eq!(
            reducibility_category(lazy.reducibility),
            reducibility_category(eager.reducibility),
            "{name}: reducibility category parity"
        );
        assert_eq!(
            lazy.level_params, eager.level_params,
            "{name}: level_params"
        );
        assert!(
            crate::inductive_replay::types_equal_ignoring_binder_info(&lazy.type_, &eager.type_),
            "{name}: type parity modulo binder-info"
        );
        checked += 1;
    }
    assert!(checked > 0);

    // add_decl(id_id) Ok-parity: eager-built env vs lazy-served env.
    let id_id = Name::from_string("id_id");
    // FIXTURE-DRIFT GUARD: assert the fixture actually carries `id_id` BEFORE the
    // `if let` guards, so a future fixture change cannot silently skip the
    // add_decl kernel-parity assertion (the core of this test) and leave it
    // vacuously green.
    assert!(
        eager_infos.contains_key(&id_id),
        "Minimal.olean fixture must declare `id_id` (the add_decl parity target)"
    );
    if let Some(eager_ci) = eager_infos.get(&id_id) {
        if let Some(decl) = constant_info_to_declaration(eager_ci) {
            // EAGER: extend env with the independent eager closure.
            let mut eager_env = Environment::with_prelude();
            let prelude: std::collections::HashSet<Name> = Environment::with_prelude()
                .constants()
                .map(|c| c.name.clone())
                .collect();
            eager_env.extend_constants_unchecked(
                eager_infos
                    .values()
                    .filter(|c| c.name != id_id && !prelude.contains(&c.name))
                    .cloned(),
            );
            let eager_ok = eager_env.add_decl(decl.clone()).is_ok();

            // LAZY: serve the closure from the source.
            let mut lazy_env = Environment::with_prelude();
            lazy_env.set_constant_source(Arc::new(source));
            let lazy_ok = lazy_env.add_decl(decl).is_ok();
            assert_eq!(eager_ok, lazy_ok, "add_decl(id_id) Ok-parity eager==lazy");
        }
    }
}

/// TEST 7: load-time source-olean MISMATCH -> not verified -> not served.
/// Flip one byte of the on-disk source `.olean` after building the shard.
#[test]
fn test_load_time_hash_mismatch_refuses() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    build_minimal_v3_shard(root.path(), shards.path());

    // Corrupt the on-disk olean (one byte) so its recomputed digest mismatches.
    let olean = root.path().join("Minimal.olean");
    let mut data = std::fs::read(&olean).unwrap();
    let mid = data.len() / 2;
    data[mid] ^= 0xFF;
    std::fs::write(&olean, &data).unwrap();

    let mut source = ShardConstantSource::from_dir(shards.path()).expect("source");
    let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
    assert!(any_v3, "still a v3 fail-closed shard");
    assert_eq!(verified, 0, "mismatched olean must NOT verify");
    // No served name resolves (all => eager).
    for name in source.servable_names_for_test() {
        assert!(
            KernelConstantSource::get(&source, &name).is_none(),
            "unverified shard must refuse to serve {name}"
        );
    }
}

/// TEST 8b (THE no-weaker BLOCKING-FIX PROOF): corrupt ONE FlatExpr-arena byte
/// of the SHARD *without touching the header or the source `.olean`*, so the
/// source-olean-hash gate and the subset gate still PASS, then drive the EXACT
/// load-time `verify_closure_shards_against_oleans` and assert the shard is left
/// UNVERIFIED (`verified == 0`) and serves NOTHING (=> HARD EAGER FALLBACK).
///
/// This is what proves the load-time arena recon_digest gate closes the gap: a
/// stale/corrupted/swapped arena that an intact header would otherwise launder
/// into a "verified" serve is now refused at LOAD time, not just at build time.
#[test]
fn test_load_time_arena_corruption_refuses() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    let bytes = build_minimal_v3_shard(root.path(), shards.path());

    // SANITY: the pristine shard verifies and serves (the positive control), so a
    // later `verified == 0` is attributable to the arena corruption alone.
    {
        let mut pristine = ShardConstantSource::from_dir(shards.path()).expect("source");
        let (any_v3, verified) = verify_closure_shards_against_oleans(&mut pristine, root.path());
        assert!(any_v3, "pristine shard is v3 fail-closed-bound");
        assert_eq!(verified, 1, "pristine shard verifies (positive control)");
    }

    // Locate the FlatExpr ARENA region precisely from the PUBLIC header fields,
    // and corrupt one byte INSIDE it (length-preserving), leaving the 256-bit
    // header source-olean digest, fail_closed marker, module name, and the
    // on-disk `.olean` ALL untouched. The arena lives after the header + zstd
    // string table + raw level pool; we patch a byte in its first half so the
    // change lands on a real FlatExpr node (not const-header padding).
    let hdr = ShardReader::from_bytes(&bytes).expect("header").header;
    let level_pool = hdr.level_count as usize * clean_kernel::flat::FlatLevel::SIZE;
    let arena_start = crate::shard::HEADER_SIZE + hdr.string_data_len as usize + level_pool;
    let arena_len = hdr.expr_count as usize * clean_kernel::flat::FlatExpr::SIZE;
    assert!(arena_len > 0, "shard has a non-empty expr arena");

    // The header bytes (0..HEADER_SIZE) and the source-olean are NOT touched, so
    // the source-olean-hash gate STILL passes — only the served arena diverges.
    // Try several byte positions across the arena; at least ONE must flip a
    // served constant's reconstruction so the recon_digest gate fires. (A byte in
    // an unused-tag slot could be inert; sweeping makes the test robust.)
    let mut caught_any = false;
    for off in 0..arena_len {
        let mut tampered = bytes.clone();
        let pos = arena_start + off;
        let before = tampered[pos];
        tampered[pos] = before ^ 0x01;
        std::fs::write(shards.path().join("Minimal.mathverse"), &tampered).unwrap();

        // The header (and thus the source-olean digest it stores) is unchanged.
        if let Ok(treader) = ShardReader::from_bytes(&tampered) {
            assert_eq!(
                treader.header.source_olean_blake3, hdr.source_olean_blake3,
                "arena patch must NOT change the header source-olean digest"
            );
            assert_eq!(treader.header.fail_closed_verified, 1, "marker intact");
        }

        // open_lazy can refuse a malformed arena outright (bounds/format) — that is
        // ALSO a refusal (=> eager). Only when it opens do we drive the verify.
        let Ok(mut source) = ShardConstantSource::from_dir(shards.path()) else {
            caught_any = true;
            break;
        };
        let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
        if !any_v3 {
            // A corrupted header field flipped the fail-closed marker etc.; still a
            // refusal. (Should not happen for an arena-only patch, but it is sound.)
            caught_any = true;
            break;
        }
        if verified == 0 {
            // The arena recon_digest gate refused this corruption: NOTHING serves.
            for name in source.servable_names_for_test() {
                assert!(
                    KernelConstantSource::get(&source, &name).is_none(),
                    "an arena-corrupted, unverified shard must serve nothing ({name})"
                );
            }
            caught_any = true;
            break;
        }
    }
    assert!(
        caught_any,
        "load-time arena recon_digest gate must REFUSE some single-byte arena \
         corruption (the no-weaker blocking fix) — header + source-olean intact"
    );
}

/// TEST 9: FOREIGN-CONSTANT LAUNDERING is refused. Build a shard that declares
/// a foreign module's name (its `module_name` is "Innocent" but it serves a
/// name outside that namespace). The subset check leaves it UNVERIFIED.
#[test]
fn test_foreign_constant_laundering_refused() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(shards.path()).unwrap();

    // Build a hand-made v3 shard declaring module "Innocent" but serving a
    // FOREIGN name "Mathlib.Logic.Basic.mem_ite", with a matching on-disk
    // "Innocent.olean" whose digest we stamp so the hash check PASSES — only
    // the subset check should refuse it.
    let olean = root.path().join("Innocent.olean");
    std::fs::write(&olean, b"INNOCENT-OLEAN").unwrap();
    let (src_hash, src_len) = source_olean_digest(&olean).unwrap();

    let mut w = ShardWriter::new();
    let l0 = w.add_level(clean_kernel::flat::FlatLevel::zero());
    let ty = w.add_expr(clean_kernel::flat::FlatExpr::sort(l0));
    let name_idx = w.add_string("Mathlib.Logic.Basic.mem_ite");
    let val = w.add_expr(clean_kernel::flat::FlatExpr::sort(l0));
    w.add_constant(crate::types::MathverseConstantHeader {
        name_idx,
        type_idx: ty,
        value_idx: val,
        source_system: crate::types::SourceSystem::Lean4 as u8,
        import_confidence: crate::types::ImportConfidence::Unverified as u8,
        content_domain: crate::types::ContentDomain::PureMath as u8,
        decl_kind: crate::types::DeclKind::Theorem as u8,
        axiom_profile: crate::types::AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    w.set_source_olean_digest(src_hash, src_len);
    w.set_module_name("Innocent");
    w.set_fail_closed_verified(true);
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    std::fs::write(shards.path().join("Innocent.mathverse"), &buf).unwrap();

    let mut source = ShardConstantSource::from_dir(shards.path()).expect("source");
    let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
    assert!(any_v3, "it IS a v3 fail-closed shard");
    assert_eq!(
        verified, 0,
        "foreign-name laundering must be refused by the subset check"
    );
    let foreign = Name::from_string("Mathlib.Logic.Basic.mem_ite");
    assert!(
        KernelConstantSource::get(&source, &foreign).is_none(),
        "laundered foreign constant must never be served"
    );
}

/// TEST 10: fail_closed_verified=0 (a non-fidelity writer) with a VALID source
/// hash is never served (the on-disk fidelity marker seals fidelity, not just
/// identity).
#[test]
fn test_fail_closed_missing_not_served() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    std::fs::create_dir_all(shards.path()).unwrap();
    let olean = root.path().join("NoGate.olean");
    std::fs::write(&olean, b"NOGATE-OLEAN").unwrap();
    let (src_hash, src_len) = source_olean_digest(&olean).unwrap();

    let mut w = ShardWriter::new();
    let l0 = w.add_level(clean_kernel::flat::FlatLevel::zero());
    let ty = w.add_expr(clean_kernel::flat::FlatExpr::sort(l0));
    let val = w.add_expr(clean_kernel::flat::FlatExpr::sort(l0));
    let name_idx = w.add_string("NoGate.thing");
    w.add_constant(crate::types::MathverseConstantHeader {
        name_idx,
        type_idx: ty,
        value_idx: val,
        source_system: crate::types::SourceSystem::Lean4 as u8,
        import_confidence: crate::types::ImportConfidence::Unverified as u8,
        content_domain: crate::types::ContentDomain::PureMath as u8,
        decl_kind: crate::types::DeclKind::Theorem as u8,
        axiom_profile: crate::types::AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    w.set_source_olean_digest(src_hash, src_len);
    w.set_module_name("NoGate");
    // NOTE: fail_closed_verified is NOT set (defaults false).
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    std::fs::write(shards.path().join("NoGate.mathverse"), &buf).unwrap();

    let mut source = ShardConstantSource::from_dir(shards.path()).expect("source");
    let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
    assert!(
        !any_v3,
        "a shard without fail_closed_verified is not a v3-bound shard"
    );
    assert_eq!(verified, 0);
    assert!(
        KernelConstantSource::get(&source, &Name::from_string("NoGate.thing")).is_none(),
        "no fail-closed marker => never served"
    );
}

/// TEST 11: a v2 shard in the closure dir is refused by the lazy open path
/// (from_bytes_strict), so `from_dir` errors -> the dispatcher falls back to
/// eager. (A v2 closure dir cannot even build a lazy source.)
#[test]
fn test_v2_shard_in_closure_dir_refused() {
    let shards = tempfile::tempdir().unwrap();
    // A genuine v2 shard: write a one-constant shard, then patch its version
    // word from 3 to 2 (length-preserving) and re-checksum.
    let mut w = ShardWriter::new();
    let l0 = w.add_level(clean_kernel::flat::FlatLevel::zero());
    let ty = w.add_expr(clean_kernel::flat::FlatExpr::sort(l0));
    let n = w.add_string("V2.thing");
    w.add_constant(crate::types::MathverseConstantHeader {
        name_idx: n,
        type_idx: ty,
        value_idx: crate::types::NO_VALUE,
        source_system: crate::types::SourceSystem::Lean4 as u8,
        import_confidence: crate::types::ImportConfidence::Unverified as u8,
        content_domain: crate::types::ContentDomain::PureMath as u8,
        decl_kind: crate::types::DeclKind::Definition as u8,
        axiom_profile: crate::types::AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    // Patch version 3 -> 2 at bytes 4..8, then recompute the footer checksum
    // over everything before the 64-byte footer.
    buf[4..8].copy_from_slice(&crate::shard::SHARD_VERSION_V2.to_le_bytes());
    let footer_start = buf.len() - 64;
    let hash = blake3::hash(&buf[..footer_start]);
    buf[footer_start..footer_start + 32].copy_from_slice(hash.as_bytes());
    std::fs::write(shards.path().join("V2.mathverse"), &buf).unwrap();

    // The lazy open path requires v3 -> from_dir errors out.
    let res = ShardConstantSource::from_dir(shards.path());
    assert!(
        res.is_err(),
        "a v2 closure shard must be refused on the lazy path"
    );
}

/// TEST 14 (prelude-stub ordering): the verify+mark must run BEFORE any
/// `get()`. We assert the structural ordering by confirming that, with the
/// load-time verification NOT yet run, a freshly-built source serves NOTHING
/// (every shard defaults unverified) — so the prelude-stub override loop,
/// which runs after verification, cannot `forget_decl` based on an unverified
/// shard's `get()`.
#[test]
fn test_prelude_stub_ordering_unverified_serves_nothing() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    build_minimal_v3_shard(root.path(), shards.path());
    let source = ShardConstantSource::from_dir(shards.path()).expect("source");
    // BEFORE verify: nothing is served (default-unverified).
    for name in source.servable_names_for_test() {
        assert!(
            KernelConstantSource::get(&source, &name).is_none(),
            "an unverified shard must serve nothing before the load-time check"
        );
    }
}

/// TEST 15 (THE OOM-skip REGRESSION for gap #1): the demand-paged base was INERT
/// because `build_lazy_base` built the `ShardConstantSource` but never ran the
/// load-time content-binding verification, so every shard stayed `shard_verified
/// = false` and `get()` returned `None` for EVERY name (closure_source.rs ~L415).
/// The coverage gate then saw the WHOLE closure as missing and eager-full-loaded
/// every owning module — silently re-inflating RSS to the fully-eager floor while
/// masquerading as a "lazy base". This asserts the exact before→after transition
/// on ONE source instance: BEFORE `verify_closure_shards_against_oleans`, a served
/// name resolves to `None` (the inert base — "served nothing"); AFTER, the SAME
/// name resolves to `Some` (the base now serves the definitional bulk, so the
/// coverage gate is satisfied and the OOM bound holds).
#[test]
fn test_bounded_base_serves_after_load_time_verify() {
    let root = tempfile::tempdir().unwrap();
    let shards = tempfile::tempdir().unwrap();
    build_minimal_v3_shard(root.path(), shards.path());

    // `from_dir` is exactly what `build_lazy_base` calls; the shard defaults
    // UNVERIFIED, so this instance is the INERT base the bug left in place.
    let mut source = ShardConstantSource::from_dir(shards.path()).expect("source");
    let served = source
        .servable_names_for_test()
        .into_iter()
        .find(|n| KernelConstantSource::get(&source, n).is_none())
        .expect("the Minimal shard indexes at least one servable name");

    // BEFORE the fix's `verify_closure_shards_against_oleans` call: the base is
    // inert — `get()` serves NOTHING (this is what drove the silent OOM re-inflation).
    assert!(
        KernelConstantSource::get(&source, &served).is_none(),
        "regression: an un-verified bounded base must serve nothing (the inert-base bug)"
    );

    // The fix: run the load-time content-binding verification (the call
    // `build_lazy_base` now makes right after `from_dir`).
    let (any_v3, verified) = verify_closure_shards_against_oleans(&mut source, root.path());
    assert!(any_v3, "the Minimal shard is v3 fail-closed-bound");
    assert_eq!(verified, 1, "the Minimal shard verifies against its olean");

    // AFTER the fix: the SAME served name now resolves — the bounded base actually
    // serves the definitional bulk, so the coverage gate no longer eager-repairs
    // the whole closure and the OOM bound is in effect.
    let ci = KernelConstantSource::get(&source, &served)
        .expect("regression: after load-time verify the bounded base MUST serve the constant");
    assert_eq!(ci.name, served, "the served constant is the requested name");
}
