// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the persistent novelty-baseline index (`MVBIDX01`).
//!
//! Hosted in a sibling file (pulled in via `#[path]`) so the owning module
//! stays under the 500-line cap. Coverage: build → load roundtrip, lookup
//! parity against the direct shard scan (`GraduationBaseline::load` and the
//! raw per-constant reconstruction path), first-name-wins hash semantics,
//! end-to-end `graduate()` parity between the two baseline backends, and
//! fail-closed loading of corrupted/truncated/foreign files.

use std::path::{Path, PathBuf};

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};

use super::super::intake::{graduate, GraduationBaseline, GraduationRequest};
use super::super::record::{
    expr_canonical_digest, EvidenceClass, NoveltyMatchKind, NoveltyVerdict, OnDuplicate,
};
use super::{
    build_baseline_index, digest_prefix, BaselineIndex, HEADER_LEN, MAGIC, TRAILER_LEN, VERSION,
};
use crate::error::MathverseError;
use crate::export::kernel_export::KernelShardBuilder;
use crate::shard::ShardReader;
use crate::shard_reconstruct::reconstruct_from_shard_with_level_lists;

fn bd() -> BinderInfo {
    BinderInfo::Default
}

/// `∀ (p : Prop), p → p` / `fun p h => h`.
fn imp_self() -> (Expr, Expr) {
    (
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(bd(), Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

/// `∀ (p q : Prop), p → q → p` / `fun p q hp hq => hp`.
fn const_left() -> (Expr, Expr) {
    (
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(
                bd(),
                Expr::prop(),
                Expr::pi(
                    bd(),
                    Expr::bvar(1),
                    Expr::pi(bd(), Expr::bvar(1), Expr::bvar(3)),
                ),
            ),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(
                bd(),
                Expr::prop(),
                Expr::lam(
                    bd(),
                    Expr::bvar(1),
                    Expr::lam(bd(), Expr::bvar(1), Expr::bvar(1)),
                ),
            ),
        ),
    )
}

/// `∀ (p q : Prop), p → q → q` / `fun p q hp hq => hq` — NOT in any
/// fixture shard; the genuinely-new candidate.
fn const_right() -> (Expr, Expr) {
    (
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(
                bd(),
                Expr::prop(),
                Expr::pi(
                    bd(),
                    Expr::bvar(1),
                    Expr::pi(bd(), Expr::bvar(1), Expr::bvar(2)),
                ),
            ),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(
                bd(),
                Expr::prop(),
                Expr::lam(
                    bd(),
                    Expr::bvar(1),
                    Expr::lam(bd(), Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        ),
    )
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// Write two fixture shards into `dir`:
/// * `a.mathverse` — `BaseIdx.imp_self` and `BaseIdx.imp_self_twin`
///   (identical statements, distinct names; first-wins check), and
/// * `b.mathverse` — `BaseIdx.const_left`.
fn write_fixture_shards(dir: &Path) {
    let (is_ty, is_val) = imp_self();
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(
            &theorem("BaseIdx.imp_self", is_ty.clone(), is_val.clone()),
            &[],
        )
        .expect("export imp_self");
    builder
        .add_declaration(&theorem("BaseIdx.imp_self_twin", is_ty, is_val), &[])
        .expect("export imp_self_twin");
    builder
        .write_to_file(dir.join("a.mathverse"))
        .expect("write shard a");

    let (cl_ty, cl_val) = const_left();
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&theorem("BaseIdx.const_left", cl_ty, cl_val), &[])
        .expect("export const_left");
    builder
        .write_to_file(dir.join("b.mathverse"))
        .expect("write shard b");
}

fn build_fixture_index(dir: &Path) -> (PathBuf, super::BaselineIndexStats) {
    let out = dir.join("fixture.mvix");
    let stats = build_baseline_index(dir, &out).expect("index build should succeed");
    (out, stats)
}

fn request(release: &str) -> GraduationRequest {
    GraduationRequest {
        project_name: "baseline-index-test".to_string(),
        manifest_kind: "clean-math-project-v1".to_string(),
        manifest_digest: "blake3:test".to_string(),
        certificate_schema: None,
        certificate_cross_checks: Vec::new(),
        mathverse_release: release.to_string(),
        on_duplicate: OnDuplicate::Reject,
        attempt_id: None,
        replay_archive_sha256: None,
        engine: None,
        seed: None,
        evidence_class: EvidenceClass::AgentAttested,
        residual_risk: "none-known".to_string(),
        clean_commit: None,
        shard_filename: None,
        decided_at_epoch_s: None,
        env_provenance: None,
        score_identity: false,
        score_defeq: false,
    }
}

#[test]
fn test_index_build_roundtrip_counts_and_digest_parity() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shards(tmp.path());
    let (out, stats) = build_fixture_index(tmp.path());

    assert_eq!(stats.shards, 2);
    assert_eq!(stats.constants, 3);
    assert_eq!(stats.names, 3);
    // imp_self and imp_self_twin share a statement hash.
    assert_eq!(stats.hashes, 2);
    // None of the fixture types use a commutative operator, so each distinct statement
    // also yields one distinct semantic (rewrite-canonical) digest — same dedup as hashes.
    assert_eq!(stats.semantic_hashes, 2);
    assert_eq!(stats.skipped_hashes, 0);

    let index = BaselineIndex::load(&out).expect("load index");
    assert_eq!(index.name_count(), 3);
    assert_eq!(index.hash_count(), 2);
    assert_eq!(index.semantic_count(), 2);

    // The corpus pin must be byte-identical to the direct scan's digest.
    let scanned = GraduationBaseline::load(tmp.path()).expect("direct scan");
    assert_eq!(index.corpus_digest(), scanned.digest());
}

#[test]
fn test_index_lookups_match_direct_shard_scan() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shards(tmp.path());
    let (out, _) = build_fixture_index(tmp.path());
    let index = BaselineIndex::load(&out).expect("load index");

    // Independent scan: per-constant reconstruction (the exact path
    // `GraduationBaseline::load` uses) over every constant of every shard.
    for shard in ["a.mathverse", "b.mathverse"] {
        let bytes = std::fs::read(tmp.path().join(shard)).expect("read shard");
        let reader = ShardReader::from_bytes(&bytes).expect("parse shard");
        for header in &reader.constants {
            let name = &reader.strings[header.name_idx as usize];
            assert!(index.contains_name(name), "name `{name}` must be indexed");
            let type_ = reconstruct_from_shard_with_level_lists(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                &reader.level_lists,
                header.type_idx,
            )
            .expect("reconstruct type");
            let digest = expr_canonical_digest(&type_).expect("hash type");
            let matched = index
                .lookup_statement_hash(&digest)
                .expect("statement hash must be indexed");
            assert!(
                index.contains_name(matched),
                "hash must map to an indexed name"
            );
        }
    }

    // First-name-wins: the shared imp_self statement maps to the constant
    // that appears first in corpus order.
    let (is_ty, _) = imp_self();
    let digest = expr_canonical_digest(&is_ty).expect("hash env-side type");
    assert_eq!(
        index.lookup_statement_hash(&digest),
        Some("BaseIdx.imp_self"),
        "env-side digest must hit the first baseline name carrying it"
    );

    // Negatives.
    assert!(!index.contains_name("BaseIdx.absent"));
    let (cl_ty, _) = const_left();
    let unrelated = Expr::pi(bd(), Expr::prop(), cl_ty);
    let miss = expr_canonical_digest(&unrelated).expect("hash unrelated");
    assert_eq!(index.lookup_statement_hash(&miss), None);
    assert_eq!(index.lookup_statement_hash("not-a-digest"), None);
    assert!(digest_prefix("blake3:zz").is_none());
}

#[test]
fn test_graduate_with_index_matches_load_backend() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_dir = tmp.path().join("shards");
    std::fs::create_dir_all(&shard_dir).expect("shard dir");
    write_fixture_shards(&shard_dir);
    let (out, _) = build_fixture_index(&shard_dir);

    // Candidate env: a name-duplicate of the baseline, a statement-duplicate
    // of shard a under a fresh name, a statement-duplicate of shard b under
    // a fresh name (env-built type vs shard-roundtripped type — the
    // cross-construction hash-match case), and a genuinely new theorem.
    let (is_ty, is_val) = imp_self();
    let (cl_ty, cl_val) = const_left();
    let (cr_ty, cr_val) = const_right();
    let mut env = Environment::with_prelude();
    env.add_decl(theorem("BaseIdx.imp_self", is_ty.clone(), is_val.clone()))
        .expect("imp_self checks");
    env.add_decl(theorem("Fresh.same_statement", is_ty, is_val))
        .expect("same_statement checks");
    env.add_decl(theorem("Fresh.const_left_renamed", cl_ty, cl_val))
        .expect("const_left_renamed checks");
    env.add_decl(theorem("Fresh.const_right", cr_ty, cr_val))
        .expect("const_right checks");
    let candidates = [
        Name::from_string("BaseIdx.imp_self"),
        Name::from_string("Fresh.same_statement"),
        Name::from_string("Fresh.const_left_renamed"),
        Name::from_string("Fresh.const_right"),
    ];

    let run = |baseline: &GraduationBaseline, out_dir: &Path| {
        graduate(&env, &candidates, &request("fixture"), baseline, out_dir).expect("graduate run")
    };
    let from_load = run(
        &GraduationBaseline::load(&shard_dir).expect("load baseline"),
        &tmp.path().join("out-load"),
    );
    let from_index = run(
        &GraduationBaseline::from_index(&out).expect("index baseline"),
        &tmp.path().join("out-index"),
    );

    assert_eq!(
        from_load.corpus_pin.manifest_digest,
        from_index.corpus_pin.manifest_digest
    );
    for (a, b) in from_load.theorems.iter().zip(from_index.theorems.iter()) {
        assert_eq!(a.name, b.name);
        assert_eq!(
            a.novelty.verdict, b.novelty.verdict,
            "verdict for {}",
            a.name
        );
        assert_eq!(
            a.novelty.matched_name, b.novelty.matched_name,
            "match for {}",
            a.name
        );
        assert_eq!(
            a.novelty.match_kind, b.novelty.match_kind,
            "kind for {}",
            a.name
        );
        assert_eq!(a.accepted, b.accepted, "accepted for {}", a.name);
    }
    let by_name = |r: &super::super::record::GraduationRecord, n: &str| {
        r.theorems
            .iter()
            .find(|t| t.name == n)
            .cloned()
            .expect("candidate present")
    };
    let dup = by_name(&from_index, "BaseIdx.imp_self");
    assert_eq!(dup.novelty.verdict, NoveltyVerdict::Duplicate);
    assert_eq!(dup.novelty.match_kind, Some(NoveltyMatchKind::Name));
    let stmt = by_name(&from_index, "Fresh.same_statement");
    assert_eq!(stmt.novelty.verdict, NoveltyVerdict::Duplicate);
    assert_eq!(
        stmt.novelty.match_kind,
        Some(NoveltyMatchKind::StatementHash)
    );
    assert_eq!(
        stmt.novelty.matched_name.as_deref(),
        Some("BaseIdx.imp_self")
    );
    let cross = by_name(&from_index, "Fresh.const_left_renamed");
    assert_eq!(cross.novelty.verdict, NoveltyVerdict::Duplicate);
    assert_eq!(
        cross.novelty.match_kind,
        Some(NoveltyMatchKind::StatementHash)
    );
    assert_eq!(
        cross.novelty.matched_name.as_deref(),
        Some("BaseIdx.const_left")
    );
    let fresh = by_name(&from_index, "Fresh.const_right");
    assert_eq!(fresh.novelty.verdict, NoveltyVerdict::New);
    assert!(fresh.accepted, "novel theorem must graduate");
}

#[test]
fn test_index_load_fails_closed_on_corruption() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shards(tmp.path());
    let (out, _) = build_fixture_index(tmp.path());
    let pristine = std::fs::read(&out).expect("read index");

    let expect_corrupt = |bytes: &[u8], label: &str| {
        let path = tmp.path().join(format!("{label}.mvix"));
        std::fs::write(&path, bytes).expect("write corrupted");
        match BaselineIndex::load(&path) {
            Err(MathverseError::BaselineIndexCorrupt { .. }) => {}
            other => panic!("{label}: expected BaselineIndexCorrupt, got {other:?}"),
        }
    };

    // (a) single bit flip in the body → self-digest mismatch.
    let mut flipped = pristine.clone();
    let mid = flipped.len() / 2;
    flipped[mid] ^= 0x01;
    expect_corrupt(&flipped, "bitflip");

    // (b) truncation.
    expect_corrupt(&pristine[..pristine.len() - 1], "truncated");
    expect_corrupt(&pristine[..10], "tiny");

    // (c) foreign magic.
    let mut foreign = pristine.clone();
    foreign[0..8].copy_from_slice(b"NOTMVIDX");
    expect_corrupt(&foreign, "magic");

    // (d) future version with a *valid* self-digest (exercises the version
    // gate itself, not the digest gate). v1 and v2 are accepted, so 3 is the
    // first rejected version.
    let mut versioned = pristine.clone();
    versioned[8..12].copy_from_slice(&3u32.to_le_bytes());
    let body_len = versioned.len() - TRAILER_LEN;
    let digest = blake3::hash(&versioned[..body_len]);
    versioned[body_len..].copy_from_slice(digest.as_bytes());
    expect_corrupt(&versioned, "version");

    // (e) out-of-range hash-record name_idx with a valid self-digest.
    let mut bad_idx = pristine.clone();
    let body_len = bad_idx.len() - TRAILER_LEN;
    let rec_name_idx_at = body_len - 4; // u32 of the last 20-byte hash record
    bad_idx[rec_name_idx_at..body_len].copy_from_slice(&u32::MAX.to_le_bytes());
    let digest = blake3::hash(&bad_idx[..body_len]);
    bad_idx[body_len..].copy_from_slice(digest.as_bytes());
    expect_corrupt(&bad_idx, "name-idx");

    // Pristine still loads after all that.
    BaselineIndex::load(&out).expect("pristine index must still load");
}

#[test]
fn test_index_build_empty_dir_yields_empty_index() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_dir = tmp.path().join("empty");
    std::fs::create_dir_all(&shard_dir).expect("mkdir");
    let out = tmp.path().join("empty.mvix");
    let stats = build_baseline_index(&shard_dir, &out).expect("build empty index");
    assert_eq!(stats.shards, 0);
    assert_eq!(stats.names, 0);
    let index = BaselineIndex::load(&out).expect("load empty index");
    assert!(!index.contains_name("anything"));
    assert_eq!(index.lookup_statement_hash("blake3:00"), None);
    assert_eq!(index.lookup_semantic("blake3:00"), None);
    assert_eq!(index.semantic_count(), 0);
    // Empty corpus digest equals blake3 of zero bytes — same as `load`.
    let scanned = GraduationBaseline::load(&shard_dir).expect("scan empty");
    assert_eq!(index.corpus_digest(), scanned.digest());
}

/// `op a b` as a curried application spine (env-free: no type-checking required —
/// the shard builder serializes the term, it does not check it).
fn bin(op: &str, a: &str, b: &str) -> Expr {
    Expr::app(
        Expr::app(Expr::const_str(op), Expr::const_str(a)),
        Expr::const_str(b),
    )
}

/// Write one shard with `Comm.and_pq : And P Q` (proof value is a placeholder
/// constant — the index never re-checks proofs, it indexes types).
fn write_commutative_shard(dir: &Path) {
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(
            &theorem(
                "Comm.and_pq",
                bin("And", "P", "Q"),
                Expr::const_str("Comm.h"),
            ),
            &[],
        )
        .expect("export and_pq");
    builder
        .write_to_file(dir.join("comm.mathverse"))
        .expect("write comm shard");
}

#[test]
fn test_semantic_table_collapses_commutative_reorder() {
    // The point of the semantic table: catch "same object, different form" that the
    // structural statement-hash misses. `And P Q` and `And Q P` are structurally
    // distinct (different hashes) but identical up to ∧-commutativity.
    let tmp = tempfile::tempdir().expect("tempdir");
    write_commutative_shard(tmp.path());
    let (out, stats) = build_fixture_index(tmp.path());
    assert_eq!(stats.names, 1);
    assert_eq!(stats.hashes, 1);
    assert_eq!(stats.semantic_hashes, 1);
    let index = BaselineIndex::load(&out).expect("load index");

    let reordered = bin("And", "Q", "P");
    let struct_hash = expr_canonical_digest(&reordered).expect("hash reordered");
    let sem_digest = clean_cake::identity::structural_rewrite_digest(&reordered);

    // The structural statement-hash table MISSES the reorder (the whole motivation) …
    assert_eq!(index.lookup_statement_hash(&struct_hash), None);
    // … but the SEMANTIC table matches it to the baseline's alternate form.
    assert_eq!(index.lookup_semantic(&sem_digest), Some("Comm.and_pq"));

    // The original form's own semantic digest also hits (roundtrip), and an
    // unrelated statement misses — no spurious semantic collapse.
    let orig_sem = clean_cake::identity::structural_rewrite_digest(&bin("And", "P", "Q"));
    assert_eq!(index.lookup_semantic(&orig_sem), Some("Comm.and_pq"));
    let unrelated_sem = clean_cake::identity::structural_rewrite_digest(&bin("And", "X", "Y"));
    assert_eq!(index.lookup_semantic(&unrelated_sem), None);
}

#[test]
fn test_v1_index_without_semantic_table_still_loads() {
    // Backward compatibility: a v1 index (no semantic table, `reserved = 0` where v2
    // keeps `sem_count`) must still load and answer name + statement-hash lookups, with
    // every semantic lookup simply missing.
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shards(tmp.path());
    let (out, _) = build_fixture_index(tmp.path());
    let v2 = std::fs::read(&out).expect("read v2 index");
    let sem_bytes = BaselineIndex::load(&out).expect("load v2").semantic_count() * 20;
    assert!(
        sem_bytes > 0,
        "fixture must have a non-empty semantic table"
    );

    // Synthesize the v1 layout from v2: drop the trailing semantic table, relabel the
    // version to 1, zero the (formerly `reserved`) field, recompute the self-digest.
    let body_len = v2.len() - TRAILER_LEN;
    let mut v1_body = v2[..body_len - sem_bytes].to_vec();
    v1_body[8..12].copy_from_slice(&1u32.to_le_bytes());
    v1_body[12..16].copy_from_slice(&0u32.to_le_bytes());
    let mut v1 = v1_body.clone();
    v1.extend_from_slice(blake3::hash(&v1_body).as_bytes());
    let v1_path = tmp.path().join("v1.mvix");
    std::fs::write(&v1_path, &v1).expect("write v1");

    let v1_index = BaselineIndex::load(&v1_path).expect("v1 index must load");
    assert_eq!(v1_index.semantic_count(), 0, "v1 has no semantic table");
    assert!(v1_index.contains_name("BaseIdx.imp_self"));
    let (is_ty, _) = imp_self();
    let digest = expr_canonical_digest(&is_ty).expect("hash imp_self");
    assert_eq!(
        v1_index.lookup_statement_hash(&digest),
        Some("BaseIdx.imp_self")
    );
    // No false positives from a v1 index's (absent) semantic table.
    assert_eq!(v1_index.lookup_semantic(&digest), None);
}

#[test]
fn test_graduate_scored_keeps_index_and_load_backends_in_parity() {
    // With `--score` the semantic probe is active. The two baseline backends must still
    // agree verdict-for-verdict (the probe runs in both; here it confirms no divergence).
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_dir = tmp.path().join("shards");
    std::fs::create_dir_all(&shard_dir).expect("shard dir");
    write_fixture_shards(&shard_dir);
    let (out, _) = build_fixture_index(&shard_dir);

    let (is_ty, is_val) = imp_self();
    let (cr_ty, cr_val) = const_right();
    let mut env = Environment::with_prelude();
    env.add_decl(theorem("Fresh.same_statement", is_ty, is_val))
        .expect("same_statement checks");
    env.add_decl(theorem("Fresh.const_right", cr_ty, cr_val))
        .expect("const_right checks");
    let candidates = [
        Name::from_string("Fresh.same_statement"),
        Name::from_string("Fresh.const_right"),
    ];
    let mut req = request("fixture");
    req.score_identity = true;

    let run = |baseline: &GraduationBaseline, out_dir: &Path| {
        graduate(&env, &candidates, &req, baseline, out_dir).expect("graduate run")
    };
    let from_load = run(
        &GraduationBaseline::load(&shard_dir).expect("load baseline"),
        &tmp.path().join("out-load"),
    );
    let from_index = run(
        &GraduationBaseline::from_index(&out).expect("index baseline"),
        &tmp.path().join("out-index"),
    );
    for (a, b) in from_load.theorems.iter().zip(from_index.theorems.iter()) {
        assert_eq!(a.name, b.name);
        assert_eq!(a.novelty.verdict, b.novelty.verdict, "verdict {}", a.name);
        assert_eq!(
            a.novelty.match_kind, b.novelty.match_kind,
            "kind {}",
            a.name
        );
        assert_eq!(a.accepted, b.accepted, "accepted {}", a.name);
    }
    // Under --score, accepted candidates carry the bound semantic identity (incl. the
    // env-free corpus key) — the graduation-record binding item 4 calls for.
    let fresh = from_index
        .theorems
        .iter()
        .find(|t| t.name == "Fresh.const_right")
        .expect("const_right present");
    assert!(fresh.accepted);
    let sid = fresh
        .semantic_identity
        .as_ref()
        .expect("scored run binds semantic identity");
    assert!(sid.structural_rewrite_digest.starts_with("blake3:"));
}

// ---------------------------------------------------------------------------
// Semantic-match wiring: end-to-end through both backends, determinism, and the
// fail-closed loader hardening (audit follow-ups, 2026-06-15).
// ---------------------------------------------------------------------------

/// `And a b` (And : Prop → Prop → Prop in the prelude; no universe params).
fn and(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_str("And"), a), b)
}

/// `∀ (p q : Prop), And o1 o2 → And o1 o2` with proof `fun p q h => h`, where
/// `(o1,o2) = (p,q)` if `!swap` else `(q,p)`. The two `swap` variants are distinct
/// statements (different statement-hash) that are identical up to ∧-commutativity, so they
/// share one Tier-1.5 `structural_rewrite_digest` — a genuine semantic-only match.
fn and_imp_self(swap: bool) -> (Expr, Expr) {
    // Under [p, q] (depth 2): p = bvar1, q = bvar0. The hypothesis adds a binder, so the
    // codomain (depth 3) shifts by one: p = bvar2, q = bvar1.
    let (d1, d2) = if swap {
        (Expr::bvar(0), Expr::bvar(1))
    } else {
        (Expr::bvar(1), Expr::bvar(0))
    };
    let (c1, c2) = if swap {
        (Expr::bvar(1), Expr::bvar(2))
    } else {
        (Expr::bvar(2), Expr::bvar(1))
    };
    let ty = Expr::pi(
        bd(),
        Expr::prop(),
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(bd(), and(d1.clone(), d2.clone()), and(c1, c2)),
        ),
    );
    let val = Expr::lam(
        bd(),
        Expr::prop(),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(bd(), and(d1, d2), Expr::bvar(0)),
        ),
    );
    (ty, val)
}

/// Shard carrying `Comm.base : ∀ p q, And q p → And q p` (the `swap` form).
fn write_and_baseline_shard(dir: &Path) {
    let (ty, val) = and_imp_self(true);
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&theorem("Comm.base", ty, val), &[])
        .expect("export Comm.base");
    builder
        .write_to_file(dir.join("comm_base.mathverse"))
        .expect("write comm baseline shard");
}

#[test]
fn test_semantic_only_match_is_nonblocking_and_parity_across_backends() {
    // A candidate that is a ∧-commutative reorder of a baseline statement: its name and
    // statement-hash both MISS, only the semantic digest hits. Under --score this must be
    // recorded (New + SemanticDigest + matched_name) but NEVER block graduation — and both
    // baseline backends (direct scan vs MVBIDX01 index) must agree exactly.
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_dir = tmp.path().join("shards");
    std::fs::create_dir_all(&shard_dir).expect("shard dir");
    write_and_baseline_shard(&shard_dir);
    let (out, _) = build_fixture_index(&shard_dir);

    let (cand_ty, cand_val) = and_imp_self(false); // And p q — the reorder
    let mut env = Environment::with_prelude();
    env.add_decl(theorem("Comm.cand", cand_ty, cand_val))
        .expect("candidate type-checks");
    let candidates = [Name::from_string("Comm.cand")];
    let mut req = request("fixture");
    req.score_identity = true;

    let run = |baseline: &GraduationBaseline, out_dir: &Path| {
        graduate(&env, &candidates, &req, baseline, out_dir).expect("graduate run")
    };
    let from_load = run(
        &GraduationBaseline::load(&shard_dir).expect("load baseline"),
        &tmp.path().join("out-load"),
    );
    let from_index = run(
        &GraduationBaseline::from_index(&out).expect("index baseline"),
        &tmp.path().join("out-index"),
    );

    for rec in [&from_load, &from_index] {
        let cand = rec
            .theorems
            .iter()
            .find(|t| t.name == "Comm.cand")
            .expect("candidate present");
        // Non-blocking: the genuinely-novel reorder graduates, NOT suppressed as a duplicate.
        assert!(
            cand.accepted,
            "semantic-only match must not block graduation"
        );
        assert_eq!(
            cand.novelty.verdict,
            NoveltyVerdict::New,
            "semantic match stays New (novel by exact identity)"
        );
        assert_eq!(
            cand.novelty.match_kind,
            Some(NoveltyMatchKind::SemanticDigest),
            "the alternate form is recorded"
        );
        assert_eq!(
            cand.novelty.matched_name.as_deref(),
            Some("Comm.base"),
            "the matched corpus alternate is named"
        );
        assert_eq!(
            cand.novelty.method,
            "name+statement-hash+tier1.5-rewrite-canonical"
        );
    }
    // Backend parity (parity-2 / parity-3): identical verdict, kind, match, accepted.
    let a = &from_load.theorems[0];
    let b = &from_index.theorems[0];
    assert_eq!(a.novelty.verdict, b.novelty.verdict);
    assert_eq!(a.novelty.match_kind, b.novelty.match_kind);
    assert_eq!(a.novelty.matched_name, b.novelty.matched_name);
    assert_eq!(a.accepted, b.accepted);
}

#[test]
fn test_semantic_probe_is_inert_without_score() {
    // determinism-1: the SAME candidate + a would-match baseline, run WITHOUT --score, must
    // be evaluated purely by exact identity (New, no match_kind) and graduate — proving the
    // semantic probe is fully inert by default, so default-run records stay byte-identical.
    let tmp = tempfile::tempdir().expect("tempdir");
    let shard_dir = tmp.path().join("shards");
    std::fs::create_dir_all(&shard_dir).expect("shard dir");
    write_and_baseline_shard(&shard_dir);

    let (cand_ty, cand_val) = and_imp_self(false);
    let mut env = Environment::with_prelude();
    env.add_decl(theorem("Comm.cand", cand_ty, cand_val))
        .expect("candidate type-checks");
    let candidates = [Name::from_string("Comm.cand")];
    let req = request("fixture"); // score_identity = false

    let rec = graduate(
        &env,
        &candidates,
        &req,
        &GraduationBaseline::load(&shard_dir).expect("load baseline"),
        &tmp.path().join("out"),
    )
    .expect("graduate run");
    let cand = &rec.theorems[0];
    assert!(cand.accepted);
    assert_eq!(cand.novelty.verdict, NoveltyVerdict::New);
    assert_eq!(
        cand.novelty.match_kind, None,
        "no semantic probe without --score"
    );
    assert_eq!(cand.novelty.matched_name, None);
    assert_eq!(cand.novelty.method, "name+statement-hash");
    assert!(
        cand.semantic_identity.is_none(),
        "no semantic identity bound without --score"
    );
}

#[test]
fn test_v1_index_with_nonzero_sem_count_fails_closed() {
    // version-1 hardening: a v1-versioned file that nonetheless declares a semantic table
    // (nonzero [12..16)) is malformed and must be rejected even with a valid self-digest.
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shards(tmp.path());
    let (out, _) = build_fixture_index(tmp.path());
    let mut bytes = std::fs::read(&out).expect("read v2 index");
    assert!(
        BaselineIndex::load(&out)
            .expect("v2 loads")
            .semantic_count()
            > 0
    );

    // Relabel version 2 -> 1 but KEEP the nonzero sem_count + sem table; recompute trailer.
    bytes[8..12].copy_from_slice(&1u32.to_le_bytes());
    let body_len = bytes.len() - TRAILER_LEN;
    let digest = blake3::hash(&bytes[..body_len]);
    bytes[body_len..].copy_from_slice(digest.as_bytes());
    let path = tmp.path().join("v1_stray_sem.mvix");
    std::fs::write(&path, &bytes).expect("write");
    match BaselineIndex::load(&path) {
        Err(MathverseError::BaselineIndexCorrupt { .. }) => {}
        other => panic!("expected BaselineIndexCorrupt for v1+sem_count, got {other:?}"),
    }
}

#[test]
fn test_crafted_huge_hash_count_fails_closed_not_panics() {
    // overflow-1: a crafted header with hash_count ≈ usize::MAX/HASH_RECORD_LEN must yield
    // BaselineIndexCorrupt via checked arithmetic, never an integer-overflow panic/abort.
    let mut body = Vec::new();
    body.extend_from_slice(MAGIC);
    body.extend_from_slice(&VERSION.to_le_bytes());
    body.extend_from_slice(&0u32.to_le_bytes()); // sem_count
    body.extend_from_slice(&0u64.to_le_bytes()); // name_count
    body.extend_from_slice(&((usize::MAX / 16) as u64).to_le_bytes()); // hash_count (huge)
    body.extend_from_slice(&0u64.to_le_bytes()); // names_blob_len
    body.extend_from_slice(&[0u8; 32]); // corpus_digest
                                        // One name-offset entry (name_count+1 = 1) so the header region is well-formed.
    body.extend_from_slice(&0u32.to_le_bytes());
    assert_eq!(body.len(), HEADER_LEN + 4);
    let digest = blake3::hash(&body);
    body.extend_from_slice(digest.as_bytes());
    let tmp = tempfile::tempdir().expect("tempdir");
    let path = tmp.path().join("overflow.mvix");
    std::fs::write(&path, &body).expect("write");
    match BaselineIndex::load(&path) {
        Err(MathverseError::BaselineIndexCorrupt { .. }) => {}
        other => panic!("expected BaselineIndexCorrupt for overflow header, got {other:?}"),
    }
}
