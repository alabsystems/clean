// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exhaustive integration tests for the Mathverse pipeline end-to-end.
//!
//! Tests shard round-trips for all importers, release packaging,
//! cross-system search, trust boundary enforcement, and axiom profiles.
//! All tests use synthetic data -- no external file dependencies.

use clean_kernel::flat::{FlatExpr, FlatLevel};

use crate::library::MathverseLibrary;
use crate::release::{verify_release, ReleaseManifest};
use crate::search::{DomainQuery, MathverseSearch};
use crate::shard::{ShardReader, ShardWriter};
use crate::trust::policy::TrustPolicy;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a ShardWriter with standard type scaffold (level zero, sort expr).
/// Returns (writer, level_zero_idx, sort_expr_idx).
fn scaffold() -> (ShardWriter, u32, u32) {
    let mut w = ShardWriter::new();
    let l0 = w.add_level(FlatLevel::zero());
    let e0 = w.add_expr(FlatExpr::sort(l0));
    (w, l0, e0)
}

/// Add a named constant to a ShardWriter and return the name string index.
fn add_named_constant(
    w: &mut ShardWriter,
    name: &str,
    type_idx: u32,
    value_idx: u32,
    source: SourceSystem,
    confidence: ImportConfidence,
    domain: ContentDomain,
    profile: AxiomProfile,
) -> u32 {
    let ni = w.add_string(name);
    w.add_constant(MathverseConstantHeader {
        name_idx: ni,
        type_idx,
        value_idx,
        source_system: source as u8,
        import_confidence: confidence as u8,
        content_domain: domain as u8,
        decl_kind: 0,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    ni
}

/// Write a ShardWriter to bytes and read it back as a ShardReader.
fn round_trip(w: &ShardWriter) -> ShardReader {
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

// ===========================================================================
// Category 1: Shard round-trip tests per importer
// ===========================================================================

#[test]
fn test_shard_round_trip_metamath() {
    // Metamath theorems use SourceSystem::Metamath with various axiom profiles.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "ax-mp",
        e0,
        e0,
        SourceSystem::Metamath,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "ax-1",
        e0,
        NO_VALUE,
        SourceSystem::Metamath,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    add_named_constant(
        &mut w,
        "ax-2",
        e0,
        NO_VALUE,
        SourceSystem::Metamath,
        ImportConfidence::Axiomatized,
        ContentDomain::Logic,
        AxiomProfile::AXIOMATIZED,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 3);
    let (_, hdr) = reader.lookup_name("ax-mp").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Metamath as u8);
    assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);
    assert!(hdr.has_value());

    let (_, hdr) = reader.lookup_name("ax-1").unwrap();
    assert!(!hdr.has_value());
    assert!(hdr.is_trust_gated());

    assert!(reader.lookup_name("ax-2").is_some());
}

#[test]
fn test_shard_round_trip_hol() {
    // HOL Light / HOL4 embeddings carry HOL_EMBEDDING axiom bits.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "HOL.BOOL_CASES_AX",
        e0,
        e0,
        SourceSystem::HolLight,
        ImportConfidence::Translated,
        ContentDomain::Logic,
        AxiomProfile::HOL_EMBEDDING,
    );
    add_named_constant(
        &mut w,
        "HOL4.arithmeticTheory.ADD_COMM",
        e0,
        e0,
        SourceSystem::Hol4,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::HOL_EMBEDDING | AxiomProfile::CHOICE,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 2);
    let (_, hdr) = reader.lookup_name("HOL.BOOL_CASES_AX").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::HolLight as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::HOL_EMBEDDING));

    let (_, hdr) = reader
        .lookup_name("HOL4.arithmeticTheory.ADD_COMM")
        .unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Hol4 as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::CHOICE));
}

#[test]
fn test_shard_round_trip_mizar() {
    // Mizar uses Tarski-Grothendieck set theory with soft typing.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "CARD_1:def_1",
        e0,
        e0,
        SourceSystem::Mizar,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::MIZAR_TG,
    );
    add_named_constant(
        &mut w,
        "XBOOLE_0:def_3",
        e0,
        e0,
        SourceSystem::Mizar,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::MIZAR_SOFT_TYPE,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 2);
    let (_, hdr) = reader.lookup_name("CARD_1:def_1").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Mizar as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::MIZAR_TG));
}

#[test]
fn test_shard_round_trip_dtt_agda() {
    // Agda DTT import with cubical extension axiom.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "Agda.Builtin.Nat.zero",
        e0,
        e0,
        SourceSystem::Agda,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "Agda.Cubical.Glue",
        e0,
        NO_VALUE,
        SourceSystem::Agda,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AGDA_CUBICAL | AxiomProfile::AXIOMATIZED,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 2);
    let (_, hdr) = reader.lookup_name("Agda.Builtin.Nat.zero").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Agda as u8);
    assert!(hdr.has_value());

    let (_, hdr) = reader.lookup_name("Agda.Cubical.Glue").unwrap();
    assert!(hdr.axiom_profile.has(AxiomProfile::AGDA_CUBICAL));
    assert!(!hdr.has_value());
}

#[test]
fn test_shard_round_trip_dtt_idris() {
    // Idris TT2 import with quantitative type theory axiom.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "Idris2.Prelude.Nat.Z",
        e0,
        e0,
        SourceSystem::Idris2,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::IDRIS_QTT,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 1);
    let (_, hdr) = reader.lookup_name("Idris2.Prelude.Nat.Z").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Idris2 as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::IDRIS_QTT));
}

#[test]
fn test_shard_round_trip_nn_cert() {
    // NN verification certificates from gamma-crown.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "nn_cert.mnist_robust_eps0_3",
        e0,
        e0,
        SourceSystem::GammaCrown,
        ImportConfidence::Translated,
        ContentDomain::NnVerification,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );
    add_named_constant(
        &mut w,
        "nn_cert.cifar_property_1",
        e0,
        e0,
        SourceSystem::AlphaBetaCrown,
        ImportConfidence::Translated,
        ContentDomain::NnVerification,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 2);
    let (_, hdr) = reader.lookup_name("nn_cert.mnist_robust_eps0_3").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::GammaCrown as u8);
    assert_eq!(hdr.content_domain, ContentDomain::NnVerification as u8);
    assert!(hdr.is_trust_gated());
}

#[test]
fn test_shard_round_trip_decision_certs_drat() {
    // DRAT/LRAT SAT certificates.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "sat_cert.pigeonhole_6_5",
        e0,
        e0,
        SourceSystem::CaDiCaL,
        ImportConfidence::Translated,
        ContentDomain::Logic,
        AxiomProfile::SAT_CERT,
    );
    add_named_constant(
        &mut w,
        "smt_cert.queens_8",
        e0,
        e0,
        SourceSystem::Z3,
        ImportConfidence::Translated,
        ContentDomain::Logic,
        AxiomProfile::SMT_ORACLE,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 2);
    let (_, hdr) = reader.lookup_name("sat_cert.pigeonhole_6_5").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::CaDiCaL as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::SAT_CERT));
}

#[test]
fn test_shard_round_trip_program_verify() {
    // Program verification VCs from Boogie/WhyML.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "boogie.binary_search_correct",
        e0,
        e0,
        SourceSystem::Boogie,
        ImportConfidence::Translated,
        ContentDomain::Software,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "why3.insertion_sort_stable",
        e0,
        e0,
        SourceSystem::Why3,
        ImportConfidence::Translated,
        ContentDomain::Software,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "dafny.stack_spec",
        e0,
        NO_VALUE,
        SourceSystem::Dafny,
        ImportConfidence::Axiomatized,
        ContentDomain::Software,
        AxiomProfile::AXIOMATIZED,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 3);
    let (_, hdr) = reader.lookup_name("boogie.binary_search_correct").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Boogie as u8);
    assert_eq!(hdr.content_domain, ContentDomain::Software as u8);
    assert!(hdr.has_value());

    let (_, hdr) = reader.lookup_name("dafny.stack_spec").unwrap();
    assert!(!hdr.has_value());
}

#[test]
fn test_shard_round_trip_lean4_shard() {
    // Lean4 native shard with kernel-verified constants.
    let (mut w, l0, e0) = scaffold();
    let l1 = w.add_level(FlatLevel::succ(l0));
    let e1 = w.add_expr(FlatExpr::sort(l1));
    let e_pi = w.add_expr(FlatExpr::pi(0, e0, e1));

    add_named_constant(
        &mut w,
        "Nat.add",
        e_pi,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "Nat.add_comm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "Classical.choice",
        e0,
        NO_VALUE,
        SourceSystem::Lean4,
        ImportConfidence::Axiomatized,
        ContentDomain::Logic,
        AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 3);
    assert_eq!(reader.header.level_count, 2);
    assert_eq!(reader.header.expr_count, 3); // e0, e1, e_pi (deduplicated)

    let (_, hdr) = reader.lookup_name("Nat.add").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Lean4 as u8);
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );

    let (_, hdr) = reader.lookup_name("Classical.choice").unwrap();
    assert!(!hdr.has_value());
    assert!(hdr.axiom_profile.has(AxiomProfile::CHOICE));
    assert!(hdr.is_trust_gated());
}

#[test]
fn test_shard_round_trip_coq() {
    // Coq imports with various extension axiom profiles.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "Coq.Init.Nat.add",
        e0,
        e0,
        SourceSystem::Coq,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "Coq.Logic.ClassicalChoice.choice",
        e0,
        NO_VALUE,
        SourceSystem::Coq,
        ImportConfidence::Axiomatized,
        ContentDomain::Logic,
        AxiomProfile::CHOICE | AxiomProfile::AXIOMATIZED,
    );
    add_named_constant(
        &mut w,
        "Coq.Init.SProp.sBox",
        e0,
        e0,
        SourceSystem::Coq,
        ImportConfidence::Translated,
        ContentDomain::Logic,
        AxiomProfile::COQ_SPROP,
    );

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 3);
    let (_, hdr) = reader.lookup_name("Coq.Init.SProp.sBox").unwrap();
    assert!(hdr.axiom_profile.has(AxiomProfile::COQ_SPROP));
}

#[test]
fn test_shard_round_trip_fstar() {
    // F* import.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "FStar.UInt32.add",
        e0,
        e0,
        SourceSystem::FStar,
        ImportConfidence::Translated,
        ContentDomain::Software,
        AxiomProfile::NONE,
    );

    let reader = round_trip(&w);
    assert_eq!(reader.header.constant_count, 1);
    let (_, hdr) = reader.lookup_name("FStar.UInt32.add").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::FStar as u8);
}

#[test]
fn test_shard_round_trip_atp_certs() {
    // ATP (automated theorem prover) certificates.
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "vampire_proof.GRP001-1",
        e0,
        e0,
        SourceSystem::Vampire,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::ATP_CERT,
    );

    let reader = round_trip(&w);
    let (_, hdr) = reader.lookup_name("vampire_proof.GRP001-1").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Vampire as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::ATP_CERT));
}

// ===========================================================================
// Category 2: Release round-trip tests
// ===========================================================================

#[test]
fn test_release_manifest_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("shards");
    std::fs::create_dir_all(&shard_dir).unwrap();

    // Write two shards into the shard directory.
    let (mut w1, _l0, e0) = scaffold();
    add_named_constant(
        &mut w1,
        "Nat.add",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    w1.write_to_file(shard_dir.join("lean4.mathverse")).unwrap();

    let (mut w2, _l0, e0) = scaffold();
    add_named_constant(
        &mut w2,
        "ax-mp",
        e0,
        e0,
        SourceSystem::Metamath,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    w2.write_to_file(shard_dir.join("metamath.mathverse"))
        .unwrap();

    // Build manifest.
    let manifest = ReleaseManifest::from_directory(&shard_dir, "0.1.0-test").unwrap();
    assert_eq!(manifest.total_shards, 2);
    assert_eq!(manifest.release_version, "0.1.0-test");
    assert!(manifest.total_bytes > 0);

    // Write and re-read manifest.
    let manifest_path = shard_dir.join("mathverse-manifest.json");
    manifest.write_to_file(&manifest_path).unwrap();

    let reloaded = ReleaseManifest::from_file(&manifest_path).unwrap();
    assert_eq!(reloaded.total_shards, manifest.total_shards);
    assert_eq!(reloaded.total_bytes, manifest.total_bytes);

    // All shards should have non-empty blake3 hashes.
    for entry in &reloaded.shards {
        assert!(!entry.blake3.is_empty());
        assert!(entry.size > 0);
        assert!(entry.path.ends_with(".mathverse"));
    }
}

#[test]
fn test_release_verify_passes() {
    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("release");
    std::fs::create_dir_all(&shard_dir).unwrap();

    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "Theorem.one",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    w.write_to_file(shard_dir.join("shard1.mathverse")).unwrap();

    // Build and write manifest.
    let manifest = ReleaseManifest::from_directory(&shard_dir, "0.2.0").unwrap();
    manifest
        .write_to_file(&shard_dir.join("mathverse-manifest.json"))
        .unwrap();

    // Verify should pass.
    let result = verify_release(&shard_dir).unwrap();
    assert!(result.is_ok(), "all checksums should pass");
    assert_eq!(result.checked, 1);
    assert_eq!(result.passed, 1);
    assert!(result.failures.is_empty());
    assert!(result.missing.is_empty());
}

#[test]
fn test_release_verify_detects_corruption() {
    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("corrupt_release");
    std::fs::create_dir_all(&shard_dir).unwrap();

    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "Theorem.corrupt",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_path = shard_dir.join("corrupted.mathverse");
    w.write_to_file(&shard_path).unwrap();

    // Build manifest with correct checksums.
    let manifest = ReleaseManifest::from_directory(&shard_dir, "0.3.0").unwrap();
    manifest
        .write_to_file(&shard_dir.join("mathverse-manifest.json"))
        .unwrap();

    // Corrupt the shard file by flipping a byte.
    let mut data = std::fs::read(&shard_path).unwrap();
    assert!(!data.is_empty());
    // Flip a byte in the middle of the file (after header, in the data section).
    let flip_pos = data.len() / 2;
    data[flip_pos] ^= 0xFF;
    std::fs::write(&shard_path, &data).unwrap();

    // Verify should detect the corruption.
    let result = verify_release(&shard_dir).unwrap();
    assert!(!result.is_ok(), "should detect corrupted shard");
    assert_eq!(result.failures.len(), 1);
    assert!(result.failures[0].path.contains("corrupted.mathverse"));
}

#[test]
fn test_release_verify_detects_missing_shard() {
    let dir = tempfile::tempdir().unwrap();
    let shard_dir = dir.path().join("missing_release");
    std::fs::create_dir_all(&shard_dir).unwrap();

    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "Theorem.present",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_path = shard_dir.join("present.mathverse");
    w.write_to_file(&shard_path).unwrap();

    // Build manifest.
    let manifest = ReleaseManifest::from_directory(&shard_dir, "0.4.0").unwrap();
    manifest
        .write_to_file(&shard_dir.join("mathverse-manifest.json"))
        .unwrap();

    // Delete the shard after manifest was created.
    std::fs::remove_file(&shard_path).unwrap();

    // Verify should detect the missing shard.
    let result = verify_release(&shard_dir).unwrap();
    assert!(!result.is_ok(), "should detect missing shard");
    assert_eq!(result.missing.len(), 1);
}

// ===========================================================================
// Category 3: Cross-system search integration tests
// ===========================================================================

#[test]
fn test_cross_system_search_metamath_and_hol() {
    // Build two shards: one Metamath, one HOL.
    let (mut w_mm, _l0, e0) = scaffold();
    add_named_constant(
        &mut w_mm,
        "mm.Nat.add_comm",
        e0,
        e0,
        SourceSystem::Metamath,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w_mm,
        "mm.Group.assoc",
        e0,
        e0,
        SourceSystem::Metamath,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_mm = round_trip(&w_mm);

    let (mut w_hol, _l0, e0) = scaffold();
    add_named_constant(
        &mut w_hol,
        "hol.NUM_ADD_SYM",
        e0,
        e0,
        SourceSystem::HolLight,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::HOL_EMBEDDING,
    );
    add_named_constant(
        &mut w_hol,
        "hol.REAL_COMPLETE",
        e0,
        e0,
        SourceSystem::HolLight,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::HOL_EMBEDDING | AxiomProfile::REAL_AXIOMS,
    );
    let shard_hol = round_trip(&w_hol);

    // Load both into a library.
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard_mm).unwrap();
    lib.load_shard(&shard_hol).unwrap();

    assert_eq!(lib.constant_count(), 4);

    // Name lookup across systems.
    assert!(lib.lookup_name("mm.Nat.add_comm").is_some());
    assert!(lib.lookup_name("hol.NUM_ADD_SYM").is_some());

    // Domain search should find both systems' theorems.
    let results = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("add".to_string()),
        )
        .unwrap();
    assert!(
        results.len() >= 2,
        "should find add-related theorems from both systems"
    );
    let sources: Vec<u8> = results.iter().map(|r| r.header.source_system).collect();
    assert!(
        sources.contains(&(SourceSystem::Metamath as u8)),
        "should include Metamath result"
    );
    assert!(
        sources.contains(&(SourceSystem::HolLight as u8)),
        "should include HOL Light result"
    );
}

#[test]
fn test_cross_system_search_three_systems() {
    // Lean4 + Coq + Agda shards.
    let (mut w_lean, _l0, e0) = scaffold();
    add_named_constant(
        &mut w_lean,
        "lean.Nat.zero",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_lean = round_trip(&w_lean);

    let (mut w_coq, _l0, e0) = scaffold();
    add_named_constant(
        &mut w_coq,
        "coq.Nat.O",
        e0,
        e0,
        SourceSystem::Coq,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_coq = round_trip(&w_coq);

    let (mut w_agda, _l0, e0) = scaffold();
    add_named_constant(
        &mut w_agda,
        "agda.Data.Nat.zero",
        e0,
        e0,
        SourceSystem::Agda,
        ImportConfidence::Translated,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard_agda = round_trip(&w_agda);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard_lean).unwrap();
    lib.load_shard(&shard_coq).unwrap();
    lib.load_shard(&shard_agda).unwrap();

    assert_eq!(lib.constant_count(), 3);

    // All three should be findable.
    assert!(lib.lookup_name("lean.Nat.zero").is_some());
    assert!(lib.lookup_name("coq.Nat.O").is_some());
    assert!(lib.lookup_name("agda.Data.Nat.zero").is_some());

    // Semantic search for "Nat" should find all three.
    let results = lib.search_semantic("Nat zero", 10).unwrap();
    assert!(
        !results.is_empty(),
        "semantic search should find Nat-related theorems"
    );
}

#[test]
fn test_cross_system_mixed_domains() {
    // Mix pure math, software, and NN verification across shards.
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "math.Group.assoc",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "sw.tcp_correct",
        e0,
        e0,
        SourceSystem::Boogie,
        ImportConfidence::Translated,
        ContentDomain::Software,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "nn.robustness_cert",
        e0,
        e0,
        SourceSystem::GammaCrown,
        ImportConfidence::Translated,
        ContentDomain::NnVerification,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );
    let shard = round_trip(&w);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    // Filter by domain.
    let math_results = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("Group".to_string()),
        )
        .unwrap();
    assert_eq!(math_results.len(), 1);

    let sw_results = lib
        .search_domain(
            ContentDomain::Software,
            &DomainQuery::SoftwareSpec("tcp".to_string()),
        )
        .unwrap();
    assert_eq!(sw_results.len(), 1);

    let nn_results = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::FreeText("robustness".to_string()),
        )
        .unwrap();
    assert_eq!(nn_results.len(), 1);
}

// ===========================================================================
// Category 4: Trust boundary tests
// ===========================================================================

#[test]
fn test_trust_default_hides_axiomatized() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "pure.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "axiom.thm",
        e0,
        NO_VALUE,
        SourceSystem::Lean4,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    add_named_constant(
        &mut w,
        "choice.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::CHOICE,
    );
    let shard = round_trip(&w);

    // Default policy: strict.
    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&shard).unwrap();

    assert!(
        lib.lookup_name("pure.thm").is_some(),
        "pure should be visible"
    );
    assert!(
        lib.lookup_name("axiom.thm").is_none(),
        "axiomatized should be hidden"
    );
    // CHOICE is not trust-gated, so visible even under strict policy.
    assert!(
        lib.lookup_name("choice.thm").is_some(),
        "CHOICE (non-gated) should be visible"
    );
}

#[test]
fn test_trust_permissive_shows_all() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "pure.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "axiom.thm",
        e0,
        NO_VALUE,
        SourceSystem::Lean4,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    add_named_constant(
        &mut w,
        "nn.cert",
        e0,
        e0,
        SourceSystem::GammaCrown,
        ImportConfidence::Translated,
        ContentDomain::NnVerification,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );
    let shard = round_trip(&w);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();

    assert!(lib.lookup_name("pure.thm").is_some());
    assert!(lib.lookup_name("axiom.thm").is_some());
    assert!(lib.lookup_name("nn.cert").is_some());
}

#[test]
fn test_trust_custom_allows_axiomatized_but_not_nn() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "axiom.thm",
        e0,
        NO_VALUE,
        SourceSystem::Isabelle,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    add_named_constant(
        &mut w,
        "nn.cert",
        e0,
        e0,
        SourceSystem::GammaCrown,
        ImportConfidence::Translated,
        ContentDomain::NnVerification,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );
    add_named_constant(
        &mut w,
        "pure.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard = round_trip(&w);

    // Custom policy: allow AXIOMATIZED but nothing else.
    let policy = TrustPolicy::with_allowed_bits(AxiomProfile::AXIOMATIZED);
    let mut lib = MathverseLibrary::new(policy);
    lib.load_shard(&shard).unwrap();

    assert!(lib.lookup_name("pure.thm").is_some(), "pure always visible");
    assert!(
        lib.lookup_name("axiom.thm").is_some(),
        "axiomatized should be visible with custom policy"
    );
    assert!(
        lib.lookup_name("nn.cert").is_none(),
        "NN cert should still be hidden"
    );
}

#[test]
fn test_trust_domain_search_respects_policy() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "visible.nat_add",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "hidden.nat_add",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    let shard = round_trip(&w);

    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&shard).unwrap();

    let results = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("nat_add".to_string()),
        )
        .unwrap();
    assert_eq!(results.len(), 1, "only visible constant should appear");
    assert_eq!(
        lib.get_name(results[0].constant_idx),
        Some("visible.nat_add")
    );
}

#[test]
fn test_trust_semantic_search_respects_policy() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "visible.comm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "hidden.comm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
    );
    let shard = round_trip(&w);

    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&shard).unwrap();

    let results = lib.search_semantic("comm", 10).unwrap();
    for r in &results {
        assert_ne!(
            lib.get_name(r.constant_idx),
            Some("hidden.comm"),
            "trust-gated constant should be filtered from semantic search"
        );
    }
}
