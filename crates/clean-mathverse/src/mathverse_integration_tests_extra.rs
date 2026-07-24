// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse integration tests: axiom profiles, compaction, deps, stress, provenance, edge cases.
//!
//! Continuation of `mathverse_integration_tests.rs` (categories 5-10).
//! All tests use synthetic data -- no external file dependencies.

use clean_kernel::flat::{FlatExpr, FlatLevel};

use crate::library::MathverseLibrary;
use crate::search::{DomainQuery, MathverseSearch};
use crate::shard::{ShardReader, ShardWriter};
use crate::trust::policy::TrustPolicy;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

fn scaffold() -> (ShardWriter, u32, u32) {
    let mut w = ShardWriter::new();
    let l0 = w.add_level(FlatLevel::zero());
    let e0 = w.add_expr(FlatExpr::sort(l0));
    (w, l0, e0)
}

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

fn round_trip(w: &ShardWriter) -> ShardReader {
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

// ===========================================================================
// Category 5: Axiom profile tests
// ===========================================================================

#[test]
fn test_axiom_profile_pure_is_kernel_verified() {
    assert!(AxiomProfile::NONE.is_pure());
    assert!(AxiomProfile::NONE.is_kernel_verified());
    assert!(!AxiomProfile::NONE.is_trust_gated());
    assert_eq!(AxiomProfile::NONE.axiom_count(), 0);
}

#[test]
fn test_axiom_profile_union_propagation() {
    let zfc = AxiomProfile::CHOICE | AxiomProfile::LEM;
    let hol = AxiomProfile::HOL_EMBEDDING;
    let combined = zfc.union(hol);

    assert!(combined.has(AxiomProfile::CHOICE));
    assert!(combined.has(AxiomProfile::LEM));
    assert!(combined.has(AxiomProfile::HOL_EMBEDDING));
    assert!(!combined.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_axiom_profile_trust_gated_bits() {
    // AXIOMATIZED, UNIVERSE_INCON, FLOAT_APPROX, NN_ABSTRACTION are trust-gated.
    assert!(AxiomProfile::AXIOMATIZED.is_trust_gated());
    assert!(AxiomProfile::UNIVERSE_INCON.is_trust_gated());
    assert!(AxiomProfile::FLOAT_APPROX.is_trust_gated());
    assert!(AxiomProfile::NN_ABSTRACTION.is_trust_gated());

    // Non-gated bits.
    assert!(!AxiomProfile::CHOICE.is_trust_gated());
    assert!(!AxiomProfile::LEM.is_trust_gated());
    assert!(!AxiomProfile::PROP_EXT.is_trust_gated());
    assert!(!AxiomProfile::HOL_EMBEDDING.is_trust_gated());
    assert!(!AxiomProfile::MIZAR_TG.is_trust_gated());
}

#[test]
fn test_axiom_profile_filter_in_library() {
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
        "classical.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::CHOICE | AxiomProfile::LEM,
    );
    add_named_constant(
        &mut w,
        "propext.thm",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::PROP_EXT,
    );
    add_named_constant(
        &mut w,
        "axiomatized.thm",
        e0,
        NO_VALUE,
        SourceSystem::Lean4,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::AXIOMATIZED,
    );
    let shard = round_trip(&w);

    // Default policy: only trust-gated are hidden.
    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&shard).unwrap();

    assert!(lib.lookup_name("pure.thm").is_some());
    assert!(lib.lookup_name("classical.thm").is_some());
    assert!(lib.lookup_name("propext.thm").is_some());
    assert!(lib.lookup_name("axiomatized.thm").is_none());
}

#[test]
fn test_default_library_filters_low_confidence_candidates_without_profile_bits() {
    let (mut w, _l0, e0) = scaffold();

    add_named_constant(
        &mut w,
        "candidate.verified",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "candidate.axiomatized_confidence_only",
        e0,
        NO_VALUE,
        SourceSystem::Lean4,
        ImportConfidence::Axiomatized,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    add_named_constant(
        &mut w,
        "candidate.unverified_confidence_only",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::Unverified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard = round_trip(&w);

    // #3702/#3713/#3714 replacement search must fail closed even when a
    // low-trust shard header forgot to set AXIOMATIZED/TRUST_GATED bits.
    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&shard).unwrap();

    assert!(lib.lookup_name("candidate.verified").is_some());
    assert!(lib
        .lookup_name("candidate.axiomatized_confidence_only")
        .is_none());
    assert!(lib
        .lookup_name("candidate.unverified_confidence_only")
        .is_none());

    let type_names: Vec<String> = lib
        .search_type(e0, 10)
        .unwrap()
        .into_iter()
        .filter_map(|result| lib.get_name(result.constant_idx).map(str::to_owned))
        .collect();
    assert_eq!(type_names, vec!["candidate.verified"]);

    let domain_names: Vec<String> = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("candidate".to_owned()),
        )
        .unwrap()
        .into_iter()
        .filter_map(|result| lib.get_name(result.constant_idx).map(str::to_owned))
        .collect();
    assert_eq!(domain_names, vec!["candidate.verified"]);

    let mut permissive = MathverseLibrary::new(TrustPolicy::permissive());
    permissive.load_shard(&shard).unwrap();
    assert!(permissive
        .lookup_name("candidate.axiomatized_confidence_only")
        .is_some());
    assert!(permissive
        .lookup_name("candidate.unverified_confidence_only")
        .is_some());
}

#[test]
fn test_axiom_profile_superset_check() {
    let zfc = AxiomProfile::CHOICE | AxiomProfile::LEM | AxiomProfile::PROP_EXT;
    let classical = AxiomProfile::CHOICE | AxiomProfile::LEM;

    assert!(zfc.is_superset_of(classical));
    assert!(!classical.is_superset_of(zfc));
    assert!(zfc.contains(classical));
}

#[test]
fn test_axiom_profile_propagation_through_library() {
    use crate::trust::policy::propagate_axiom_profiles;

    let make_header = |profile: AxiomProfile| MathverseConstantHeader {
        name_idx: 0,
        type_idx: 0,
        value_idx: 0,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    };

    // 0: CHOICE (leaf)
    // 1: HOL_EMBEDDING (leaf)
    // 2: depends on 0 and 1
    // 3: depends on 2
    let mut headers = vec![
        make_header(AxiomProfile::CHOICE),
        make_header(AxiomProfile::HOL_EMBEDDING),
        make_header(AxiomProfile::LEM),
        make_header(AxiomProfile::NONE),
    ];
    let deps = vec![vec![], vec![], vec![0, 1], vec![2]];

    propagate_axiom_profiles(&mut headers, &deps).unwrap();

    // 2 should now have CHOICE | HOL_EMBEDDING | LEM.
    assert!(headers[2].axiom_profile.has(AxiomProfile::CHOICE));
    assert!(headers[2].axiom_profile.has(AxiomProfile::HOL_EMBEDDING));
    assert!(headers[2].axiom_profile.has(AxiomProfile::LEM));

    // 3 should inherit everything from 2.
    assert!(headers[3].axiom_profile.has(AxiomProfile::CHOICE));
    assert!(headers[3].axiom_profile.has(AxiomProfile::HOL_EMBEDDING));
    assert!(headers[3].axiom_profile.has(AxiomProfile::LEM));
}

// ===========================================================================
// Category 6: Shard compaction integration tests
// ===========================================================================

#[test]
fn test_compact_deltas_preserves_multi_system_data() {
    use crate::shard::compact_deltas;

    let dir = tempfile::tempdir().unwrap();

    // Shard 0: Metamath constants.
    let path0 = dir.path().join("mm.mathverse");
    {
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
        w.write_to_file(&path0).unwrap();
    }

    // Shard 1: HOL constants.
    let path1 = dir.path().join("hol.mathverse");
    {
        let (mut w, _l0, e0) = scaffold();
        add_named_constant(
            &mut w,
            "BOOL_CASES_AX",
            e0,
            e0,
            SourceSystem::HolLight,
            ImportConfidence::Translated,
            ContentDomain::Logic,
            AxiomProfile::HOL_EMBEDDING,
        );
        w.write_to_file(&path1).unwrap();
    }

    let shard0 = ShardReader::from_file(&path0).unwrap();
    let shard1 = ShardReader::from_file(&path1).unwrap();

    let out_path = dir.path().join("compacted.mathverse");
    compact_deltas(&[shard0, shard1], &out_path).unwrap();

    let result = ShardReader::from_file(&out_path).unwrap();
    assert_eq!(result.header.constant_count, 2);

    let (_, hdr) = result.lookup_name("ax-mp").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::Metamath as u8);

    let (_, hdr) = result.lookup_name("BOOL_CASES_AX").unwrap();
    assert_eq!(hdr.source_system, SourceSystem::HolLight as u8);
    assert!(hdr.axiom_profile.has(AxiomProfile::HOL_EMBEDDING));
}

// ===========================================================================
// Category 7: Multi-shard library with dependency walking
// ===========================================================================

#[test]
fn test_library_dependency_walk_across_shards() {
    let (mut w1, _l0, e0) = scaffold();
    add_named_constant(
        &mut w1,
        "Base.Nat",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard1 = round_trip(&w1);

    let (mut w2, _l0, e0) = scaffold();
    add_named_constant(
        &mut w2,
        "Derived.add",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );
    let shard2 = round_trip(&w2);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard1).unwrap();
    lib.load_shard(&shard2).unwrap();

    // Manually add cross-shard dependency.
    lib.add_dependency(1, 0); // Derived.add depends on Base.Nat

    let walked: Vec<u32> = lib.walk_deps(1).collect();
    assert!(walked.contains(&0), "should walk across shard boundaries");
    assert!(walked.contains(&1), "should include root");
}

// ===========================================================================
// Category 8: Large shard stress test
// ===========================================================================

#[test]
fn test_large_shard_1000_constants() {
    let (mut w, _l0, e0) = scaffold();

    for i in 0..1000 {
        add_named_constant(
            &mut w,
            &format!("Mathlib.Topology.Theorem.{i:04}"),
            e0,
            e0,
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        );
    }

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 1000);
    assert!(reader.has_sorted_index());

    // Verify random lookups work.
    for i in [0, 42, 500, 999] {
        let name = format!("Mathlib.Topology.Theorem.{i:04}");
        assert!(reader.lookup_name(&name).is_some(), "should find {name}");
    }

    // Verify negative lookups.
    assert!(reader
        .lookup_name("Mathlib.Topology.Theorem.9999")
        .is_none());

    // Load into library and verify search.
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();
    assert_eq!(lib.constant_count(), 1000);

    let results = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("Topology".to_string()),
        )
        .unwrap();
    assert_eq!(
        results.len(),
        1000,
        "all 1000 topology theorems should match"
    );
}

// ===========================================================================
// Category 9: Provenance sidecar round-trip
// ===========================================================================

#[test]
fn test_shard_provenance_sidecar_round_trip() {
    // Provenance is a structured bincode-serialised
    // `ProvenanceSidecar`, not raw bytes — the reader's validator
    // deserialises it on load. Build a real sidecar with one record
    // and digest the constant header to match.
    use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};

    let mut w = ShardWriter::new();
    let l0 = w.add_level(FlatLevel::zero());
    let e0 = w.add_expr(FlatExpr::sort(l0));

    let ni = w.add_string("test.thm");

    let mut sidecar = ProvenanceSidecar::new();
    let record = ProvenanceBuilder::new("test.thm").build();
    let (prov_idx, digest) = add_provenance(&mut sidecar, record);

    w.add_constant(MathverseConstantHeader {
        name_idx: ni,
        type_idx: e0,
        value_idx: e0,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: digest,
        provenance_idx: prov_idx,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    w.set_provenance(sidecar.to_bytes().expect("encode provenance"));

    let reader = round_trip(&w);

    assert_eq!(reader.header.constant_count, 1);
    assert!(!reader.provenance.is_empty());
    let decoded = ProvenanceSidecar::from_bytes(&reader.provenance).expect("decode provenance");
    assert_eq!(decoded.len(), 1);

    let (_, hdr) = reader.lookup_name("test.thm").unwrap();
    assert_eq!(hdr.sidecar_digest, digest);
    assert_eq!(hdr.provenance_idx, prov_idx);
}

// ===========================================================================
// Category 10: Edge cases
// ===========================================================================

#[test]
fn test_empty_shard_round_trip() {
    let w = ShardWriter::new();
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 0);
    // string_count and level_count are each 1 — the pre-seeded sentinel
    // (empty string at index 0, zero level at index 0) is present even
    // in an "empty" shard.
    assert_eq!(reader.header.string_count, 1);
    assert_eq!(reader.header.expr_count, 0);
    assert_eq!(reader.header.level_count, 1);
    assert!(reader.lookup_name("anything").is_none());
}

#[test]
fn test_shard_checksum_mismatch_detected() {
    let (mut w, _l0, e0) = scaffold();
    add_named_constant(
        &mut w,
        "test",
        e0,
        e0,
        SourceSystem::Lean4,
        ImportConfidence::KernelVerified,
        ContentDomain::PureMath,
        AxiomProfile::NONE,
    );

    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();

    // Corrupt a byte in the middle.
    let mid = buf.len() / 2;
    buf[mid] ^= 0xFF;

    let result = ShardReader::from_bytes(&buf);
    assert!(result.is_err(), "corrupted shard should fail checksum");
}

#[test]
fn test_library_load_empty_shard() {
    let w = ShardWriter::new();
    let mut buf = Vec::new();
    w.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let added = lib.load_shard(&reader).unwrap();
    assert_eq!(added, 0);
    assert_eq!(lib.constant_count(), 0);
}

#[test]
fn test_all_source_systems_round_trip() {
    let systems = [
        SourceSystem::Lean4,
        SourceSystem::Coq,
        SourceSystem::Agda,
        SourceSystem::Idris2,
        SourceSystem::FStar,
        SourceSystem::Isabelle,
        SourceSystem::HolLight,
        SourceSystem::Hol4,
        SourceSystem::Metamath,
        SourceSystem::Mizar,
        SourceSystem::Dafny,
        SourceSystem::Why3,
        SourceSystem::GammaCrown,
        SourceSystem::Z3,
        SourceSystem::Cvc5,
        SourceSystem::Vampire,
        SourceSystem::CaDiCaL,
        SourceSystem::Boogie,
        SourceSystem::CleanNative,
        SourceSystem::Arxiv,
    ];

    let (mut w, _l0, e0) = scaffold();
    for (i, &sys) in systems.iter().enumerate() {
        add_named_constant(
            &mut w,
            &format!("system_{i}"),
            e0,
            e0,
            sys,
            ImportConfidence::Translated,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        );
    }

    let reader = round_trip(&w);
    assert_eq!(reader.header.constant_count, systems.len() as u32);

    for (i, &sys) in systems.iter().enumerate() {
        let name = format!("system_{i}");
        let (_, hdr) = reader.lookup_name(&name).unwrap();
        assert_eq!(
            hdr.source_system, sys as u8,
            "source system mismatch for {name}"
        );
    }
}

#[test]
fn test_all_content_domains_round_trip() {
    let domains = [
        ContentDomain::PureMath,
        ContentDomain::Software,
        ContentDomain::Complexity,
        ContentDomain::NnVerification,
        ContentDomain::Physics,
        ContentDomain::Logic,
        ContentDomain::Cryptography,
    ];

    let (mut w, _l0, e0) = scaffold();
    for (i, &domain) in domains.iter().enumerate() {
        add_named_constant(
            &mut w,
            &format!("domain_{i}"),
            e0,
            e0,
            SourceSystem::Lean4,
            ImportConfidence::KernelVerified,
            domain,
            AxiomProfile::NONE,
        );
    }

    let reader = round_trip(&w);
    for (i, &domain) in domains.iter().enumerate() {
        let name = format!("domain_{i}");
        let (_, hdr) = reader.lookup_name(&name).unwrap();
        assert_eq!(
            hdr.content_domain, domain as u8,
            "domain mismatch for {name}"
        );
    }
}

#[test]
fn test_all_import_confidence_levels_round_trip() {
    let levels = [
        ImportConfidence::KernelVerified,
        ImportConfidence::Translated,
        ImportConfidence::Axiomatized,
        ImportConfidence::Unverified,
    ];

    let (mut w, _l0, e0) = scaffold();
    for (i, &conf) in levels.iter().enumerate() {
        add_named_constant(
            &mut w,
            &format!("conf_{i}"),
            e0,
            e0,
            SourceSystem::Lean4,
            conf,
            ContentDomain::PureMath,
            AxiomProfile::NONE,
        );
    }

    let reader = round_trip(&w);
    for (i, &conf) in levels.iter().enumerate() {
        let name = format!("conf_{i}");
        let (_, hdr) = reader.lookup_name(&name).unwrap();
        assert_eq!(
            hdr.import_confidence, conf as u8,
            "confidence mismatch for {name}"
        );
    }
}
