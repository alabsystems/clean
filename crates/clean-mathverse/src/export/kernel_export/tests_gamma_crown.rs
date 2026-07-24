// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gamma-crown integration tests for the kernel export pipeline.

use super::*;
use crate::shard::ShardReader;
use crate::types::{ContentDomain, ImportConfidence, SourceSystem};
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;

/// Build a simple theorem declaration: `thm : Prop := Prop`.
fn make_prop_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // Prop
        value: Expr::sort(Level::zero()), // Prop (not a valid proof, but fine for export)
    }
}

// ---------------------------------------------------------------------------
// Gamma-crown C001-C012, C028-C030 integration tests
// ---------------------------------------------------------------------------

/// The 15 gamma-crown conjectures, each with a unique nn_verify.* name.
/// C001 has two theorems (soundness + tightness), giving 16 total entries.
const GAMMA_CROWN_MANIFEST: &[(&str, &str)] = &[
    ("nn_verify.compress_soundness", "C001"),
    ("nn_verify.compress_tightness", "C001"),
    ("nn_verify.correlation_firewall", "C002"),
    ("nn_verify.eclipse_convergence", "C003"),
    ("nn_verify.crown_equals_ibp", "C004"),
    ("nn_verify.mccormick_attention_tight", "C005"),
    ("nn_verify.blockwise_equals_monolithic", "C006"),
    ("nn_verify.streaming_cert_soundness", "C007"),
    ("nn_verify.ibp_tightness_bound", "C008"),
    ("nn_verify.crown_exponential_gap", "C009"),
    ("nn_verify.zonotope_crown_equivalence", "C010"),
    ("nn_verify.softmax_width_monotone", "C011"),
    ("nn_verify.relu_stability", "C012"),
    ("nn_verify.nullstellensatz_sos", "C028"),
    ("nn_verify.pac_to_proof", "C029"),
    ("nn_verify.orbit_crown_speedup", "C030"),
];

/// Export the gamma-crown conjecture set (16 entries) to a mathverse shard and
/// verify the round-trip: names, trust levels, NnVerification domain, bloom.
#[test]
fn test_kernel_export_all_gamma_crown_conjectures() {
    let mut builder = KernelShardBuilder::new();

    // Build Declaration::Theorem for each conjecture entry.
    for (name, conj_id) in GAMMA_CROWN_MANIFEST {
        let decl = make_prop_theorem(name);
        builder
            .add_declaration(&decl, &["gamma-crown", conj_id])
            .unwrap_or_else(|e| panic!("failed to add {name}: {e}"));
    }

    assert_eq!(builder.entry_count(), 16);

    // Write to bytes and read back.
    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    assert_eq!(reader.header.constant_count, 16);

    // Verify every entry is findable with correct metadata.
    for (i, (name, _conj_id)) in GAMMA_CROWN_MANIFEST.iter().enumerate() {
        let result = reader.lookup_name(name);
        assert!(result.is_some(), "entry {i} ({name}) not found in shard");
        let (_, hdr) = result.unwrap();

        // All are CleanNative, KernelVerified, NnVerification domain.
        assert_eq!(
            hdr.source_system,
            SourceSystem::CleanNative as u8,
            "{name}: wrong source system"
        );
        assert_eq!(
            hdr.import_confidence,
            ImportConfidence::KernelVerified as u8,
            "{name}: wrong import confidence"
        );
        assert_eq!(
            hdr.content_domain,
            ContentDomain::NnVerification as u8,
            "{name}: wrong content domain"
        );
        assert!(hdr.has_value(), "{name}: should have proof value");

        // NN axiom profile bits set.
        assert!(
            hdr.axiom_profile.has(AxiomProfile::FLOAT_APPROX),
            "{name}: missing FLOAT_APPROX"
        );
        assert!(
            hdr.axiom_profile.has(AxiomProfile::NN_ABSTRACTION),
            "{name}: missing NN_ABSTRACTION"
        );
    }

    // Bloom filter should pass for all entries.
    for (name, _) in GAMMA_CROWN_MANIFEST {
        assert!(
            reader.bloom_maybe_contains(name),
            "{name}: bloom filter miss"
        );
    }
}

/// Verify that all 15 conjectures are searchable by NnVerification domain
/// after loading the shard into an MathverseLibrary.
#[test]
fn test_kernel_export_gamma_crown_library_search() {
    use crate::library::MathverseLibrary;
    use crate::search::{DomainQuery, MathverseSearch};
    use crate::trust::policy::TrustPolicy;

    let mut builder = KernelShardBuilder::new();
    for (name, conj_id) in GAMMA_CROWN_MANIFEST {
        let decl = make_prop_theorem(name);
        builder
            .add_declaration(&decl, &["gamma-crown", conj_id])
            .unwrap();
    }

    let bytes = builder.write_to_bytes().unwrap();
    let reader = ShardReader::from_bytes(&bytes).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // All 16 entries should be findable by name lookup.
    for (name, _) in GAMMA_CROWN_MANIFEST {
        assert!(
            lib.lookup_name(name).is_some(),
            "library name lookup failed for {name}"
        );
    }

    // Domain search for NnVerification + "compress" should find C001 entries.
    let compress_results = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("compress".to_string()),
        )
        .unwrap();
    assert_eq!(
        compress_results.len(),
        2,
        "should find 2 C001 entries (soundness + tightness)"
    );

    // Domain search for "crown" should find multiple entries (C004, C009, C010, C030).
    let crown_results = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("crown".to_string()),
        )
        .unwrap();
    assert!(
        crown_results.len() >= 3,
        "should find multiple CROWN-related entries, got {}",
        crown_results.len()
    );

    // Domain search for specific conjectures.
    let softmax = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("softmax".to_string()),
        )
        .unwrap();
    assert_eq!(
        softmax.len(),
        1,
        "should find exactly one softmax entry (C011)"
    );

    let orbit = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("orbit".to_string()),
        )
        .unwrap();
    assert_eq!(orbit.len(), 1, "should find exactly one orbit entry (C030)");

    let pac = lib
        .search_domain(
            ContentDomain::NnVerification,
            &DomainQuery::NNArchitecture("pac".to_string()),
        )
        .unwrap();
    assert_eq!(pac.len(), 1, "should find exactly one pac entry (C029)");
}

/// File-based round-trip: write all gamma-crown conjectures to a .mathverse file
/// and read them back.
#[test]
fn test_kernel_export_gamma_crown_file_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("gamma_crown.mathverse");

    let mut builder = KernelShardBuilder::new();
    for (name, conj_id) in GAMMA_CROWN_MANIFEST {
        let decl = make_prop_theorem(name);
        builder
            .add_declaration(&decl, &["gamma-crown", conj_id])
            .unwrap();
    }
    builder.write_to_file(&path).unwrap();

    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 16);

    // Spot-check first and last.
    assert!(reader.lookup_name("nn_verify.compress_soundness").is_some());
    assert!(reader
        .lookup_name("nn_verify.orbit_crown_speedup")
        .is_some());
}

/// Verify that the native_export manifest matches kernel_export expectations.
#[test]
fn test_kernel_export_native_manifest_consistency() {
    use crate::export::native_export::collect_nn_verify_theorems;

    let native_entries = collect_nn_verify_theorems();
    assert_eq!(native_entries.len(), GAMMA_CROWN_MANIFEST.len());

    // Every native entry name should match our manifest.
    for (i, entry) in native_entries.iter().enumerate() {
        assert_eq!(
            entry.name, GAMMA_CROWN_MANIFEST[i].0,
            "manifest mismatch at index {i}"
        );
    }

    // All conjectures C001-C012, C028-C030 should be present.
    let expected_conjectures = [
        "C001", "C002", "C003", "C004", "C005", "C006", "C007", "C008", "C009", "C010", "C011",
        "C012", "C028", "C029", "C030",
    ];
    for conj in &expected_conjectures {
        let found = native_entries
            .iter()
            .any(|e| e.conjecture_id.as_deref() == Some(conj));
        assert!(found, "conjecture {conj} missing from native manifest");
    }
}
