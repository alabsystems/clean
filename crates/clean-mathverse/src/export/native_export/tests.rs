// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the native theorem export pipeline.

use super::*;
use crate::shard::ShardReader;
use crate::types::{ImportConfidence, SourceSystem};

#[test]
fn test_export_single_theorem() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("single.mathverse");

    let entry = NativeTheoremEntry {
        name: "Test.singleThm".to_string(),
        type_expr: Expr::sort(Level::zero()),
        value_expr: Some(Expr::sort(Level::zero())),
        content_domain: ContentDomain::PureMath,
        axiom_profile: AxiomProfile::NONE,
        tags: vec!["test".to_string()],
        conjecture_id: None,
    };

    let stats = export_native_theorems(&[entry], &path).unwrap();
    assert_eq!(stats.entries_written, 1);
    assert_eq!(
        stats.by_domain.get(&(ContentDomain::PureMath as u8)),
        Some(&1)
    );

    // Read back the shard.
    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 1);

    let (idx, hdr) = reader
        .lookup_name("Test.singleThm")
        .expect("should find exported theorem");
    assert_eq!(idx, 0);
    assert_eq!(hdr.source_system, SourceSystem::CleanNative as u8);
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(hdr.has_value());
}

#[test]
fn test_export_with_tags_and_conjecture() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("tagged.mathverse");

    let entries = vec![
        NativeTheoremEntry {
            name: "nn_verify.compress_soundness".to_string(),
            type_expr: Expr::sort(Level::zero()),
            value_expr: Some(Expr::sort(Level::zero())),
            content_domain: ContentDomain::NnVerification,
            axiom_profile: AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
            tags: vec!["zonotope".to_string(), "CROWN".to_string()],
            conjecture_id: Some("C001".to_string()),
        },
        NativeTheoremEntry {
            name: "PureMath.addComm".to_string(),
            type_expr: Expr::sort(Level::zero()),
            value_expr: Some(Expr::sort(Level::zero())),
            content_domain: ContentDomain::PureMath,
            axiom_profile: AxiomProfile::NONE,
            tags: vec![],
            conjecture_id: None,
        },
    ];

    let stats = export_native_theorems(&entries, &path).unwrap();
    assert_eq!(stats.entries_written, 2);

    // Check the metadata sidecar exists and contains correct data.
    let sidecar_path = crate::shard_metadata::sidecar_path_for(&path);
    assert!(sidecar_path.exists(), "metadata sidecar should exist");

    let sidecar_json = std::fs::read_to_string(&sidecar_path).unwrap();
    let meta: NativeShardMetadata = serde_json::from_str(&sidecar_json).unwrap();

    // Check tags.
    let tags = meta.tags.get("nn_verify.compress_soundness").unwrap();
    assert_eq!(tags, &["zonotope", "CROWN"]);
    assert!(!meta.tags.contains_key("PureMath.addComm"));

    // Check conjecture refs.
    let conj = meta
        .conjecture_refs
        .get("nn_verify.compress_soundness")
        .unwrap();
    assert_eq!(conj, "C001");
    assert!(!meta.conjecture_refs.contains_key("PureMath.addComm"));

    // Check base metadata.
    assert_eq!(meta.base.system_name, "CleanNative");
    assert_eq!(meta.base.declaration_count, 2);
}

#[test]
fn test_round_trip_native_shard() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("roundtrip.mathverse");

    let prop = Expr::sort(Level::zero());
    let entries = vec![
        NativeTheoremEntry {
            name: "Test.thm1".to_string(),
            type_expr: prop.clone(),
            value_expr: Some(prop.clone()),
            content_domain: ContentDomain::PureMath,
            axiom_profile: AxiomProfile::NONE,
            tags: vec!["algebra".to_string()],
            conjecture_id: None,
        },
        NativeTheoremEntry {
            name: "nn_verify.C001_robustness".to_string(),
            type_expr: prop.clone(),
            value_expr: Some(prop.clone()),
            content_domain: ContentDomain::NnVerification,
            axiom_profile: AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION,
            tags: vec!["CROWN".to_string(), "robustness".to_string()],
            conjecture_id: Some("C001".to_string()),
        },
        NativeTheoremEntry {
            name: "Test.axiom1".to_string(),
            type_expr: prop.clone(),
            value_expr: None,
            content_domain: ContentDomain::Logic,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            tags: vec![],
            conjecture_id: None,
        },
    ];

    let stats = export_native_theorems(&entries, &path).unwrap();
    assert_eq!(stats.entries_written, 3);

    // Read back the shard.
    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 3);

    // Verify first theorem: PureMath, kernel verified.
    let (_, hdr0) = reader
        .lookup_name("Test.thm1")
        .expect("should find Test.thm1");
    assert_eq!(hdr0.source_system, SourceSystem::CleanNative as u8);
    assert_eq!(
        hdr0.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(hdr0.has_value());

    // Verify NN theorem: NnVerification domain, has NN axiom bits.
    let (_, hdr1) = reader
        .lookup_name("nn_verify.C001_robustness")
        .expect("should find nn_verify.C001_robustness");
    assert_eq!(hdr1.content_domain, ContentDomain::NnVerification as u8);
    assert_eq!(hdr1.source_system, SourceSystem::CleanNative as u8);

    // Verify axiom: no value, axiomatized confidence.
    let (_, hdr2) = reader
        .lookup_name("Test.axiom1")
        .expect("should find Test.axiom1");
    assert!(!hdr2.has_value());
    assert_eq!(hdr2.import_confidence, ImportConfidence::Axiomatized as u8);

    // Verify bloom filter for all entries.
    assert!(reader.bloom_maybe_contains("Test.thm1"));
    assert!(reader.bloom_maybe_contains("nn_verify.C001_robustness"));
    assert!(reader.bloom_maybe_contains("Test.axiom1"));
}

#[test]
fn test_collect_nn_verify_theorems_manifest() {
    let entries = collect_nn_verify_theorems();
    // 16 entries: C001 has 2 (soundness + tightness), rest have 1 each = 15 conjectures
    assert_eq!(entries.len(), 16);

    // Verify the manifest contents — spot-check key entries.
    assert_eq!(entries[0].name, "nn_verify.compress_soundness");
    assert_eq!(entries[0].conjecture_id, Some("C001".to_string()));
    assert!(entries[0].tags.contains(&"zonotope".to_string()));

    assert_eq!(entries[1].name, "nn_verify.compress_tightness");
    assert_eq!(entries[1].conjecture_id, Some("C001".to_string()));

    assert_eq!(entries[2].name, "nn_verify.correlation_firewall");
    assert_eq!(entries[2].conjecture_id, Some("C002".to_string()));

    assert_eq!(entries[3].name, "nn_verify.eclipse_convergence");
    assert_eq!(entries[3].conjecture_id, Some("C003".to_string()));

    assert_eq!(entries[4].name, "nn_verify.crown_equals_ibp");
    assert_eq!(entries[4].conjecture_id, Some("C004".to_string()));

    assert_eq!(entries[5].name, "nn_verify.mccormick_attention_tight");
    assert_eq!(entries[5].conjecture_id, Some("C005".to_string()));

    assert_eq!(entries[6].name, "nn_verify.blockwise_equals_monolithic");
    assert_eq!(entries[6].conjecture_id, Some("C006".to_string()));

    assert_eq!(entries[7].name, "nn_verify.streaming_cert_soundness");
    assert_eq!(entries[7].conjecture_id, Some("C007".to_string()));

    assert_eq!(entries[8].name, "nn_verify.ibp_tightness_bound");
    assert_eq!(entries[8].conjecture_id, Some("C008".to_string()));

    assert_eq!(entries[9].name, "nn_verify.crown_exponential_gap");
    assert_eq!(entries[9].conjecture_id, Some("C009".to_string()));

    assert_eq!(entries[10].name, "nn_verify.zonotope_crown_equivalence");
    assert_eq!(entries[10].conjecture_id, Some("C010".to_string()));

    assert_eq!(entries[11].name, "nn_verify.softmax_width_monotone");
    assert_eq!(entries[11].conjecture_id, Some("C011".to_string()));

    assert_eq!(entries[12].name, "nn_verify.relu_stability");
    assert_eq!(entries[12].conjecture_id, Some("C012".to_string()));

    assert_eq!(entries[13].name, "nn_verify.nullstellensatz_sos");
    assert_eq!(entries[13].conjecture_id, Some("C028".to_string()));

    assert_eq!(entries[14].name, "nn_verify.pac_to_proof");
    assert_eq!(entries[14].conjecture_id, Some("C029".to_string()));

    assert_eq!(entries[15].name, "nn_verify.orbit_crown_speedup");
    assert_eq!(entries[15].conjecture_id, Some("C030".to_string()));

    // All should be NnVerification domain.
    for entry in &entries {
        assert_eq!(entry.content_domain, ContentDomain::NnVerification);
        assert!(entry.axiom_profile.has(AxiomProfile::FLOAT_APPROX));
        assert!(entry.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
        assert!(entry.value_expr.is_some());
    }
}

#[test]
fn test_collect_and_export_nn_verify_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("nn_verify.mathverse");

    let entries = collect_nn_verify_theorems();
    let stats = export_native_theorems(&entries, &path).unwrap();
    assert_eq!(stats.entries_written, 16);
    assert_eq!(
        stats.by_domain.get(&(ContentDomain::NnVerification as u8)),
        Some(&16)
    );

    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 16);

    // All 16 should be findable by name.
    for entry in &entries {
        let result = reader.lookup_name(&entry.name);
        assert!(result.is_some(), "should find {}", entry.name);
        let (_, hdr) = result.unwrap();
        assert_eq!(hdr.source_system, SourceSystem::CleanNative as u8);
    }

    // Metadata sidecar should have conjecture refs for all 16 entries.
    let sidecar_path = crate::shard_metadata::sidecar_path_for(&path);
    let sidecar_json = std::fs::read_to_string(&sidecar_path).unwrap();
    let meta: NativeShardMetadata = serde_json::from_str(&sidecar_json).unwrap();
    assert_eq!(meta.conjecture_refs.len(), 16);
    assert_eq!(
        meta.conjecture_refs.get("nn_verify.compress_soundness"),
        Some(&"C001".to_string())
    );
    assert_eq!(
        meta.conjecture_refs.get("nn_verify.orbit_crown_speedup"),
        Some(&"C030".to_string())
    );
}

#[test]
fn test_export_empty_entries() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("empty.mathverse");

    let stats = export_native_theorems(&[], &path).unwrap();
    assert_eq!(stats.entries_written, 0);

    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_export_kernel_verified_entry_preserves_axiomatized_profile() {
    // Regression: a kernel-verified theorem that is *axiom-relative* (e.g. a
    // Metamath `set.mm` theorem resting on the `$a` postulates) is tagged
    // `KernelVerified` (the kernel re-checked the derivation) AND carries
    // `AxiomProfile::AXIOMATIZED` so it is trust-gated rather than mislabeled
    // as a foundational-only proof. The `has_value`-only classifier used to
    // drop the entry's explicit profile; this test pins the honest behavior.
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("mm_kv.mathverse");

    let prop = Expr::sort(Level::zero());
    let entry = NativeTheoremEntry {
        name: "metamath.a1i".to_string(),
        type_expr: prop.clone(),
        value_expr: Some(prop.clone()),
        content_domain: ContentDomain::Logic,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        tags: vec!["metamath".to_string(), "set.mm".to_string()],
        conjecture_id: None,
    };

    let stats = export_native_theorems(&[entry], &path).unwrap();
    assert_eq!(stats.entries_written, 1);

    let reader = ShardReader::from_file(&path).unwrap();
    let (_, hdr) = reader
        .lookup_name("metamath.a1i")
        .expect("should find metamath.a1i");
    // Kernel re-checked the derivation -> KernelVerified.
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(hdr.has_value());
    // ...but it rests on Metamath's axioms -> AXIOMATIZED bit preserved.
    assert!(
        hdr.axiom_profile.has(AxiomProfile::AXIOMATIZED),
        "axiom-relative kernel-verified entry must carry AXIOMATIZED"
    );
    assert!(
        hdr.is_trust_gated(),
        "AXIOMATIZED entries must be trust-gated"
    );
    // Honesty invariant: it must NOT claim to be foundational-only.
    assert!(!hdr.axiom_profile.is_kernel_verified());
}

#[test]
fn test_export_axiom_no_value() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("axiom.mathverse");

    let entry = NativeTheoremEntry {
        name: "Test.myAxiom".to_string(),
        type_expr: Expr::sort(Level::zero()),
        value_expr: None,
        content_domain: ContentDomain::Logic,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        tags: vec!["logic".to_string()],
        conjecture_id: None,
    };

    let stats = export_native_theorems(&[entry], &path).unwrap();
    assert_eq!(stats.entries_written, 1);

    let reader = ShardReader::from_file(&path).unwrap();
    let (_, hdr) = reader.lookup_name("Test.myAxiom").unwrap();
    assert!(!hdr.has_value());
    assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
}

#[test]
fn test_streaming_export_writes_valid_shard_and_matches_batch() {
    let dir = tempfile::tempdir().unwrap();
    let streamed = dir.path().join("streamed.mathverse");
    let batch = dir.path().join("batch.mathverse");

    // 50 synthetic entries with distinct names; a few are type-only (value None).
    let entries: Vec<NativeTheoremEntry> = (0..50)
        .map(|i| NativeTheoremEntry {
            name: format!("Stream.thm{i}"),
            type_expr: Expr::sort(Level::zero()),
            value_expr: if i % 7 == 0 {
                None
            } else {
                Some(Expr::sort(Level::zero()))
            },
            content_domain: ContentDomain::Logic,
            axiom_profile: AxiomProfile::AXIOMATIZED,
            tags: vec!["metamath".to_string()],
            conjecture_id: None,
        })
        .collect();

    // Feed them one at a time through the streaming exporter.
    let mut exporter = StreamingShardExporter::new();
    assert!(exporter.is_empty());
    for e in &entries {
        exporter.add(e).expect("streaming add should succeed");
    }
    assert_eq!(exporter.len(), 50);
    let s_stats = exporter
        .finish(&streamed)
        .expect("streaming finish should write");
    assert_eq!(s_stats.entries_written, 50);

    // The batch wrapper, for an equivalence check.
    let b_stats = export_native_theorems(&entries, &batch).expect("batch export should write");
    assert_eq!(b_stats.entries_written, 50);

    // `from_file` validates the footer checksum, so a clean reload proves the
    // streamed shard's checksum is correct; both carry the same constant count.
    let rs = ShardReader::from_file(&streamed).expect("streamed shard reloads + checksum valid");
    let rb = ShardReader::from_file(&batch).expect("batch shard reloads + checksum valid");
    assert_eq!(rs.header.constant_count, 50);
    assert_eq!(rs.header.constant_count, rb.header.constant_count);

    // A value-kept sample (thm1) reloads as KernelVerified with its value retained.
    let (_idx, hdr) = rs.lookup_name("Stream.thm1").expect("sample present");
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert!(hdr.has_value());
}

#[test]
fn test_value_less_entry_kernel_verified_opt_in() {
    // A value-less (type-only) entry is `Axiomatized` by default, but
    // `KernelVerified` when the caller opts in via
    // `with_value_less_kernel_verified` — the `--type-only` Metamath export, whose
    // entries were all kernel-verified before their proof terms were dropped.
    let dir = tempfile::tempdir().unwrap();
    let entry = NativeTheoremEntry {
        name: "mm.typeOnlyThm".to_string(),
        type_expr: Expr::sort(Level::zero()),
        value_expr: None, // type-only: proof value dropped from the shard
        content_domain: ContentDomain::Logic,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        tags: vec!["metamath".to_string()],
        conjecture_id: None,
    };

    // Default: a value-less entry is Axiomatized (conservative).
    let path_default = dir.path().join("default.mathverse");
    let mut exp = StreamingShardExporter::new();
    exp.add(&entry).expect("add default");
    exp.finish(&path_default).expect("finish default");
    let reader = ShardReader::from_file(&path_default).expect("reload default");
    let (_, hdr) = reader
        .lookup_name("mm.typeOnlyThm")
        .expect("value-less entry present");
    assert_eq!(
        hdr.import_confidence,
        ImportConfidence::Axiomatized as u8,
        "value-less entry must default to Axiomatized"
    );
    assert!(!hdr.has_value());

    // Opt-in: the SAME value-less entry is KernelVerified, and still round-trips
    // with no stored value.
    let path_kv = dir.path().join("kv.mathverse");
    let mut exp_kv = StreamingShardExporter::new().with_value_less_kernel_verified(true);
    exp_kv.add(&entry).expect("add kv");
    exp_kv.finish(&path_kv).expect("finish kv");
    let reader_kv = ShardReader::from_file(&path_kv).expect("reload kv");
    let (_, hdr_kv) = reader_kv
        .lookup_name("mm.typeOnlyThm")
        .expect("kv entry present");
    assert_eq!(
        hdr_kv.import_confidence,
        ImportConfidence::KernelVerified as u8,
        "with_value_less_kernel_verified must mark the value-less entry KernelVerified"
    );
    assert!(
        !hdr_kv.has_value(),
        "type-only entry stores no value even when KernelVerified"
    );
}
