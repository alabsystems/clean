// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Lean 4 `.olean` to `.mathverse` shard importer.

use super::*;
use crate::shard::ShardReader;
use crate::types::{AxiomProfile, ImportConfidence, SourceSystem};
use clean_olean::expr::ParsedExpr;
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

/// Build a minimal `ParsedModule` with the given constants.
fn mock_module(constants: Vec<ParsedConstant>) -> ParsedModule {
    ParsedModule {
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// Build a minimal `ParsedConstant`.
fn mock_constant(name: &str, kind: ConstantKind, has_val: bool) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
        value: if has_val {
            Some(ParsedExpr::Sort(ParsedLevel::Zero))
        } else {
            None
        },
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    }
}

#[test]
fn test_importer_default_config() {
    let importer = Lean4OleanImporter::new();
    assert!(!importer.config.skip_sorry);
    assert!(!importer.config.include_private);
    assert_eq!(importer.config.max_expr_depth, 0);
}

#[test]
fn test_importer_custom_config() {
    let config = Lean4ImportConfig::builder()
        .skip_sorry(true)
        .include_private(true)
        .max_expr_depth(256)
        .trusted_module("Init")
        .build();
    let importer = Lean4OleanImporter::with_config(config);
    assert!(importer.config.skip_sorry);
    assert!(importer.config.include_private);
    assert_eq!(importer.config.max_expr_depth, 256);
}

#[test]
fn test_import_parsed_module_to_shard() {
    let constants = vec![
        mock_constant("Nat.add", ConstantKind::Definition, true),
        mock_constant("Nat.add_comm", ConstantKind::Theorem, true),
        mock_constant("Classical.choice", ConstantKind::Axiom, false),
        mock_constant("propext", ConstantKind::Axiom, false),
        mock_constant("Quot", ConstantKind::Quot, false),
    ];
    let module = mock_module(constants);

    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("lean4.mathverse");

    let importer = Lean4OleanImporter::new();
    let result = importer
        .import_parsed_module(&module, &output)
        .expect("import should succeed");

    // Check stats
    assert_eq!(result.stats.total, 5);
    assert_eq!(result.stats.kernel_verified, 3); // Def + Thm + Quot
    assert_eq!(result.stats.axiomatized, 2); // 2 Axioms

    // Check provenance
    assert_eq!(result.provenance.len(), 5);

    // Read back and verify
    let reader = ShardReader::from_file(&output).unwrap();
    assert_eq!(reader.header.constant_count, 5);

    // All should be Lean4 source
    for c in &reader.constants {
        assert_eq!(c.source_system, SourceSystem::Lean4 as u8);
    }

    // Check axiom profiles
    let choice = reader.lookup_name("Classical.choice").unwrap().1;
    assert!(choice.profile().has(AxiomProfile::CHOICE));
    assert!(choice.profile().has(AxiomProfile::AXIOMATIZED));
    assert!(!choice.has_value());

    let propext = reader.lookup_name("propext").unwrap().1;
    assert!(propext.profile().has(AxiomProfile::PROP_EXT));
    assert!(propext.profile().has(AxiomProfile::AXIOMATIZED));

    let quot = reader.lookup_name("Quot").unwrap().1;
    assert!(quot.profile().has(AxiomProfile::QUOT));
    assert!(!quot.profile().has(AxiomProfile::AXIOMATIZED));

    let nat_add = reader.lookup_name("Nat.add").unwrap().1;
    assert!(nat_add.profile().is_pure());
    assert!(nat_add.has_value());
    // #3576: Mock `ParsedExpr::Sort(0)` bodies cannot round-trip to a
    // kernel-verified form because the reconstruction is lossy (placeholder
    // sort, no universe levels). The importer now assigns
    // `ImportConfidence::SourceVerified` in this name-match upgrade path to
    // distinguish "source system verified this constant" from "kernel
    // re-verified the reconstructed shard form". A richer mock that produces
    // a constructible kernel term would yield `KernelVerified`; the fixture
    // here exists to pin the default import path, so `SourceVerified` is the
    // correct pinned value.
    assert_eq!(
        nat_add.import_confidence,
        ImportConfidence::SourceVerified as u8
    );
}

#[test]
fn test_import_parsed_into_writer() {
    let constants = vec![
        mock_constant("A.thm", ConstantKind::Theorem, true),
        mock_constant("B.thm", ConstantKind::Theorem, true),
    ];
    let module = mock_module(constants);

    let importer = Lean4OleanImporter::new();
    let mut writer = ShardWriter::new();
    let stats = importer
        .import_parsed_into(&module, &mut writer)
        .expect("import should succeed");

    assert_eq!(stats.total, 2);
    assert_eq!(stats.kernel_verified, 2);

    // Write and verify
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 2);
    assert!(reader.lookup_name("A.thm").is_some());
    assert!(reader.lookup_name("B.thm").is_some());
}

#[test]
fn test_import_multiple_modules_into_one_shard() {
    let mod_a = mock_module(vec![
        mock_constant("A.x", ConstantKind::Definition, true),
        mock_constant("A.y", ConstantKind::Theorem, true),
    ]);
    let mod_b = mock_module(vec![
        mock_constant("B.x", ConstantKind::Axiom, false),
        mock_constant("B.y", ConstantKind::Inductive, false),
    ]);

    let importer = Lean4OleanImporter::new();
    let mut writer = ShardWriter::new();

    let stats_a = importer
        .import_parsed_into(&mod_a, &mut writer)
        .expect("import A");
    let stats_b = importer
        .import_parsed_into(&mod_b, &mut writer)
        .expect("import B");

    assert_eq!(stats_a.total + stats_b.total, 4);

    // Write combined shard
    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("combined.mathverse");
    writer.write_to_file(&output).unwrap();

    let reader = ShardReader::from_file(&output).unwrap();
    assert_eq!(reader.header.constant_count, 4);
    assert!(reader.lookup_name("A.x").is_some());
    assert!(reader.lookup_name("A.y").is_some());
    assert!(reader.lookup_name("B.x").is_some());
    assert!(reader.lookup_name("B.y").is_some());
}

#[test]
fn test_verify_shard() {
    let constants = vec![
        mock_constant("verified.thm", ConstantKind::Theorem, true),
        mock_constant("an.axiom", ConstantKind::Axiom, false),
        mock_constant("an.opaque", ConstantKind::Opaque, false),
    ];
    let module = mock_module(constants);

    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("test.mathverse");

    let importer = Lean4OleanImporter::new();
    importer
        .import_parsed_module(&module, &output)
        .expect("import should succeed");

    let verify = Lean4OleanImporter::verify_shard(&output).expect("verify should succeed");
    assert_eq!(verify.constant_count, 3);
    assert_eq!(verify.kernel_verified, 1); // only the theorem has value
    assert_eq!(verify.axiomatized, 2); // axiom + opaque have no value
    assert_eq!(verify.trust_gated, 2); // axiom + opaque are trust-gated
    assert!(verify.has_sorted_index);
}

#[test]
fn test_skip_sorry_config() {
    let sorry_expr = ParsedExpr::Const("sorryAx".to_string(), vec![]);
    let constants = vec![
        ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "bad_thm".to_string(),
            kind: ConstantKind::Theorem,
            level_params: Vec::new(),
            type_: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
            value: Some(sorry_expr),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        },
        mock_constant("good_thm", ConstantKind::Theorem, true),
    ];
    let module = mock_module(constants);

    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("no_sorry.mathverse");

    let config = Lean4ImportConfig::builder().skip_sorry(true).build();
    let importer = Lean4OleanImporter::with_config(config);
    let result = importer
        .import_parsed_module(&module, &output)
        .expect("import");

    assert_eq!(result.stats.total, 2);
    assert_eq!(result.stats.skipped, 1);
    assert_eq!(result.stats.kernel_verified, 1);

    // The shard should only contain the good theorem
    let reader = ShardReader::from_file(&output).unwrap();
    assert_eq!(reader.header.constant_count, 1);
    assert!(reader.lookup_name("good_thm").is_some());
    assert!(reader.lookup_name("bad_thm").is_none());
}

#[test]
fn test_lean4_axiom_profile_mapping() {
    use crate::lean4::olean::alpha::compute_axiom_profile;

    // Test the full axiom mapping: Choice, Quot, PropExt
    let choice = mock_constant("Classical.choice", ConstantKind::Axiom, false);
    let propext = mock_constant("propext", ConstantKind::Axiom, false);
    let quot_mk = mock_constant("Quot.mk", ConstantKind::Quot, false);
    let quot_ind = mock_constant("Quot.ind", ConstantKind::Quot, false);
    let quot_lift = mock_constant("Quot.lift", ConstantKind::Quot, false);
    let regular = mock_constant("Nat.add", ConstantKind::Definition, true);

    let prof_choice = compute_axiom_profile(&choice);
    assert!(prof_choice.has(AxiomProfile::CHOICE));
    assert!(prof_choice.has(AxiomProfile::CLASSICAL));
    assert!(prof_choice.has(AxiomProfile::AXIOMATIZED));
    assert!(prof_choice.is_trust_gated());

    let prof_propext = compute_axiom_profile(&propext);
    assert!(prof_propext.has(AxiomProfile::PROP_EXT));
    assert!(prof_propext.has(AxiomProfile::AXIOMATIZED));
    assert!(!prof_propext.has(AxiomProfile::CHOICE));

    for (name, c) in [
        ("Quot.mk", &quot_mk),
        ("Quot.ind", &quot_ind),
        ("Quot.lift", &quot_lift),
    ] {
        let prof = compute_axiom_profile(c);
        assert!(prof.has(AxiomProfile::QUOT), "{name} should have QUOT");
        assert!(
            !prof.has(AxiomProfile::AXIOMATIZED),
            "{name} Quot kind != Axiom"
        );
    }

    let prof_regular = compute_axiom_profile(&regular);
    assert!(prof_regular.is_pure());
    assert!(!prof_regular.is_trust_gated());
}

#[test]
fn test_dedup_stats_populated() {
    // Build a module with constants that share type expressions
    // (all Sort(0)) to exercise deduplication.
    let constants: Vec<ParsedConstant> = (0..20)
        .map(|i| mock_constant(&format!("C.c{i}"), ConstantKind::Theorem, true))
        .collect();
    let module = mock_module(constants);

    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("dedup.mathverse");

    let importer = Lean4OleanImporter::new();
    let result = importer
        .import_parsed_module(&module, &output)
        .expect("import");

    assert_eq!(result.stats.total, 20);
    // All constants share Sort(Zero) for type and value, so there
    // should be significant deduplication.
    assert!(
        result.dedup_stats.levels_deduped > 0
            || result.dedup_stats.exprs_deduped > 0
            || result.dedup_stats.strings_deduped > 0,
        "Should have some deduplication with 20 identical-typed constants"
    );
}

#[test]
fn test_init_constants_round_trip() {
    // Simulate a small Init-like module with Lean 4's core constants.
    let constants = vec![
        // Core types
        mock_constant("Nat", ConstantKind::Inductive, false),
        mock_constant("Nat.zero", ConstantKind::Constructor, false),
        mock_constant("Nat.succ", ConstantKind::Constructor, false),
        mock_constant("Nat.rec", ConstantKind::Recursor, false),
        mock_constant("Bool", ConstantKind::Inductive, false),
        mock_constant("Bool.true", ConstantKind::Constructor, false),
        mock_constant("Bool.false", ConstantKind::Constructor, false),
        // Axioms
        mock_constant("Classical.choice", ConstantKind::Axiom, false),
        mock_constant("propext", ConstantKind::Axiom, false),
        mock_constant("Quot", ConstantKind::Quot, false),
        mock_constant("Quot.mk", ConstantKind::Quot, false),
        mock_constant("Quot.ind", ConstantKind::Quot, false),
        mock_constant("Quot.lift", ConstantKind::Quot, false),
        // Theorems
        mock_constant("Nat.add_comm", ConstantKind::Theorem, true),
        mock_constant("Nat.add_assoc", ConstantKind::Theorem, true),
        mock_constant("Nat.zero_add", ConstantKind::Theorem, true),
    ];
    let module = mock_module(constants);

    let dir = tempfile::tempdir().unwrap();
    let output = dir.path().join("lean4.mathverse");

    let importer = Lean4OleanImporter::new();
    let result = importer
        .import_parsed_module(&module, &output)
        .expect("import");

    assert_eq!(result.stats.total, 16);
    // Kernel verified: 4 Inductive/Constructor + 3 Constructor + 1 Recursor
    //                   + 4 Quot + 3 Theorems = 14
    // Axiomatized: Classical.choice + propext = 2
    assert_eq!(result.stats.kernel_verified, 14);
    assert_eq!(result.stats.axiomatized, 2);

    // Read back and verify all names survive round-trip
    let reader = ShardReader::from_file(&output).unwrap();
    assert_eq!(reader.header.constant_count, 16);

    let expected_names = [
        "Nat",
        "Nat.zero",
        "Nat.succ",
        "Nat.rec",
        "Bool",
        "Bool.true",
        "Bool.false",
        "Classical.choice",
        "propext",
        "Quot",
        "Quot.mk",
        "Quot.ind",
        "Quot.lift",
        "Nat.add_comm",
        "Nat.add_assoc",
        "Nat.zero_add",
    ];
    for name in &expected_names {
        assert!(
            reader.lookup_name(name).is_some(),
            "Expected to find {name} in shard"
        );
    }

    // Verify trust gating
    assert!(reader
        .lookup_name("Classical.choice")
        .unwrap()
        .1
        .is_trust_gated());
    assert!(reader.lookup_name("propext").unwrap().1.is_trust_gated());
    assert!(!reader
        .lookup_name("Nat.add_comm")
        .unwrap()
        .1
        .is_trust_gated());
    assert!(!reader.lookup_name("Quot").unwrap().1.is_trust_gated());
}
