// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end pipeline test: build shard -> verify -> search -> reconstruct -> apply to kernel.
//!
//! Exercises the full mathverse library pipeline with synthetic data:
//! 1. ShardWriter builds a shard with 3 dependent constants (A, B depends on A, C depends on B)
//! 2. verify_shard_incremental() verifies all constants pass
//! 3. MathverseLibrary loads the shard and lookup_name works
//! 4. Semantic search finds constants
//! 5. reconstruct_from_shard() converts FlatExpr back to kernel Expr
//! 6. Environment::add_decl() accepts the reconstructed declarations
//! 7. Trust levels propagate correctly through the pipeline

use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::{Declaration, Environment, Name};

use crate::library::MathverseLibrary;
use crate::search::MathverseSearch;
use crate::shard::{ShardReader, ShardWriter};
use crate::shard_reconstruct::reconstruct_from_shard;
use crate::trust::policy::TrustPolicy;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};
use crate::verify::incremental::verify_shard_incremental;

/// Build a synthetic shard with 3 dependent constants:
/// - A: axiom with type Sort(0), no value, no dependencies
/// - B: axiom with type Sort(0), value references A via Const("A"), depends on A
/// - C: axiom with type Sort(0), value references B via Const("B"), depends on B
///
/// Returns (shard_bytes, ShardReader).
fn build_pipeline_shard() -> (Vec<u8>, ShardReader) {
    let mut writer = ShardWriter::new();

    // Level pool
    let l0 = writer.add_level(FlatLevel::zero());

    // Expression arena
    let sort_prop = writer.add_expr(FlatExpr::sort(l0)); // idx 0: Sort(0) = Prop

    // String table
    let name_a = writer.add_string("TestConst.A");
    let name_b = writer.add_string("TestConst.B");
    let name_c = writer.add_string("TestConst.C");

    // Build value expressions for B and C that reference their dependencies
    let const_a = writer.add_expr(FlatExpr::const_ref(name_a, u32::MAX)); // Const("TestConst.A")
    let const_b = writer.add_expr(FlatExpr::const_ref(name_b, u32::MAX)); // Const("TestConst.B")

    // Constant A: no dependencies, axiom (type = Prop, no value)
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_a,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Constant B: depends on A (value references A)
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_b,
        type_idx: sort_prop,
        value_idx: const_a,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Constant C: depends on B (value references B)
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_c,
        type_idx: sort_prop,
        value_idx: const_b,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::CHOICE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    (buf, reader)
}

// ---------------------------------------------------------------------------
// Step 1: Build shard with dependent constants
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step1_build_shard_with_dependencies() {
    let (_buf, reader) = build_pipeline_shard();

    // Verify the shard structure
    assert_eq!(
        reader.header.constant_count, 3,
        "shard should have 3 constants"
    );
    assert_eq!(
        reader.strings.len(),
        4,
        "shard should have 3 user strings + 1 pre-seeded empty sentinel"
    );
    assert!(
        reader.header.level_count >= 1,
        "shard should have at least 1 level"
    );
    assert!(
        reader.header.expr_count >= 3,
        "shard should have at least 3 expressions"
    );

    // Verify name lookup works at the shard level
    assert!(
        reader.lookup_name("TestConst.A").is_some(),
        "A should be findable"
    );
    assert!(
        reader.lookup_name("TestConst.B").is_some(),
        "B should be findable"
    );
    assert!(
        reader.lookup_name("TestConst.C").is_some(),
        "C should be findable"
    );
    assert!(
        reader.lookup_name("TestConst.Z").is_none(),
        "Z should not exist"
    );

    // Verify bloom filter
    assert!(reader.bloom_maybe_contains("TestConst.A"));
    assert!(reader.bloom_maybe_contains("TestConst.B"));
    assert!(reader.bloom_maybe_contains("TestConst.C"));

    // Verify sorted index exists
    assert!(reader.has_sorted_index(), "shard should have sorted index");
}

// ---------------------------------------------------------------------------
// Step 2: Incremental verification
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step2_verify_shard_incremental() {
    let (_buf, reader) = build_pipeline_shard();

    let report = verify_shard_incremental(&reader);

    assert_eq!(report.total, 3, "should consider 3 constants");
    assert_eq!(report.cycle_skipped, 0, "no cycles expected");
    assert_eq!(
        report.reconstruct_failed, 0,
        "no reconstruction failures expected"
    );
    // A is a NO_VALUE theorem and B/C carry synthetic Const bodies the kernel
    // does not accept, so all three fall back to an axiom registration. None is a
    // genuine proof-check: the dependency graph still resolves (no failures) but
    // kernel_verified is honestly 0.
    assert_eq!(
        report.kernel_verified, 0,
        "synthetic pipeline bodies are not genuinely kernel-verified: failures = {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_fallback, 3,
        "all 3 constants fall back to an axiom: failures = {:?}",
        report.failures
    );
    assert_eq!(report.axiom_accepted, 0);
    assert_eq!(report.failed, 0, "no failures expected");
    assert!(
        report.elapsed_secs >= 0.0,
        "elapsed time should be non-negative"
    );
    assert!(
        report.elapsed_secs < 30.0,
        "verification should complete quickly"
    );
}

// ---------------------------------------------------------------------------
// Step 3: Load into MathverseLibrary and verify lookup
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step3_library_load_and_lookup() {
    let (_buf, reader) = build_pipeline_shard();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let added = lib.load_shard(&reader).unwrap();

    assert_eq!(added, 3, "should add 3 constants to library");
    assert_eq!(lib.constant_count(), 3, "library should have 3 constants");

    // Lookup by name (via MathverseSearch trait)
    let a_header = lib.lookup_name("TestConst.A");
    assert!(a_header.is_some(), "A should be found in library");
    let a_hdr = a_header.unwrap();
    assert_eq!(a_hdr.source_system, SourceSystem::Lean4 as u8);
    assert_eq!(
        a_hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );
    assert_eq!(a_hdr.content_domain, ContentDomain::PureMath as u8);

    let b_header = lib.lookup_name("TestConst.B");
    assert!(b_header.is_some(), "B should be found in library");

    let c_header = lib.lookup_name("TestConst.C");
    assert!(c_header.is_some(), "C should be found in library");

    assert!(
        lib.lookup_name("TestConst.Z").is_none(),
        "Z should not exist"
    );

    // get_name accessor
    assert_eq!(lib.get_name(0), Some("TestConst.A"));
    assert_eq!(lib.get_name(1), Some("TestConst.B"));
    assert_eq!(lib.get_name(2), Some("TestConst.C"));
}

// ---------------------------------------------------------------------------
// Step 4: Search (semantic and name lookup)
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step4_search_semantic() {
    let (_buf, reader) = build_pipeline_shard();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // Semantic search for "TestConst" should find all 3
    let results = lib.search_semantic("TestConst", 10).unwrap();
    assert!(
        !results.is_empty(),
        "semantic search for 'TestConst' should return results"
    );

    // All results should have valid constant indices
    for r in &results {
        assert!(
            (r.constant_idx as usize) < lib.constant_count(),
            "constant_idx {} should be in range",
            r.constant_idx
        );
        assert!(r.score > 0.0, "score should be positive");
    }
}

// ---------------------------------------------------------------------------
// Step 5: Reconstruct expressions from shard to kernel Expr
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step5_reconstruct_expressions() {
    let (_buf, reader) = build_pipeline_shard();

    // Reconstruct the type expression for each constant
    for (i, constant) in reader.constants.iter().enumerate() {
        let name = &reader.strings[constant.name_idx as usize];

        // Reconstruct type
        let type_result = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        );
        assert!(
            type_result.is_ok(),
            "type reconstruction failed for {name} (constant {i}): {:?}",
            type_result.err()
        );

        // Reconstruct value (if present)
        if constant.value_idx != NO_VALUE {
            let value_result = reconstruct_from_shard(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                constant.value_idx,
            );
            assert!(
                value_result.is_ok(),
                "value reconstruction failed for {name} (constant {i}): {:?}",
                value_result.err()
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Step 6: Apply reconstructed declarations to kernel Environment
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step6_apply_to_kernel_environment() {
    let (_buf, reader) = build_pipeline_shard();

    let mut env = Environment::new();
    let mut added_count = 0;

    // Add constants in dependency order (A first, then B, then C)
    // The shard is already in dependency order since A has no deps, B deps on A, C on B
    for constant in &reader.constants {
        let name = &reader.strings[constant.name_idx as usize];

        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        )
        .unwrap();

        let decl = if constant.value_idx != NO_VALUE {
            // Try as theorem first, fall back to axiom
            let value_expr = reconstruct_from_shard(
                &reader.exprs,
                &reader.levels,
                &reader.strings,
                constant.value_idx,
            );
            match value_expr {
                Ok(val) => {
                    // Try adding as theorem
                    let thm = Declaration::Theorem {
                        name: Name::from_string(name),
                        level_params: vec![],
                        type_: type_expr.clone(),
                        value: val,
                    };
                    if env.add_decl(thm).is_ok() {
                        added_count += 1;
                        continue;
                    }
                    // Fall back to axiom
                    Declaration::Axiom {
                        name: Name::from_string(name),
                        level_params: vec![],
                        type_: type_expr,
                    }
                }
                Err(_) => Declaration::Axiom {
                    name: Name::from_string(name),
                    level_params: vec![],
                    type_: type_expr,
                },
            }
        } else {
            Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_: type_expr,
            }
        };

        let result = env.add_decl(decl);
        assert!(
            result.is_ok(),
            "kernel add_decl failed for {name}: {:?}",
            result.err()
        );
        added_count += 1;
    }

    assert_eq!(
        added_count, 3,
        "all 3 constants should be added to kernel environment"
    );
}

// ---------------------------------------------------------------------------
// Step 7: Trust level propagation
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step7_trust_levels_propagated() {
    let (_buf, reader) = build_pipeline_shard();

    // Load into library with default (restrictive) trust policy
    let mut lib_default = MathverseLibrary::new(TrustPolicy::default_policy());
    lib_default.load_shard(&reader).unwrap();

    // A and B have AxiomProfile::NONE (not trust-gated) -> visible
    assert!(
        lib_default.lookup_name("TestConst.A").is_some(),
        "A (NONE profile) should be visible under default policy"
    );
    assert!(
        lib_default.lookup_name("TestConst.B").is_some(),
        "B (NONE profile) should be visible under default policy"
    );
    // C has AxiomProfile::CHOICE which is NOT trust-gated, so it should also be visible
    assert!(
        lib_default.lookup_name("TestConst.C").is_some(),
        "C (CHOICE profile, not trust-gated) should be visible under default policy"
    );

    // Verify axiom profile values are preserved
    let mut lib_perm = MathverseLibrary::new(TrustPolicy::permissive());
    lib_perm.load_shard(&reader).unwrap();

    let a_hdr = lib_perm.lookup_name("TestConst.A").unwrap();
    assert!(
        a_hdr.axiom_profile.is_pure(),
        "A should have pure (NONE) axiom profile"
    );
    assert!(!a_hdr.is_trust_gated(), "A should not be trust-gated");

    let c_hdr = lib_perm.lookup_name("TestConst.C").unwrap();
    assert!(
        c_hdr.axiom_profile.has(AxiomProfile::CHOICE),
        "C should have CHOICE bit set"
    );
    assert!(
        !c_hdr.is_trust_gated(),
        "C (CHOICE only) should not be trust-gated"
    );

    // Verify import confidence is preserved
    assert_eq!(
        a_hdr.import_confidence,
        ImportConfidence::KernelVerified as u8,
        "import confidence should be preserved"
    );

    // Verify content domain is preserved
    assert_eq!(
        a_hdr.content_domain,
        ContentDomain::PureMath as u8,
        "content domain should be PureMath for A"
    );
    assert_eq!(
        c_hdr.content_domain,
        ContentDomain::Logic as u8,
        "content domain should be Logic for C"
    );
}

// ---------------------------------------------------------------------------
// Step 7b: Trust-gated constants filtered under default policy
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_step7b_trust_gated_constants_filtered() {
    // Build a shard with an AXIOMATIZED constant (trust-gated)
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let name_visible = writer.add_string("Visible.Thm");
    let name_gated = writer.add_string("Gated.Thm");

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_visible,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    writer.add_constant(MathverseConstantHeader {
        name_idx: name_gated,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Isabelle as u8,
        import_confidence: ImportConfidence::Axiomatized as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::AXIOMATIZED,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    // Default policy: trust-gated constants hidden
    let mut lib = MathverseLibrary::new(TrustPolicy::default_policy());
    lib.load_shard(&reader).unwrap();

    assert!(
        lib.lookup_name("Visible.Thm").is_some(),
        "non-gated constant should be visible"
    );
    assert!(
        lib.lookup_name("Gated.Thm").is_none(),
        "AXIOMATIZED constant should be hidden under default policy"
    );

    // Permissive policy: all visible
    let mut lib_perm = MathverseLibrary::new(TrustPolicy::permissive());
    lib_perm.load_shard(&reader).unwrap();

    assert!(
        lib_perm.lookup_name("Visible.Thm").is_some(),
        "non-gated constant should be visible under permissive"
    );
    assert!(
        lib_perm.lookup_name("Gated.Thm").is_some(),
        "AXIOMATIZED constant should be visible under permissive policy"
    );
}

// ---------------------------------------------------------------------------
// Full pipeline: single test combining all steps
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_full_pipeline_build_verify_search_reconstruct_apply() {
    // Step 1: Build
    let (_buf, reader) = build_pipeline_shard();
    assert_eq!(reader.header.constant_count, 3);

    // Step 2: Verify incrementally. The synthetic pipeline bodies are not genuine
    // proof-checks, so every constant falls back to an axiom; the graph still
    // resolves (no failures) but kernel_verified is honestly 0.
    let report = verify_shard_incremental(&reader);
    assert_eq!(
        report.kernel_verified, 0,
        "synthetic bodies are not genuinely kernel-verified: {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_fallback, 3,
        "all fall back to an axiom: {:?}",
        report.failures
    );
    assert_eq!(report.failed, 0);
    assert_eq!(report.cycle_skipped, 0);

    // Step 3: Load into library
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let added = lib.load_shard(&reader).unwrap();
    assert_eq!(added, 3);

    // Step 4: Search
    assert!(lib.lookup_name("TestConst.A").is_some());
    assert!(lib.lookup_name("TestConst.B").is_some());
    assert!(lib.lookup_name("TestConst.C").is_some());

    let search_results = lib.search_semantic("TestConst", 10).unwrap();
    assert!(
        !search_results.is_empty(),
        "semantic search should find results"
    );

    // Step 5: Reconstruct
    for constant in &reader.constants {
        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        );
        assert!(type_expr.is_ok(), "type reconstruction should succeed");
    }

    // Step 6: Apply to kernel
    let mut env = Environment::new();
    for constant in &reader.constants {
        let name = &reader.strings[constant.name_idx as usize];
        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        )
        .unwrap();

        let decl = Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: type_expr,
        };
        let result = env.add_decl(decl);
        assert!(result.is_ok(), "add_decl should succeed for {name}");
    }

    // Step 7: Trust levels
    let a_hdr = lib.lookup_name("TestConst.A").unwrap();
    assert!(a_hdr.axiom_profile.is_pure());
    assert_eq!(
        a_hdr.import_confidence,
        ImportConfidence::KernelVerified as u8
    );

    let c_hdr = lib.lookup_name("TestConst.C").unwrap();
    assert!(c_hdr.axiom_profile.has(AxiomProfile::CHOICE));
    assert_eq!(c_hdr.content_domain, ContentDomain::Logic as u8);
}

// ---------------------------------------------------------------------------
// Dependency analysis through the pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_dependency_analysis_through_pipeline() {
    let (_buf, reader) = build_pipeline_shard();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // After loading, dependency analysis should detect the const_ref chains.
    // B's value references A, C's value references B.
    let deps = lib.deps();

    // A (idx 0) has type=Sort, value=NO_VALUE -> no deps
    assert!(
        deps[0].is_empty(),
        "A should have no dependencies, got: {:?}",
        deps[0]
    );

    // B (idx 1) has value=Const("TestConst.A") -> depends on A (idx 0)
    assert!(
        deps[1].contains(&0),
        "B should depend on A (idx 0), got: {:?}",
        deps[1]
    );

    // C (idx 2) has value=Const("TestConst.B") -> depends on B (idx 1)
    assert!(
        deps[2].contains(&1),
        "C should depend on B (idx 1), got: {:?}",
        deps[2]
    );
}

// ---------------------------------------------------------------------------
// Shard round-trip through bytes
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_shard_round_trip_bytes() {
    let (buf, reader1) = build_pipeline_shard();

    // Re-read from the same bytes
    let reader2 = ShardReader::from_bytes(&buf).unwrap();

    assert_eq!(reader1.header.constant_count, reader2.header.constant_count);
    assert_eq!(reader1.header.expr_count, reader2.header.expr_count);
    assert_eq!(reader1.header.level_count, reader2.header.level_count);
    assert_eq!(reader1.strings, reader2.strings);

    // Both readers should find the same constants
    for name in &["TestConst.A", "TestConst.B", "TestConst.C"] {
        let r1 = reader1.lookup_name(name);
        let r2 = reader2.lookup_name(name);
        assert!(r1.is_some(), "reader1 should find {name}");
        assert!(r2.is_some(), "reader2 should find {name}");
        assert_eq!(r1.unwrap().0, r2.unwrap().0, "same index for {name}");
    }
}

// ---------------------------------------------------------------------------
// File-based round trip
// ---------------------------------------------------------------------------

/// Write a 3-constant dependent shard (A, B->A, C->B) to a file.
fn write_dependent_shard_to_file(path: &std::path::Path, prefix: &str) -> [String; 3] {
    let names = [
        format!("{prefix}.A"),
        format!("{prefix}.B"),
        format!("{prefix}.C"),
    ];

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let ni: Vec<u32> = names.iter().map(|n| writer.add_string(n)).collect();

    // A: no deps
    writer.add_constant(MathverseConstantHeader {
        name_idx: ni[0],
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // B: refs A
    let ca = writer.add_expr(FlatExpr::const_ref(ni[0], u32::MAX));
    writer.add_constant(MathverseConstantHeader {
        name_idx: ni[1],
        type_idx: sort_prop,
        value_idx: ca,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // C: refs B
    let cb = writer.add_expr(FlatExpr::const_ref(ni[1], u32::MAX));
    writer.add_constant(MathverseConstantHeader {
        name_idx: ni[2],
        type_idx: sort_prop,
        value_idx: cb,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    writer.write_to_file(path).unwrap();
    names
}

#[test]
fn test_e2e_shard_file_round_trip() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("e2e_test.mathverse");
    let names = write_dependent_shard_to_file(&path, "FileTest");

    // Read from file and run full pipeline
    let reader = ShardReader::from_file(&path).unwrap();
    assert_eq!(reader.header.constant_count, 3);

    // Verify. Same synthetic A/B/C bodies: not genuine proof-checks, so all fall
    // back to an axiom (kernel_verified honestly 0, graph still resolves).
    let report = verify_shard_incremental(&reader);
    assert_eq!(
        report.kernel_verified, 0,
        "synthetic file round-trip bodies are not genuinely kernel-verified: {:?}",
        report.failures
    );
    assert_eq!(
        report.axiom_fallback, 3,
        "file round-trip: {:?}",
        report.failures
    );

    // Load into library
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    for name in &names {
        assert!(
            lib.lookup_name(name).is_some(),
            "should find {name} after file round-trip"
        );
    }

    // Reconstruct and apply to kernel
    let mut env = Environment::new();
    for constant in &reader.constants {
        let name = &reader.strings[constant.name_idx as usize];
        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        )
        .unwrap();

        let decl = Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: type_expr,
        };
        env.add_decl(decl).unwrap();
    }
}

// ---------------------------------------------------------------------------
// Throughput benchmark: measure pipeline ops/sec with synthetic data
// ---------------------------------------------------------------------------

/// Build a shard with N independent axioms for throughput measurement.
fn build_throughput_shard(n: usize) -> (Vec<u8>, ShardReader) {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    for i in 0..n {
        let name = writer.add_string(&format!("Throughput.C{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx: name,
            type_idx: sort_prop,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: 0,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();
    (buf, reader)
}

#[test]
fn test_e2e_throughput_shard_build_1000() {
    let start = std::time::Instant::now();
    let (_buf, reader) = build_throughput_shard(1000);
    let elapsed = start.elapsed();

    assert_eq!(reader.header.constant_count, 1000);
    let rate = 1000.0 / elapsed.as_secs_f64();
    // Shard building should handle at least 10K constants/sec on any machine.
    assert!(
        rate > 10_000.0,
        "shard build rate {rate:.0} constants/sec is below 10K threshold"
    );
}

#[test]
fn test_e2e_throughput_verify_incremental_1000() {
    let (_buf, reader) = build_throughput_shard(1000);

    let start = std::time::Instant::now();
    let report = verify_shard_incremental(&reader);
    let elapsed = start.elapsed();

    assert_eq!(report.total, 1000);
    // These are NO_VALUE decl_kind-0 (theorem) constants, so each falls back to
    // an axiom registration rather than being proof-checked.
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.axiom_fallback, 1000);
    assert_eq!(report.failed, 0);

    let rate = 1000.0 / elapsed.as_secs_f64();
    // Incremental verification should handle at least 1K constants/sec.
    assert!(
        rate > 1_000.0,
        "verify rate {rate:.0} constants/sec is below 1K threshold"
    );
}

#[test]
fn test_e2e_throughput_library_load_and_search_1000() {
    let (_buf, reader) = build_throughput_shard(1000);

    // Library load throughput
    let start = std::time::Instant::now();
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    let added = lib.load_shard(&reader).unwrap();
    let load_elapsed = start.elapsed();

    assert_eq!(added, 1000);
    let load_rate = 1000.0 / load_elapsed.as_secs_f64();
    assert!(
        load_rate > 10_000.0,
        "library load rate {load_rate:.0} constants/sec is below 10K threshold"
    );

    // Lookup throughput: 1000 individual name lookups
    let start = std::time::Instant::now();
    for i in 0..1000 {
        let name = format!("Throughput.C{i}");
        assert!(lib.lookup_name(&name).is_some());
    }
    let lookup_elapsed = start.elapsed();

    let lookup_rate = 1000.0 / lookup_elapsed.as_secs_f64();
    assert!(
        lookup_rate > 10_000.0,
        "lookup rate {lookup_rate:.0} ops/sec is below 10K threshold"
    );
}

#[test]
fn test_e2e_throughput_full_pipeline_100() {
    // Full pipeline at 100 constants: build -> verify -> load -> search -> reconstruct -> add_decl
    let start = std::time::Instant::now();

    let (_buf, reader) = build_throughput_shard(100);

    let report = verify_shard_incremental(&reader);
    // NO_VALUE decl_kind-0 constants fall back to axiom registration, not a
    // genuine proof-check.
    assert_eq!(report.kernel_verified, 0);
    assert_eq!(report.axiom_fallback, 100);

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    for i in 0..100 {
        let name = format!("Throughput.C{i}");
        assert!(lib.lookup_name(&name).is_some());
    }

    let mut env = Environment::new();
    for constant in &reader.constants {
        let name = &reader.strings[constant.name_idx as usize];
        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        )
        .unwrap();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: type_expr,
        })
        .unwrap();
    }

    let elapsed = start.elapsed();
    let rate = 100.0 / elapsed.as_secs_f64();
    assert!(
        rate > 100.0,
        "full pipeline rate {rate:.0} constants/sec is below 100 threshold"
    );
}

// ---------------------------------------------------------------------------
// Domain search through the pipeline
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_domain_search_filters_by_content_domain() {
    use crate::search::{DomainQuery, MathverseSearch};

    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort_prop = writer.add_expr(FlatExpr::sort(l0));

    let name_math = writer.add_string("DomainTest.MathThm");
    let name_logic = writer.add_string("DomainTest.LogicThm");
    let name_sw = writer.add_string("DomainTest.SoftwareSpec");

    // PureMath constant
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_math,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Logic constant
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_logic,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::Logic as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    // Software constant
    writer.add_constant(MathverseConstantHeader {
        name_idx: name_sw,
        type_idx: sort_prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::KernelVerified as u8,
        content_domain: ContentDomain::Software as u8,
        decl_kind: 0,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    // Search PureMath domain — should find math constant
    let math_results = lib
        .search_domain(
            ContentDomain::PureMath,
            &DomainQuery::FreeText("DomainTest".to_string()),
        )
        .unwrap();
    let math_names: Vec<_> = math_results
        .iter()
        .map(|r| &reader.strings[r.header.name_idx as usize])
        .collect();
    assert!(
        math_names.iter().any(|n| n.contains("MathThm")),
        "PureMath domain search should find MathThm, got: {math_names:?}"
    );

    // Search Logic domain — should find logic constant
    let logic_results = lib
        .search_domain(
            ContentDomain::Logic,
            &DomainQuery::FreeText("DomainTest".to_string()),
        )
        .unwrap();
    let logic_names: Vec<_> = logic_results
        .iter()
        .map(|r| &reader.strings[r.header.name_idx as usize])
        .collect();
    assert!(
        logic_names.iter().any(|n| n.contains("LogicThm")),
        "Logic domain search should find LogicThm, got: {logic_names:?}"
    );

    // Search Software domain — should find software constant
    let sw_results = lib
        .search_domain(
            ContentDomain::Software,
            &DomainQuery::FreeText("DomainTest".to_string()),
        )
        .unwrap();
    let sw_names: Vec<_> = sw_results
        .iter()
        .map(|r| &reader.strings[r.header.name_idx as usize])
        .collect();
    assert!(
        sw_names.iter().any(|n| n.contains("SoftwareSpec")),
        "Software domain search should find SoftwareSpec, got: {sw_names:?}"
    );
}

// ---------------------------------------------------------------------------
// Kernel export bridge: clean facade check -> KernelShardBuilder -> shard -> verify
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_bridge_clean_check_to_mathverse_shard() {
    use crate::export::kernel_export::KernelShardBuilder;
    use crate::search::MathverseSearch;

    // Step 1: Parse and type-check Lean source via the clean facade check pipeline
    let source = r#"
def bridgeVal : Nat := 42
theorem bridgeTruth : True := True.intro
"#;
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = clean::CheckConfig::default();
    let check_result =
        clean::load_source_into(&mut env, source, &config).expect("clean check should succeed");
    assert!(
        check_result.errors.is_empty(),
        "clean check should have no errors: {:?}",
        check_result.errors
    );
    assert!(
        check_result.passed_count >= 2,
        "should have at least 2 passed declarations"
    );

    // Step 2: Retrieve declarations from the environment
    let bridge_val_decl = env
        .get_const(&Name::from_string("bridgeVal"))
        .expect("bridgeVal should be in environment after check");
    let bridge_truth_decl = env
        .get_const(&Name::from_string("bridgeTruth"))
        .expect("bridgeTruth should be in environment after check");

    // Step 3: Export to mathverse shard via KernelShardBuilder
    let mut builder = KernelShardBuilder::new();

    // Build Declaration objects from the ConstantInfo in the environment
    let val_decl = Declaration::Axiom {
        name: Name::from_string("bridgeVal"),
        level_params: vec![],
        type_: bridge_val_decl.type_.clone(),
    };
    builder
        .add_declaration(&val_decl, &["bridge", "nat"])
        .expect("add bridgeVal should succeed");

    let truth_decl = Declaration::Axiom {
        name: Name::from_string("bridgeTruth"),
        level_params: vec![],
        type_: bridge_truth_decl.type_.clone(),
    };
    builder
        .add_declaration(&truth_decl, &["bridge", "truth"])
        .expect("add bridgeTruth should succeed");

    // Step 4: Write shard to bytes
    let shard_bytes = builder
        .write_to_bytes()
        .expect("shard write should succeed");
    assert!(!shard_bytes.is_empty(), "shard bytes should be non-empty");

    // Step 5: Read shard back and verify
    let reader = ShardReader::from_bytes(&shard_bytes).expect("shard read should succeed");
    assert_eq!(
        reader.header.constant_count, 2,
        "shard should have 2 constants"
    );

    // Step 6: Verify incrementally. The shard carries references to prelude
    // constants (`Nat`, `True`, `True.intro`) that the build side registered
    // via `Environment::try_with_prelude()`. The verify side must seed the
    // same prelude, otherwise the kernel rejects both constants with
    // "Unknown constant: Nat" / "Unknown constant: True". See #3576.
    let verify_env =
        Environment::try_with_prelude().expect("verify-side prelude should initialize");
    let report = crate::verify::incremental::verify_shard_incremental_with_env(&reader, verify_env);
    assert_eq!(report.total, 2, "should verify 2 constants");
    assert_eq!(
        report.failed, 0,
        "no verification failures expected: {:?}",
        report.failures
    );

    // Step 7: Load into library and search
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).unwrap();

    assert!(
        lib.lookup_name("bridgeVal").is_some(),
        "bridgeVal should be findable in library"
    );
    assert!(
        lib.lookup_name("bridgeTruth").is_some(),
        "bridgeTruth should be findable in library"
    );

    // Semantic search should find bridge constants
    let results = lib.search_semantic("bridge", 10).unwrap();
    assert!(
        !results.is_empty(),
        "semantic search for 'bridge' should return results"
    );

    // Step 8: Reconstruct from shard back to kernel and verify add_decl.
    // Same prelude-seed requirement as Step 6: the reconstructed types
    // reference `Nat` / `True`, which are registered by `init_prelude_*`,
    // not carried in the shard itself. See #3576.
    let mut fresh_env =
        Environment::try_with_prelude().expect("fresh-env prelude should initialize");
    for constant in &reader.constants {
        let name = &reader.strings[constant.name_idx as usize];
        let type_expr = reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            constant.type_idx,
        )
        .expect("type reconstruction should succeed");

        let decl = Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: type_expr,
        };
        fresh_env
            .add_decl(decl)
            .unwrap_or_else(|e| panic!("kernel add_decl failed for {name}: {e:?}"));
    }

    // Verify the fresh environment has the reconstructed constants
    assert!(
        fresh_env
            .get_const(&Name::from_string("bridgeVal"))
            .is_some(),
        "reconstructed bridgeVal should be in fresh environment"
    );
    assert!(
        fresh_env
            .get_const(&Name::from_string("bridgeTruth"))
            .is_some(),
        "reconstructed bridgeTruth should be in fresh environment"
    );
}

// Non-trivial e2e tests (universe polymorphism, DeclKind, dependencies, level lists)
// are in tests_e2e_nontrivial.rs to keep file under size limit.
