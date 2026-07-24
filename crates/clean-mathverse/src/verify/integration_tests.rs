// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for verification-aware Lean 4 shard conversion.

use super::*;
use crate::shard::ShardReader;
use crate::types::{AxiomProfile, ContentDomain, MathverseConstantHeader, SourceSystem, NO_VALUE};
use clean_kernel::flat::{FlatExpr, FlatLevel};

fn test_shard(names: &[&str]) -> Vec<u8> {
    let mut writer = ShardWriter::new();
    let level_idx = writer.add_level(FlatLevel::zero());
    let expr_idx = writer.add_expr(FlatExpr::sort(level_idx));

    for name in names {
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: expr_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
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
    buf
}

fn test_summary() -> BatchSummary {
    BatchSummary {
        root_dir: "/tmp/lean4".to_string(),
        total_files: 2,
        processed_files: 2,
        load_success: 1,
        load_failure: 1,
        total_constants: 2,
        tc_pass: 1,
        tc_fail: 1,
        total_skipped: 0,
        total_elapsed_secs: 1.25,
        pass_rate_pct: 50.0,
        validation_mode: clean_olean::verify_batch::ValidationMode::InferOnly,
        validation_label: "type-only-infer".to_string(),
        error_categories: BTreeMap::new(),
        modules: vec![
            ModuleResult {
                path: "A.olean".to_string(),
                module_name: "A".to_string(),
                load_ok: true,
                constants_added: 2,
                constants_skipped: 0,
                tc_pass: 1,
                tc_fail: 1,
                elapsed_ms: 10,
                load_error: None,
                tc_errors: BTreeMap::from([("A.bad".to_string(), "type mismatch".to_string())]),
            },
            ModuleResult {
                path: "B.olean".to_string(),
                module_name: "B".to_string(),
                load_ok: false,
                constants_added: 0,
                constants_skipped: 0,
                tc_pass: 0,
                tc_fail: 0,
                elapsed_ms: 5,
                load_error: Some("load failed".to_string()),
                tc_errors: BTreeMap::new(),
            },
        ],
    }
}

fn clean_module(name: &str, constants: usize) -> ModuleResult {
    ModuleResult {
        path: format!("{name}.olean"),
        module_name: name.to_string(),
        load_ok: true,
        constants_added: constants,
        constants_skipped: 0,
        tc_pass: constants,
        tc_fail: 0,
        elapsed_ms: 5,
        load_error: None,
        tc_errors: BTreeMap::new(),
    }
}

fn clean_summary(modules: Vec<ModuleResult>) -> BatchSummary {
    let total: usize = modules.iter().map(|m| m.constants_added).sum();
    BatchSummary {
        root_dir: "/tmp".to_string(),
        total_files: modules.len(),
        processed_files: modules.len(),
        load_success: modules.len(),
        load_failure: 0,
        total_constants: total,
        tc_pass: total,
        tc_fail: 0,
        total_skipped: 0,
        total_elapsed_secs: 0.1,
        pass_rate_pct: 100.0,
        validation_mode: clean_olean::verify_batch::ValidationMode::InferOnly,
        validation_label: "type-only-infer".to_string(),
        error_categories: BTreeMap::new(),
        modules,
    }
}

#[test]
fn test_config_defaults_expected() {
    let config = VerifyOleanConfig::default();
    assert_eq!(config.timeout_secs, 300);
    assert!(!config.parallel);
    assert_eq!(config.fallback_trust, TrustLevel::TrustedOracle);
}

#[test]
fn test_aggregate_verification_reports_empty_report_expected() {
    let summary = aggregate_verification_reports(&[]);
    assert_eq!(summary.total_declarations, 0);
    assert_eq!(summary.total_kernel_verified, 0);
    assert_eq!(summary.total_trusted_oracle, 0);
    assert_eq!(summary.kernel_verified_pct, 0.0);
    assert!(summary.per_source.is_empty());
}

#[test]
fn test_upgrade_shard_trust_levels_tc_failures_and_load_failures_expected() {
    let shard = test_shard(&["A.good", "A.bad", "B.foo"]);
    let upgraded = upgrade_shard_trust_levels(&shard, &test_summary()).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    let by_name: HashMap<&str, u8> = reader
        .constants
        .iter()
        .map(|constant| {
            (
                reader.strings[constant.name_idx as usize].as_str(),
                constant.import_confidence,
            )
        })
        .collect();

    // Name-match upgrade now produces SourceVerified (not KernelVerified)
    // to avoid trust inflation from lossy shard reconstruction.
    assert_eq!(by_name["A.good"], ImportConfidence::SourceVerified as u8);
    assert_eq!(by_name["A.bad"], ImportConfidence::Axiomatized as u8);
    assert_eq!(by_name["B.foo"], ImportConfidence::Axiomatized as u8);
}

#[test]
fn test_upgrade_preserves_constant_count() {
    let names = &["X.a", "X.b", "X.c", "X.d"];
    let shard = test_shard(names);
    let summary = clean_summary(vec![clean_module("X", 4)]);

    let upgraded = upgrade_shard_trust_levels(&shard, &summary).unwrap();
    let original = ShardReader::from_bytes(&shard).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    assert_eq!(reader.constants.len(), original.constants.len());
    assert_eq!(reader.constants.len(), 4);
}

#[test]
fn test_upgrade_all_pass_marks_source_verified() {
    let names = &["M.x", "M.y"];
    let shard = test_shard(names);
    let summary = clean_summary(vec![clean_module("M", 2)]);

    let upgraded = upgrade_shard_trust_levels(&shard, &summary).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    for constant in &reader.constants {
        assert_eq!(
            constant.import_confidence,
            ImportConfidence::SourceVerified as u8,
            "constant {} should be SourceVerified (name-match upgrade, not KernelVerified)",
            reader.strings[constant.name_idx as usize]
        );
    }
}

#[test]
fn test_upgrade_preserves_axiom_profile_and_metadata() {
    use crate::provenance::{add_provenance, ProvenanceBuilder, ProvenanceSidecar};

    let mut writer = ShardWriter::new();
    let level_idx = writer.add_level(FlatLevel::zero());
    let expr_idx = writer.add_expr(FlatExpr::sort(level_idx));
    let name_idx = writer.add_string("P.q");

    // sidecar_digest cannot be nonzero without a backing provenance
    // sidecar — the shard validator rejects that combination. Build a
    // real sidecar so the digest is meaningful (and gets preserved
    // through the upgrade).
    let mut sidecar = ProvenanceSidecar::new();
    let record = ProvenanceBuilder::new("P.q").build();
    let (prov_idx, digest) = add_provenance(&mut sidecar, record);

    let profile = AxiomProfile(0x0000_0000_0000_000F);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: expr_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
        import_confidence: ImportConfidence::Unverified as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: 0,
        axiom_profile: profile,
        sidecar_digest: digest,
        provenance_idx: prov_idx,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
    writer.set_provenance(sidecar.to_bytes().expect("encode provenance"));

    let mut shard = Vec::new();
    writer.write(&mut shard).unwrap();

    let summary = clean_summary(vec![clean_module("P", 1)]);

    let upgraded = upgrade_shard_trust_levels(&shard, &summary).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.axiom_profile, profile);
    assert_eq!(c.sidecar_digest, digest);
    assert_eq!(c.import_confidence, ImportConfidence::SourceVerified as u8);
}

#[test]
fn test_build_tc_error_set_collects_across_modules() {
    let summary = test_summary();
    let errors = build_tc_error_set(&summary);
    assert!(errors.contains("A.bad"));
    assert!(!errors.contains("A.good"));
    assert_eq!(errors.len(), 1);
}

#[test]
fn test_build_tc_error_set_empty_on_clean_summary() {
    let summary = clean_summary(vec![clean_module("C", 1)]);
    let errors = build_tc_error_set(&summary);
    assert!(errors.is_empty());
}

#[test]
fn test_confidence_for_fallback_trust_mapping() {
    assert_eq!(
        confidence_for_fallback_trust(TrustLevel::KernelVerified) as u8,
        ImportConfidence::KernelVerified as u8
    );
    assert_eq!(
        confidence_for_fallback_trust(TrustLevel::CertificateReplayed) as u8,
        ImportConfidence::Translated as u8
    );
    assert_eq!(
        confidence_for_fallback_trust(TrustLevel::TrustedOracle) as u8,
        ImportConfidence::Axiomatized as u8
    );
    assert_eq!(
        confidence_for_fallback_trust(TrustLevel::AxiomDependent) as u8,
        ImportConfidence::Axiomatized as u8
    );
    assert_eq!(
        confidence_for_fallback_trust(TrustLevel::PartiallyAxiomatized) as u8,
        ImportConfidence::Axiomatized as u8
    );
}

#[test]
fn test_aggregate_multiple_reports() {
    let reports = vec![
        VerificationReport {
            source_dir: "/a".to_string(),
            total_constants: 100,
            kernel_verified: 90,
            trusted_oracle: 10,
            failed_load: 1,
            elapsed_secs: 1.0,
            per_module: vec![],
        },
        VerificationReport {
            source_dir: "/b".to_string(),
            total_constants: 200,
            kernel_verified: 180,
            trusted_oracle: 20,
            failed_load: 2,
            elapsed_secs: 2.0,
            per_module: vec![],
        },
    ];
    let summary = aggregate_verification_reports(&reports);
    assert_eq!(summary.total_declarations, 300);
    assert_eq!(summary.total_kernel_verified, 270);
    assert_eq!(summary.total_trusted_oracle, 30);
    assert!((summary.kernel_verified_pct - 90.0).abs() < 0.01);
    assert_eq!(summary.per_source.len(), 2);
}

#[test]
fn test_module_matches_name_exact() {
    assert!(module_matches_name("Nat", "Nat"));
    assert!(module_matches_name("Nat", "Nat.add"));
    assert!(module_matches_name("Nat", "Nat.add.comm"));
    assert!(!module_matches_name("Nat", "Natural"));
    assert!(!module_matches_name("Nat", "NatAdd"));
}

#[test]
fn test_shard_output_path_normal() {
    let path = shard_output_path(Path::new("/data/lean4"), Path::new("/out"));
    assert_eq!(path, PathBuf::from("/out/lean4.mathverse"));
}

#[test]
fn test_shard_output_path_empty_basename_fallback() {
    let path = shard_output_path(Path::new("/"), Path::new("/out"));
    assert_eq!(path, PathBuf::from("/out/lean4.mathverse"));
}

#[test]
fn test_upgrade_with_custom_fallback_confidence() {
    let shard = test_shard(&["A.good", "A.bad"]);
    let summary = BatchSummary {
        root_dir: "/tmp".to_string(),
        total_files: 1,
        processed_files: 1,
        load_success: 1,
        load_failure: 0,
        total_constants: 2,
        tc_pass: 1,
        tc_fail: 1,
        total_skipped: 0,
        total_elapsed_secs: 0.1,
        pass_rate_pct: 50.0,
        validation_mode: clean_olean::verify_batch::ValidationMode::InferOnly,
        validation_label: "type-only-infer".to_string(),
        error_categories: BTreeMap::new(),
        modules: vec![ModuleResult {
            path: "A.olean".to_string(),
            module_name: "A".to_string(),
            load_ok: true,
            constants_added: 2,
            constants_skipped: 0,
            tc_pass: 1,
            tc_fail: 1,
            elapsed_ms: 5,
            load_error: None,
            tc_errors: BTreeMap::from([("A.bad".to_string(), "err".to_string())]),
        }],
    };

    let upgraded =
        upgrade_shard_trust_levels_with_confidence(&shard, &summary, ImportConfidence::Translated)
            .unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    let by_name: HashMap<&str, u8> = reader
        .constants
        .iter()
        .map(|c| {
            (
                reader.strings[c.name_idx as usize].as_str(),
                c.import_confidence,
            )
        })
        .collect();

    assert_eq!(by_name["A.good"], ImportConfidence::SourceVerified as u8);
    assert_eq!(by_name["A.bad"], ImportConfidence::Translated as u8);
}

#[test]
fn test_name_match_upgrade_produces_source_verified_not_kernel_verified() {
    // Core trust inflation fix: name-match upgrade must produce SourceVerified,
    // because the source .olean passed TC but the reconstructed mathverse shard
    // representation may be lossy.
    let shard = test_shard(&["M.theorem1", "M.theorem2"]);
    let summary = clean_summary(vec![clean_module("M", 2)]);

    let upgraded = upgrade_shard_trust_levels(&shard, &summary).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    for constant in &reader.constants {
        let name = reader.strings[constant.name_idx as usize].as_str();
        assert_eq!(
            constant.import_confidence,
            ImportConfidence::SourceVerified as u8,
            "constant {name} should be SourceVerified, not KernelVerified"
        );
        // Verify it is NOT KernelVerified (the old incorrect behavior)
        assert_ne!(
            constant.import_confidence,
            ImportConfidence::KernelVerified as u8,
            "constant {name} must NOT be KernelVerified from name-match alone"
        );
    }
}

#[test]
fn test_trust_ordering_kernel_gt_source_gt_translated_gt_axiomatized() {
    // Verify the trust ordering: KernelVerified > SourceVerified > Translated > Axiomatized > Unverified
    // In Ord terms, "better" means smaller (KernelVerified < SourceVerified < ...).
    assert!(ImportConfidence::KernelVerified < ImportConfidence::SourceVerified);
    assert!(ImportConfidence::SourceVerified < ImportConfidence::Translated);
    assert!(ImportConfidence::Translated < ImportConfidence::Axiomatized);
    assert!(ImportConfidence::Axiomatized < ImportConfidence::Unverified);

    // Verify discriminant stability for shard binary compat
    assert_eq!(ImportConfidence::KernelVerified as u8, 0);
    assert_eq!(ImportConfidence::Translated as u8, 1);
    assert_eq!(ImportConfidence::Axiomatized as u8, 2);
    assert_eq!(ImportConfidence::Unverified as u8, 3);
    assert_eq!(ImportConfidence::SourceVerified as u8, 6);
}

#[test]
fn test_upgrade_never_emits_kernel_verified_invariant() {
    // Trust-model honesty invariant (the `TrustedOracle`-placeholder concern):
    // the name-match upgrade path has NO Clean-kernel re-check wired, so it must
    // NEVER stamp any constant `KernelVerified` regardless of the mix of
    // pass / TC-fail / load-fail constants. The most it may honestly claim is
    // `SourceVerified` (source TC passed) or `Axiomatized` (source TC failed /
    // module failed to load). Only the separate `import_module_verified` path —
    // which receives names verified by OUR kernel — may produce KernelVerified.
    let shard = test_shard(&["A.good", "A.bad", "B.foo"]);
    let upgraded = upgrade_shard_trust_levels(&shard, &test_summary()).unwrap();
    let reader = ShardReader::from_bytes(&upgraded).unwrap();

    let kernel_verified_count = reader
        .constants
        .iter()
        .filter(|c| c.import_confidence == ImportConfidence::KernelVerified as u8)
        .count();
    assert_eq!(
        kernel_verified_count, 0,
        "name-match upgrade must not silently mislabel any constant as \
         KernelVerified (no kernel re-check path is wired here)"
    );

    // Every constant must land in the honest {SourceVerified, Axiomatized} set.
    for c in &reader.constants {
        let conf = c.import_confidence;
        assert!(
            conf == ImportConfidence::SourceVerified as u8
                || conf == ImportConfidence::Axiomatized as u8,
            "constant {} got unexpected confidence {conf}",
            reader.strings[c.name_idx as usize]
        );
    }
}
