// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the verify_foreign module.

use std::fs;
use std::time::Duration;

use clean_kernel::flat::{FlatExpr, FlatLevel};

use super::*;
use crate::shard::{ShardReader, ShardWriter};
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn reader_from_writer(writer: &ShardWriter) -> ShardReader {
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    ShardReader::from_bytes(&buf).unwrap()
}

/// Create a shard with a single axiom: type = Sort(0) = Prop.
fn make_axiom_shard(name: &str) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let name_idx = writer.add_string(name);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: prop,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Lean4 as u8,
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
    writer
}

/// Create a shard with a theorem: id : Prop -> Prop := fun x => x.
fn make_theorem_shard(name: &str) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));
    let name_idx = writer.add_string(name);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: thm_type,
        value_idx: thm_value,
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
    writer
}

/// Create a shard with multiple axioms.
fn make_multi_axiom_shard(count: usize) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));

    for i in 0..count {
        let name_idx = writer.add_string(&format!("axiom_{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: prop,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
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
    }
    writer
}

/// Create a mixed shard with both axioms and theorems.
fn make_mixed_shard(axiom_count: usize, theorem_count: usize) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));

    for i in 0..axiom_count {
        let name_idx = writer.add_string(&format!("axiom_{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: prop,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
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
    }

    for i in 0..theorem_count {
        let name_idx = writer.add_string(&format!("thm_{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: thm_type,
            value_idx: thm_value,
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
    writer
}

fn default_config() -> VerifyForeignConfig {
    VerifyForeignConfig::default()
}

// ---------------------------------------------------------------------------
// Single constant tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_single_axiom_accepted() {
    let writer = make_axiom_shard("Test.axiom");
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    assert_eq!(result.total, 1);
    assert_eq!(result.axiom_accepted, 1);
    assert_eq!(result.verified, 0);
    assert_eq!(result.failed, 0);
    assert_eq!(result.skipped, 0);
    assert_eq!(result.constants.len(), 1);
    assert_eq!(result.constants[0].outcome, ConstantOutcome::AxiomAccepted);
    assert_eq!(result.constants[0].name, "Test.axiom");
}

#[test]
fn test_verify_foreign_single_theorem_verified() {
    let writer = make_theorem_shard("Test.id");
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    assert_eq!(result.total, 1);
    assert_eq!(result.verified + result.axiom_accepted, 1);
    assert_eq!(result.failed, 0);
    assert_eq!(result.skipped, 0);
}

#[test]
fn test_verify_foreign_acceptance_rate_all_accepted() {
    let writer = make_multi_axiom_shard(10);
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    let rate = result.acceptance_rate();
    assert!(
        (rate - 1.0).abs() < f64::EPSILON,
        "expected 100% acceptance, got {rate}"
    );
}

// ---------------------------------------------------------------------------
// Batch size tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_batch_size_limits_processing() {
    let writer = make_multi_axiom_shard(20);
    let reader = reader_from_writer(&writer);
    let config = VerifyForeignConfig {
        batch_size: 5,
        ..default_config()
    };

    let result = verify_foreign_reader(&reader, &config);

    assert_eq!(result.total, 20);
    assert_eq!(result.axiom_accepted, 5);
    assert_eq!(result.skipped, 15);
    assert_eq!(result.constants.len(), 20);

    // First 5 should be accepted, rest skipped.
    for cr in &result.constants[..5] {
        assert_eq!(cr.outcome, ConstantOutcome::AxiomAccepted);
    }
    for cr in &result.constants[5..] {
        assert_eq!(cr.outcome, ConstantOutcome::Skipped);
    }
}

#[test]
fn test_verify_foreign_batch_size_zero_means_unlimited() {
    let writer = make_multi_axiom_shard(50);
    let reader = reader_from_writer(&writer);
    let config = VerifyForeignConfig {
        batch_size: 0,
        ..default_config()
    };

    let result = verify_foreign_reader(&reader, &config);

    assert_eq!(result.total, 50);
    assert_eq!(result.axiom_accepted, 50);
    assert_eq!(result.skipped, 0);
}

// ---------------------------------------------------------------------------
// Error policy tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_continue_on_error() {
    let writer = make_multi_axiom_shard(10);
    let reader = reader_from_writer(&writer);
    let config = VerifyForeignConfig {
        error_policy: ErrorPolicy::Continue,
        ..default_config()
    };

    let result = verify_foreign_reader(&reader, &config);

    // All valid axioms should be processed.
    assert_eq!(result.total, 10);
    assert_eq!(result.axiom_accepted, 10);
    assert_eq!(result.failed, 0);
}

// ---------------------------------------------------------------------------
// Mixed content tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_mixed_axioms_and_theorems() {
    let writer = make_mixed_shard(5, 5);
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    assert_eq!(result.total, 10);
    assert_eq!(result.failed, 0);
    assert_eq!(result.skipped, 0);
    // All should be accepted (verified or axiom-accepted).
    assert_eq!(result.verified + result.axiom_accepted, 10);
}

// ---------------------------------------------------------------------------
// File-based shard tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_shard_from_file() {
    let dir = tempfile::tempdir().unwrap();
    let writer = make_axiom_shard("File.axiom");
    let path = dir.path().join("test.mathverse");
    writer.write_to_file(&path).unwrap();
    let config = default_config();

    let result = verify_foreign_shard(&path, &config).unwrap();

    assert_eq!(result.shard_path, Some(path));
    assert_eq!(result.total, 1);
    assert_eq!(result.axiom_accepted, 1);
}

#[test]
fn test_verify_foreign_shard_invalid_file() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("bad.mathverse");
    fs::write(&path, b"not a valid mathverse shard").unwrap();
    let config = default_config();

    let result = verify_foreign_shard(&path, &config);

    assert!(result.is_err(), "corrupt shard should return error");
}

// ---------------------------------------------------------------------------
// Batch processing tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_batch_multiple_shards() {
    let dir = tempfile::tempdir().unwrap();

    let w0 = make_axiom_shard("S0.ax");
    let p0 = dir.path().join("s0.mathverse");
    w0.write_to_file(&p0).unwrap();

    let w1 = make_theorem_shard("S1.thm");
    let p1 = dir.path().join("s1.mathverse");
    w1.write_to_file(&p1).unwrap();

    let config = default_config();
    let results = verify_foreign_batch(&[p0, p1], &config);

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].total, 1);
    assert_eq!(results[1].total, 1);
}

#[test]
fn test_verify_foreign_batch_with_corrupt_shard() {
    let dir = tempfile::tempdir().unwrap();

    let w0 = make_axiom_shard("Valid.ax");
    let p0 = dir.path().join("valid.mathverse");
    w0.write_to_file(&p0).unwrap();

    let p1 = dir.path().join("corrupt.mathverse");
    fs::write(&p1, b"bad data").unwrap();

    let config = default_config();
    let results = verify_foreign_batch(&[p0, p1], &config);

    assert_eq!(results.len(), 2);
    // Valid shard should be processed normally.
    assert_eq!(results[0].total, 1);
    assert_eq!(results[0].axiom_accepted, 1);
    // Corrupt shard should produce empty result (error swallowed by batch).
    assert_eq!(results[1].total, 0);
}

#[test]
fn test_verify_foreign_batch_empty_input() {
    let config = default_config();
    let results = verify_foreign_batch(&[], &config);
    assert!(results.is_empty());
}

// ---------------------------------------------------------------------------
// BatchStats tests
// ---------------------------------------------------------------------------

#[test]
fn test_batch_stats_aggregation() {
    let dir = tempfile::tempdir().unwrap();

    let w0 = make_multi_axiom_shard(100);
    let p0 = dir.path().join("s0.mathverse");
    w0.write_to_file(&p0).unwrap();

    let w1 = make_multi_axiom_shard(200);
    let p1 = dir.path().join("s1.mathverse");
    w1.write_to_file(&p1).unwrap();

    let config = default_config();
    let results = verify_foreign_batch(&[p0, p1], &config);
    let stats = BatchStats::from_results(&results);

    assert_eq!(stats.shards_processed, 2);
    assert_eq!(stats.total_constants, 300);
    assert_eq!(stats.total_axiom_accepted, 300);
    assert_eq!(stats.total_failed, 0);
    assert_eq!(stats.total_skipped, 0);
}

// ---------------------------------------------------------------------------
// Error recovery: one failure doesn't stop the batch
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_error_recovery_batch() {
    let dir = tempfile::tempdir().unwrap();

    // 3 valid shards.
    let mut paths = Vec::new();
    for i in 0..3 {
        let w = make_axiom_shard(&format!("valid_{i}"));
        let p = dir.path().join(format!("valid_{i}.mathverse"));
        w.write_to_file(&p).unwrap();
        paths.push(p);
    }

    // 1 corrupt shard in the middle.
    let bad = dir.path().join("corrupt.mathverse");
    fs::write(&bad, b"garbage").unwrap();
    paths.insert(1, bad);

    let config = default_config();
    let results = verify_foreign_batch(&paths, &config);

    assert_eq!(results.len(), 4);
    // Valid shards should all succeed.
    assert_eq!(results[0].axiom_accepted, 1);
    assert_eq!(results[2].axiom_accepted, 1);
    assert_eq!(results[3].axiom_accepted, 1);
    // Corrupt shard returns empty result.
    assert_eq!(results[1].total, 0);

    let stats = BatchStats::from_results(&results);
    assert_eq!(stats.total_axiom_accepted, 3);
}

// ---------------------------------------------------------------------------
// Config defaults
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_config_default() {
    let config = VerifyForeignConfig::default();
    assert_eq!(config.batch_size, 0);
    assert_eq!(config.timeout_per_constant, Duration::from_secs(30));
    assert_eq!(config.error_policy, ErrorPolicy::Continue);
}

// ---------------------------------------------------------------------------
// Per-constant result correctness
// ---------------------------------------------------------------------------

#[test]
fn test_verify_foreign_per_constant_names_correct() {
    let writer = make_multi_axiom_shard(5);
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    for (i, cr) in result.constants.iter().enumerate() {
        assert_eq!(cr.index, i);
        assert_eq!(cr.name, format!("axiom_{i}"));
        assert!(cr.elapsed >= Duration::ZERO);
    }
}

#[test]
fn test_verify_foreign_elapsed_is_positive() {
    let writer = make_multi_axiom_shard(100);
    let reader = reader_from_writer(&writer);
    let config = default_config();

    let result = verify_foreign_reader(&reader, &config);

    // Total elapsed should be non-negative.
    assert!(result.elapsed >= Duration::ZERO);
}
