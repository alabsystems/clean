// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    discover_mathverse_files, source_system_name, verify_shard_dir_default as verify_shard_dir,
    write_results_json,
};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};
use clean_kernel::flat::{FlatExpr, FlatLevel};
use std::fs;
use std::path::{Path, PathBuf};

/// Write a ShardWriter to a temp file and return the path.
fn write_shard_to_file(writer: &ShardWriter, dir: &Path, name: &str) -> PathBuf {
    let path = dir.join(name);
    writer.write_to_file(&path).unwrap();
    path
}

/// Create a shard containing a single axiom with type = Sort(0) = Prop.
fn make_axiom_shard(name: &str, source: SourceSystem) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let name_idx = writer.add_string(name);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: prop,
        value_idx: NO_VALUE,
        source_system: source as u8,
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

/// Create a shard containing a "theorem": id : Prop -> Prop := fun x => x
fn make_theorem_shard(name: &str, source: SourceSystem) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    // Type: Pi (x : Prop), Prop  (i.e., Prop -> Prop)
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    // Value: Lam (x : Prop), x
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));
    let name_idx = writer.add_string(name);
    writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx: thm_type,
        value_idx: thm_value,
        source_system: source as u8,
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

/// Create a multi-constant shard with N axioms from the given source system.
fn make_multi_axiom_shard(prefix: &str, count: usize, source: SourceSystem) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));

    for i in 0..count {
        let name_idx = writer.add_string(&format!("{prefix}.axiom_{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: prop,
            value_idx: NO_VALUE,
            source_system: source as u8,
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

/// Create a multi-constant shard with N theorems (id : Prop -> Prop).
fn make_multi_theorem_shard(prefix: &str, count: usize, source: SourceSystem) -> ShardWriter {
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));

    for i in 0..count {
        let name_idx = writer.add_string(&format!("{prefix}.thm_{i}"));
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: thm_type,
            value_idx: thm_value,
            source_system: source as u8,
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

/// Create a mixed shard with both axioms and theorems across multiple source systems.
fn make_mixed_multi_system_shard(constants_per_system: usize) -> ShardWriter {
    let systems = [
        (SourceSystem::Lean4, "Lean4"),
        (SourceSystem::Coq, "Coq"),
        (SourceSystem::Isabelle, "Isabelle"),
        (SourceSystem::HolLight, "HOL"),
        (SourceSystem::Metamath, "MM"),
        (SourceSystem::Mizar, "Mizar"),
        (SourceSystem::Agda, "Agda"),
        (SourceSystem::FStar, "FStar"),
    ];

    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));

    for (source, name_prefix) in &systems {
        for i in 0..constants_per_system {
            let is_theorem = i % 3 == 0; // 1/3 theorems, 2/3 axioms
            let name_idx = writer.add_string(&format!("{name_prefix}.const_{i}"));
            writer.add_constant(MathverseConstantHeader {
                name_idx,
                type_idx: if is_theorem { thm_type } else { prop },
                value_idx: if is_theorem { thm_value } else { NO_VALUE },
                source_system: *source as u8,
                import_confidence: if is_theorem {
                    ImportConfidence::KernelVerified as u8
                } else {
                    ImportConfidence::Axiomatized as u8
                },
                content_domain: ContentDomain::PureMath as u8,
                decl_kind: 0,
                axiom_profile: if is_theorem {
                    AxiomProfile::NONE
                } else {
                    AxiomProfile::AXIOMATIZED
                },
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start: 0,
                level_params_count: 0,
                _pad2: [0u8; 26],
            });
        }
    }
    writer
}

#[test]
fn test_verify_shard_dir_single_axiom_shard() {
    let dir = tempfile::tempdir().unwrap();
    let writer = make_axiom_shard("Test.axiom", SourceSystem::Lean4);
    let path = write_shard_to_file(&writer, dir.path(), "axiom.mathverse");

    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.shards_processed, 1);
    assert_eq!(report.stats.shards_skipped, 0);
    assert_eq!(report.stats.total_constants, 1);
    // Axiom with type=Prop should be accepted as Translated (axiom accepted)
    assert_eq!(report.stats.translated, 1);
    assert_eq!(report.stats.kernel_verified, 0);
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
}

#[test]
fn test_verify_shard_dir_single_theorem_shard() {
    let dir = tempfile::tempdir().unwrap();
    let writer = make_theorem_shard("Test.id", SourceSystem::Lean4);
    let path = write_shard_to_file(&writer, dir.path(), "theorem.mathverse");

    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.shards_processed, 1);
    assert_eq!(report.stats.total_constants, 1);
    // Constant should be accepted either as verified or translated
    assert_eq!(
        report.stats.kernel_verified + report.stats.translated,
        1,
        "constant should be accepted either as verified or translated"
    );
    assert_eq!(report.stats.type_check_failed, 0);
    assert_eq!(report.stats.reconstruct_failed, 0);
}

#[test]
fn test_verify_shard_dir_multiple_shards() {
    let dir = tempfile::tempdir().unwrap();
    let axiom_writer = make_axiom_shard("Shard0.ax", SourceSystem::Lean4);
    let thm_writer = make_theorem_shard("Shard1.id", SourceSystem::Coq);
    let path0 = write_shard_to_file(&axiom_writer, dir.path(), "shard0.mathverse");
    let path1 = write_shard_to_file(&thm_writer, dir.path(), "shard1.mathverse");

    let report = verify_shard_dir(&[path0, path1]);

    assert_eq!(report.stats.shards_processed, 2);
    assert_eq!(report.stats.total_constants, 2);
    assert_eq!(report.shard_results.len(), 2);
    // Per-system should have entries for both Lean4 and Coq
    assert!(report.per_system.contains_key(&(SourceSystem::Lean4 as u8)));
    assert!(report.per_system.contains_key(&(SourceSystem::Coq as u8)));
}

#[test]
fn test_verify_shard_dir_skips_invalid_file() {
    let dir = tempfile::tempdir().unwrap();
    let bad_path = dir.path().join("corrupt.mathverse");
    fs::write(&bad_path, b"not a valid mathverse shard").unwrap();

    let report = verify_shard_dir(&[bad_path]);

    assert_eq!(report.stats.shards_processed, 0);
    assert_eq!(report.stats.shards_skipped, 1);
    assert_eq!(report.stats.total_constants, 0);
    assert_eq!(report.shard_results.len(), 1);
    assert!(report.shard_results[0].error.is_some());
}

#[test]
fn test_verify_shard_dir_empty_input() {
    let report = verify_shard_dir(&[]);

    assert_eq!(report.stats.shards_processed, 0);
    assert_eq!(report.stats.shards_skipped, 0);
    assert_eq!(report.stats.total_constants, 0);
    assert!(report.shard_results.is_empty());
    assert!(report.per_system.is_empty());
}

#[test]
fn test_verify_shard_dir_per_system_breakdown() {
    let dir = tempfile::tempdir().unwrap();

    // Build a shard with mixed source systems
    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));

    for (name, source) in [
        ("Lean4.a", SourceSystem::Lean4),
        ("Lean4.b", SourceSystem::Lean4),
        ("Coq.a", SourceSystem::Coq),
        ("Metamath.a", SourceSystem::Metamath),
    ] {
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: prop,
            value_idx: NO_VALUE,
            source_system: source as u8,
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

    let path = write_shard_to_file(&writer, dir.path(), "mixed.mathverse");
    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.total_constants, 4);
    assert_eq!(report.per_system.len(), 3); // Lean4, Coq, Metamath

    let lean4_stats = &report.per_system[&(SourceSystem::Lean4 as u8)];
    assert_eq!(lean4_stats.total, 2);

    let coq_stats = &report.per_system[&(SourceSystem::Coq as u8)];
    assert_eq!(coq_stats.total, 1);

    let mm_stats = &report.per_system[&(SourceSystem::Metamath as u8)];
    assert_eq!(mm_stats.total, 1);
}

#[test]
fn test_write_results_json_produces_valid_json() {
    let dir = tempfile::tempdir().unwrap();

    let axiom_writer = make_axiom_shard("Test.axiom", SourceSystem::Lean4);
    let path = write_shard_to_file(&axiom_writer, dir.path(), "test.mathverse");
    let report = verify_shard_dir(&[path]);

    let json_path = dir.path().join("results.json");
    write_results_json(&report, &json_path).unwrap();

    let contents = fs::read_to_string(&json_path).unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&contents).unwrap();

    assert_eq!(parsed["shards_processed"], 1);
    assert_eq!(parsed["total_constants"], 1);
    assert!(parsed["per_system"].is_array());
    assert!(!parsed["per_system"].as_array().unwrap().is_empty());
}

#[test]
fn test_source_system_name_known_ids() {
    assert_eq!(source_system_name(0), "Lean4");
    assert_eq!(source_system_name(1), "Coq");
    assert_eq!(source_system_name(9), "Metamath");
    assert_eq!(source_system_name(27), "clean");
    assert_eq!(source_system_name(255), "Other");
}

#[test]
fn test_verify_shard_dir_shard_results_match_stats() {
    let dir = tempfile::tempdir().unwrap();
    let w0 = make_axiom_shard("S0.ax", SourceSystem::Lean4);
    let w1 = make_axiom_shard("S1.ax", SourceSystem::Coq);
    let p0 = write_shard_to_file(&w0, dir.path(), "s0.mathverse");
    let p1 = write_shard_to_file(&w1, dir.path(), "s1.mathverse");

    let report = verify_shard_dir(&[p0, p1]);

    // Sum of per-shard results should equal global stats
    let total_verified: u64 = report.shard_results.iter().map(|r| r.verified).sum();
    let total_translated: u64 = report.shard_results.iter().map(|r| r.translated).sum();
    let total_failed: u64 = report.shard_results.iter().map(|r| r.failed).sum();

    assert_eq!(total_verified, report.stats.kernel_verified);
    assert_eq!(total_translated, report.stats.translated);
    assert_eq!(
        total_failed,
        report.stats.reconstruct_failed + report.stats.type_check_failed
    );
}

#[test]
fn test_discover_mathverse_files_finds_nested() {
    let dir = tempfile::tempdir().unwrap();
    let sub = dir.path().join("sub");
    fs::create_dir_all(&sub).unwrap();

    let w0 = make_axiom_shard("A", SourceSystem::Lean4);
    let w1 = make_axiom_shard("B", SourceSystem::Lean4);
    write_shard_to_file(&w0, dir.path(), "root.mathverse");
    write_shard_to_file(&w1, &sub, "nested.mathverse");
    // Also create a non-mathverse file that should be skipped
    fs::write(dir.path().join("readme.txt"), "not a shard").unwrap();

    let files = discover_mathverse_files(dir.path());
    assert_eq!(files.len(), 2);
}

#[test]
fn test_discover_mathverse_files_empty_dir() {
    let dir = tempfile::tempdir().unwrap();
    let files = discover_mathverse_files(dir.path());
    assert!(files.is_empty());
}

// ---------------------------------------------------------------------------
// At-scale verification tests: exercise the pipeline with many constants
// across multiple source systems and shards.
// ---------------------------------------------------------------------------

/// 1,000 axioms in a single shard: verify all are accepted as Translated.
#[test]
fn test_verify_at_scale_1k_axioms_single_shard() {
    let dir = tempfile::tempdir().unwrap();
    let count = 1_000;
    let writer = make_multi_axiom_shard("Scale", count, SourceSystem::Lean4);
    let path = write_shard_to_file(&writer, dir.path(), "scale_1k.mathverse");

    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.shards_processed, 1);
    assert_eq!(report.stats.total_constants, count as u64);
    assert_eq!(report.stats.translated, count as u64);
    assert_eq!(report.stats.kernel_verified, 0);
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
}

/// 1,000 kernel-verifiable theorems: verify all are accepted.
#[test]
fn test_verify_at_scale_1k_theorems_single_shard() {
    let dir = tempfile::tempdir().unwrap();
    let count = 1_000;
    let writer = make_multi_theorem_shard("Scale", count, SourceSystem::Lean4);
    let path = write_shard_to_file(&writer, dir.path(), "scale_thm_1k.mathverse");

    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.shards_processed, 1);
    assert_eq!(report.stats.total_constants, count as u64);
    // All should be accepted (verified or translated)
    assert_eq!(
        report.stats.kernel_verified + report.stats.translated,
        count as u64,
        "all 1000 theorems should be accepted"
    );
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
}

/// 10,000 constants across 10 shards: verify pipeline handles multi-shard scale.
#[test]
fn test_verify_at_scale_10k_across_10_shards() {
    let dir = tempfile::tempdir().unwrap();
    let per_shard = 1_000;
    let shard_count = 10;

    let mut paths = Vec::new();
    for i in 0..shard_count {
        let writer = make_multi_axiom_shard(&format!("Shard{i}"), per_shard, SourceSystem::Lean4);
        let path = write_shard_to_file(&writer, dir.path(), &format!("shard_{i}.mathverse"));
        paths.push(path);
    }

    let report = verify_shard_dir(&paths);

    let total = (per_shard * shard_count) as u64;
    assert_eq!(report.stats.shards_processed, shard_count as u64);
    assert_eq!(report.stats.shards_skipped, 0);
    assert_eq!(report.stats.total_constants, total);
    assert_eq!(report.stats.translated, total);
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
    assert_eq!(report.shard_results.len(), shard_count);

    // Each shard result should account for exactly per_shard constants
    for sr in &report.shard_results {
        assert_eq!(sr.num_constants, per_shard);
        assert_eq!(sr.translated, per_shard as u64);
        assert!(sr.error.is_none());
    }
}

/// 8 source systems, 100 constants each (800 total): verify per-system breakdown.
#[test]
fn test_verify_at_scale_multi_system_breakdown() {
    let dir = tempfile::tempdir().unwrap();
    let per_system = 100;
    let writer = make_mixed_multi_system_shard(per_system);
    let path = write_shard_to_file(&writer, dir.path(), "multi_system.mathverse");

    let report = verify_shard_dir(&[path]);

    let total = per_system * 8;
    assert_eq!(report.stats.shards_processed, 1);
    assert_eq!(report.stats.total_constants, total as u64);
    // No failures expected -- all types are valid (Prop or Prop->Prop)
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);

    // 8 systems expected
    assert_eq!(report.per_system.len(), 8);

    // Each system should have exactly per_system constants
    for sys_stats in report.per_system.values() {
        assert_eq!(sys_stats.total, per_system as u64);
        // For each system: 1/3 are theorems (verified or translated), 2/3 are axioms (translated)
        // All should be accepted (zero failures)
        assert_eq!(sys_stats.failed, 0);
        assert_eq!(
            sys_stats.kernel_verified + sys_stats.translated,
            per_system as u64,
        );
    }

    // Global verified + translated should equal total
    assert_eq!(
        report.stats.kernel_verified + report.stats.translated,
        total as u64,
    );
}

/// Verify at-scale with a mix of valid and corrupt shards.
#[test]
fn test_verify_at_scale_mixed_valid_and_corrupt() {
    let dir = tempfile::tempdir().unwrap();

    // 5 valid shards
    let mut paths = Vec::new();
    for i in 0..5 {
        let writer = make_multi_axiom_shard(&format!("Valid{i}"), 200, SourceSystem::Lean4);
        let path = write_shard_to_file(&writer, dir.path(), &format!("valid_{i}.mathverse"));
        paths.push(path);
    }

    // 3 corrupt shards
    for i in 0..3 {
        let corrupt_path = dir.path().join(format!("corrupt_{i}.mathverse"));
        fs::write(&corrupt_path, format!("bad data {i}").as_bytes()).unwrap();
        paths.push(corrupt_path);
    }

    let report = verify_shard_dir(&paths);

    assert_eq!(report.stats.shards_processed, 5);
    assert_eq!(report.stats.shards_skipped, 3);
    assert_eq!(report.stats.total_constants, 1000); // 5 * 200
    assert_eq!(report.stats.translated, 1000);
    assert_eq!(report.shard_results.len(), 8);

    // Count errors in shard results
    let errors: Vec<_> = report
        .shard_results
        .iter()
        .filter(|r| r.error.is_some())
        .collect();
    assert_eq!(
        errors.len(),
        3,
        "should have 3 error results for corrupt shards"
    );
}

/// Verify the per-system stats sum correctly matches global stats.
#[test]
fn test_verify_at_scale_per_system_sums_match_global() {
    let dir = tempfile::tempdir().unwrap();
    let writer = make_mixed_multi_system_shard(50);
    let path = write_shard_to_file(&writer, dir.path(), "sum_check.mathverse");

    let report = verify_shard_dir(&[path]);

    let sys_total: u64 = report.per_system.values().map(|s| s.total).sum();
    let sys_verified: u64 = report.per_system.values().map(|s| s.kernel_verified).sum();
    let sys_translated: u64 = report.per_system.values().map(|s| s.translated).sum();
    let sys_failed: u64 = report.per_system.values().map(|s| s.failed).sum();

    assert_eq!(sys_total, report.stats.total_constants);
    assert_eq!(sys_verified, report.stats.kernel_verified);
    assert_eq!(sys_translated, report.stats.translated);
    assert_eq!(
        sys_failed,
        report.stats.reconstruct_failed + report.stats.type_check_failed,
    );
}

/// JSON output at scale: verify the JSON includes all systems and correct totals.
#[test]
fn test_verify_at_scale_json_output() {
    let dir = tempfile::tempdir().unwrap();

    // Create shards from 3 different systems
    let w0 = make_multi_axiom_shard("Lean4", 500, SourceSystem::Lean4);
    let w1 = make_multi_theorem_shard("Coq", 300, SourceSystem::Coq);
    let w2 = make_multi_axiom_shard("MM", 200, SourceSystem::Metamath);

    let p0 = write_shard_to_file(&w0, dir.path(), "lean4.mathverse");
    let p1 = write_shard_to_file(&w1, dir.path(), "coq.mathverse");
    let p2 = write_shard_to_file(&w2, dir.path(), "mm.mathverse");

    let report = verify_shard_dir(&[p0, p1, p2]);

    let json_path = dir.path().join("results.json");
    write_results_json(&report, &json_path).unwrap();

    let contents = fs::read_to_string(&json_path).unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&contents).unwrap();

    assert_eq!(parsed["shards_processed"], 3);
    assert_eq!(parsed["total_constants"], 1000);
    assert_eq!(parsed["reconstruct_failed"], 0);
    assert_eq!(parsed["type_check_failed"], 0);

    let per_system = parsed["per_system"].as_array().unwrap();
    assert_eq!(per_system.len(), 3);

    // Verify the per-system entries are sorted by total (descending)
    let totals: Vec<u64> = per_system
        .iter()
        .map(|s| s["total"].as_u64().unwrap())
        .collect();
    assert_eq!(
        totals,
        vec![500, 300, 200],
        "per_system should be sorted descending by total"
    );
}

/// Verify discover_mathverse_files + verify_shard_dir end-to-end pipeline.
#[test]
fn test_verify_at_scale_discover_and_verify_pipeline() {
    let dir = tempfile::tempdir().unwrap();
    let sub = dir.path().join("systems");
    let sub_lean = sub.join("lean4");
    let sub_coq = sub.join("coq");
    fs::create_dir_all(&sub_lean).unwrap();
    fs::create_dir_all(&sub_coq).unwrap();

    // Write shards into nested directories
    let w0 = make_multi_axiom_shard("Root", 100, SourceSystem::Lean4);
    write_shard_to_file(&w0, dir.path(), "root.mathverse");

    let w1 = make_multi_theorem_shard("Lean4.Init", 200, SourceSystem::Lean4);
    write_shard_to_file(&w1, &sub_lean, "init.mathverse");

    let w2 = make_multi_axiom_shard("Coq.Stdlib", 150, SourceSystem::Coq);
    write_shard_to_file(&w2, &sub_coq, "stdlib.mathverse");

    // Also write some non-mathverse files
    fs::write(sub_lean.join("notes.txt"), "not a shard").unwrap();

    // Discover phase
    let files = discover_mathverse_files(dir.path());
    assert_eq!(
        files.len(),
        3,
        "should discover 3 .mathverse files recursively"
    );

    // Verify phase
    let report = verify_shard_dir(&files);

    assert_eq!(report.stats.shards_processed, 3);
    assert_eq!(report.stats.total_constants, 450); // 100 + 200 + 150
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
    assert_eq!(report.stats.kernel_verified + report.stats.translated, 450,);
}

/// At scale: verify all 13 named source systems produce correct names.
#[test]
fn test_verify_all_source_system_names_coverage() {
    let named_systems: Vec<(u8, &str)> = vec![
        (0, "Lean4"),
        (1, "Coq"),
        (2, "Agda"),
        (3, "Idris2"),
        (4, "FStar"),
        (5, "Cedille"),
        (6, "Isabelle"),
        (7, "HOLLight"),
        (8, "HOL4"),
        (9, "Metamath"),
        (10, "Mizar"),
        (11, "Dafny"),
        (12, "Why3"),
        (27, "clean"),
    ];
    for (id, expected) in &named_systems {
        assert_eq!(
            source_system_name(*id),
            *expected,
            "mismatch for system id {id}"
        );
    }

    // Unmapped IDs should return "Other"
    for id in [13, 14, 15, 50, 100, 254] {
        assert_eq!(source_system_name(id), "Other");
    }
}

/// Verify that at scale, shard_results have correct per-shard counts.
#[test]
fn test_verify_at_scale_per_shard_result_correctness() {
    let dir = tempfile::tempdir().unwrap();
    let shard_sizes = [100, 250, 500, 1000, 50];

    let mut paths = Vec::new();
    for (i, &size) in shard_sizes.iter().enumerate() {
        let writer = make_multi_axiom_shard(&format!("Shard{i}"), size, SourceSystem::Lean4);
        let path = write_shard_to_file(&writer, dir.path(), &format!("s{i}.mathverse"));
        paths.push(path);
    }

    let report = verify_shard_dir(&paths);

    assert_eq!(report.shard_results.len(), shard_sizes.len());
    for (sr, &expected_size) in report.shard_results.iter().zip(shard_sizes.iter()) {
        assert_eq!(
            sr.num_constants,
            expected_size,
            "shard {} should have {expected_size} constants",
            sr.path.display()
        );
        assert_eq!(sr.translated, expected_size as u64);
        assert_eq!(sr.verified, 0);
        assert_eq!(sr.failed, 0);
        assert!(sr.error.is_none());
    }

    let total: usize = shard_sizes.iter().sum();
    assert_eq!(report.stats.total_constants, total as u64);
}

/// Mixed theorem/axiom shard at scale: verify theorem acceptance rate.
#[test]
fn test_verify_at_scale_theorem_acceptance_rate() {
    let dir = tempfile::tempdir().unwrap();

    let mut writer = ShardWriter::new();
    let level_zero = writer.add_level(FlatLevel::zero());
    let prop = writer.add_expr(FlatExpr::sort(level_zero));
    let bvar0 = writer.add_expr(FlatExpr::bvar(0));
    let thm_type = writer.add_expr(FlatExpr::pi(0, prop, prop));
    let thm_value = writer.add_expr(FlatExpr::lam(0, prop, bvar0));

    let theorem_count = 500;
    let axiom_count = 500;

    // Add 500 theorems
    for i in 0..theorem_count {
        let name_idx = writer.add_string(&format!("Thm.{i}"));
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

    // Add 500 axioms
    for i in 0..axiom_count {
        let name_idx = writer.add_string(&format!("Ax.{i}"));
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

    let path = write_shard_to_file(&writer, dir.path(), "mixed_1k.mathverse");
    let report = verify_shard_dir(&[path]);

    assert_eq!(report.stats.total_constants, 1000);
    // All should be accepted (zero failures)
    assert_eq!(report.stats.reconstruct_failed, 0);
    assert_eq!(report.stats.type_check_failed, 0);
    // All constants should be accepted (verified or translated).
    // Theorems may kernel-verify if the kernel accepts them, or fall back to
    // axiom acceptance (translated). Axioms always go through the axiom path.
    assert_eq!(
        report.stats.kernel_verified + report.stats.translated,
        1000,
        "all 1000 constants should be accepted"
    );
    // Translated count includes axioms plus any theorems that fell back to axiom path
    assert!(
        report.stats.translated >= axiom_count as u64,
        "at least {axiom_count} axioms should be translated"
    );
}

// #3561 native_gate foundational whitelist drift regression. See
// `axiom_audit::FOUNDATIONAL_AXIOMS` for the canonical list; the drifted
// `is_foundational_axiom_name` was missing Rat min/max, Fin.castSucc /
// Fin.last, Rat ring / field batches (#3551/#3555), and Nat.le_refl, while
// still containing `sorryAx` (#3554) and `Eq.symm` / `Eq.trans` / `Eq.subst`
// (#3559). Tests pin that (a) every canonical name is accepted by the gate,
// (b) names removed by #3554/#3559 are rejected, (c) no file outside
// `crates/clean-kernel/src/env/axiom_audit.rs` re-declares the const array.

use super::native_gate_helpers::is_foundational_axiom_name;
use clean_kernel::{is_foundational_axiom, Name};

/// Representative sample covering every category in the canonical list.
///
/// NOTE (#3575): Names that were promoted from `Declaration::Axiom` to
/// `Declaration::Theorem` (and thus removed from `FOUNDATIONAL_AXIOMS` per
/// the #3559 disjointness rule) have been moved to
/// `NON_FOUNDATIONAL_CANONICAL_NAMES` below. Specifically: `Rat.add_comm`
/// (#3572), `Rat.add_assoc` (#3572), `Rat.zero_add` / `Rat.add_zero` /
/// `Rat.one_mul` / `Rat.mul_one` (#3581), `Rat.mul_comm` (#3572),
/// `Rat.mul_assoc` (#3582), `Rat.inv_zero` (#3581).
const CANONICAL_FOUNDATIONAL_NAMES: &[&str] = &[
    // Propositional / logical core — the FULL canonical list as of the
    // TCB-shrink campaign: every former `Rat.*` / `Fin.*` whitelist entry
    // has been GENUINELY ELIMINATED (kernel-checked Definitions/Theorems
    // over the quotient `Rat` carrier — WS-A/WS-B atomic live switch — and
    // computable `Fin` constructors), and `instDecidableEqFin` is a
    // computable Definition (`algebra_fin_dec_eq_proof.rs`). Per the #3559
    // disjointness rule a non-axiom name must NOT stay whitelisted, so the
    // retired names live in `NON_FOUNDATIONAL_CANONICAL_NAMES` below.
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Eq.refl",
    "proofIrrel",
    "Quot",
    "Quot.mk",
    "Quot.ind",
    "Quot.lift",
    "WellFounded.fix",
    "String.decEq",
    "Char.decEq",
    // NOTE: `funext`, `Classical.em`, and `Classical.byContradiction` were
    // GENUINELY ELIMINATED from the kernel's FOUNDATIONAL_AXIOMS — they are now
    // kernel-checked `Declaration::Theorem`s (`funext` from `Quot.sound` via
    // `init_funext`; `em`/`byContradiction` from `Classical.choice`+`propext`+
    // `funext` via the DIACONESCU census in `classical_em_proof.rs`). They moved
    // to `NON_FOUNDATIONAL_CANONICAL_NAMES` below; keeping them here would violate
    // the #3559 disjointness invariant pinned by
    // `test_foundational_axioms_disjoint_from_theorems`.
    // Nat reflexivity — `Nat.le_refl` was removed from the kernel's
    // FOUNDATIONAL_AXIOMS in #3599 because it is now registered as a
    // `Declaration::Theorem` with a constructive proof term
    // (`fun n => @Nat.le.refl n`) in
    // `nat_top_level_ordering_proof::register_nat_le_refl_theorem`.
    // Keeping it here would violate the disjointness invariant pinned
    // by `test_foundational_axioms_disjoint_from_theorems`.
];

/// Names that must NOT be foundational under the canonical whitelist. The
/// drifted native-gate copy previously included `sorryAx` / `Eq.symm` /
/// `Eq.trans` / `Eq.subst`; #3554 moved `sorryAx` into `TRUST_MARKERS`, and
/// #3559 removed the three Eq.* entries because they are registered as
/// `Declaration::Theorem` with genuine kernel-checked proof terms.
///
/// NOTE (#3575): Several additional `Rat.*` names that were promoted from
/// `Declaration::Axiom` to `Declaration::Theorem` per the #3559 disjointness
/// rule have been migrated into this list: `Rat.add_comm` (#3572),
/// `Rat.add_assoc` (#3572), `Rat.zero_add` / `Rat.add_zero` / `Rat.one_mul` /
/// `Rat.mul_one` (#3581), `Rat.mul_comm` (#3572), `Rat.mul_assoc` (#3582),
/// `Rat.inv_zero` (#3581). Each is now a registered Theorem with a
/// kernel-checked proof term, so classifying them as foundational would be a
/// regression (the BFS short-circuits on `kind == Axiom`, so whitelisting a
/// Theorem silently masks a demotion). The kernel-side disjointness
/// invariant is pinned by `test_foundational_axioms_disjoint_from_theorems`
/// in `clean-kernel/src/env/tests_axiom_audit.rs`.
///
/// NOTE (#3654): `Rat.zero_mul` and `Rat.mul_zero`
/// were promoted to `Declaration::Theorem` under #3642/#3643 using the
/// `Rat.mk_eq_mk_of_cross_eq` bridge (#3585). The bridge is UNSOUND under
/// the current free-inductive Rat carrier (see the soundness note in
/// `crates/clean-kernel/src/env/algebra_field_inst.rs` Tranche C block
/// and the re-whitelist entries in
/// `crates/clean-kernel/src/env/axiom_audit.rs`). The bridge and the
/// proof modules have been deleted; those two names have moved back
/// into `CANONICAL_FOUNDATIONAL_NAMES` above. `Rat.left_distrib` remains
/// deliberately non-foundational so theorem closures like `Rat.mul_sub`
/// still expose that trust gap directly.
const NON_FOUNDATIONAL_CANONICAL_NAMES: &[&str] = &[
    "sorryAx",
    "sorry",
    "trustedArith",
    "trustedAy",
    "Eq.symm",
    "Eq.trans",
    "Eq.subst",
    // Derived theorems, NOT foundational axioms (kernel TCB-shrink): `funext` is
    // proved from `Quot.sound` (`init_funext` / `funext_proof_value`); `Classical.em`
    // and `Classical.byContradiction` are the DIACONESCU census −2 — kernel-checked
    // Theorems built in `classical_em_proof.rs`. All three were removed from the
    // kernel `FOUNDATIONAL_AXIOMS` per the #3559 disjointness rule, so the native
    // gate must reject them as foundational AXIOMS (their closures are still
    // foundational-only, but a Theorem is not an axiom).
    "funext",
    "Classical.em",
    "Classical.byContradiction",
    "Rat.add_le_add",
    "Rat.neg_le_neg",
    // Rat.* names promoted to Declaration::Theorem (#3572/#3581/#3582):
    "Rat.add_comm",
    "Rat.add_assoc",
    "Rat.add_zero",
    "Rat.zero_add",
    "Rat.mul_comm",
    "Rat.mul_assoc",
    "Rat.one_mul",
    "Rat.mul_one",
    "Rat.inv_zero",
    "Rat.left_distrib",
    // TCB-shrink: `instDecidableEqFin` is no longer an axiom — it is a
    // computable, axiom-free `Declaration::Definition`
    // (`algebra_fin_dec_eq_proof.rs`) deciding `Eq (Fin n) a b` via
    // `Nat.decEq` on `Fin.val`. Removed from the kernel's
    // `FOUNDATIONAL_AXIOMS` per the #3559 disjointness rule (whitelisting a
    // non-axiom silently masks a demotion regression), so the native gate
    // must reject the name too.
    "instDecidableEqFin",
    // TCB-shrink (WS-A atomic live switch + order/ring/min-max payoffs):
    // every remaining `Rat.*` ordering / ring / min-max whitelist entry was
    // GENUINELY ELIMINATED — kernel-checked constructive
    // Definitions/Theorems over the quotient carrier
    // (`Rat := Quot Rat.Raw.Equiv`; see `algebra_rat_quotient.rs`,
    // `algebra_rat_order_proofs.rs`, `algebra_rat_minmax_proof.rs`,
    // `algebra_rat_le_trans_proof.rs`). Whitelisting any of them again
    // would mask a demotion regression (#3559 disjointness rule).
    "Rat.le_refl",
    "Rat.le_trans",
    "Rat.le_antisymm",
    "Rat.lt_iff_le_not_le",
    "Rat.le_total",
    "Rat.add_le_add_left",
    "Rat.mul_pos",
    "Rat.zero_lt_one",
    "Rat.le_add_of_nonneg_right",
    "Rat.mul_nonneg",
    "Rat.max",
    "Rat.min",
    "Rat.max_def",
    "Rat.max_def'",
    "Rat.min_def",
    "Rat.min_def'",
    "Rat.add_left_neg",
    "Rat.add_neg_self",
    "Rat.add_right_cancel",
    "Rat.mul_neg",
    "Rat.right_distrib",
    "Rat.mul_inv_cancel",
    "Rat.zero_mul",
    "Rat.mul_zero",
    // #3470: `Fin.castSucc` / `Fin.last` are computable
    // `Declaration::Definition`s over `Fin.mk`/`Fin.val`/`Fin.rec`
    // (`nn_verify_fin_sum.rs`) — no longer axioms.
    "Fin.castSucc",
    "Fin.last",
    "my_domain_axiom",
];

/// #3561: the native gate and the kernel must agree bit-for-bit on which
/// axioms are foundational. Exercising every name surfaced by the drifted
/// copy pins single-source-of-truth — if the gate is ever re-forked with its
/// own hard-coded list, this test will catch the divergence.
#[test]
fn test_native_gate_foundational_axioms_delegates_to_canonical() {
    for &name in CANONICAL_FOUNDATIONAL_NAMES {
        let n = Name::from_string(name);
        assert!(
            is_foundational_axiom(&n),
            "{name} must be foundational in axiom_audit (canonical list)"
        );
        assert!(
            is_foundational_axiom_name(name),
            "{name} is foundational per axiom_audit but native_gate rejects \
             it — drift regression (#3561)"
        );
    }
}

/// Negative form of #3561: names removed from / never present in
/// `FOUNDATIONAL_AXIOMS` must be rejected by the native gate.
#[test]
fn test_native_gate_non_foundational_names_rejected() {
    for &name in NON_FOUNDATIONAL_CANONICAL_NAMES {
        let n = Name::from_string(name);
        assert!(
            !is_foundational_axiom(&n),
            "{name} must NOT be foundational in axiom_audit"
        );
        assert!(
            !is_foundational_axiom_name(name),
            "{name} is non-foundational per axiom_audit but native_gate \
             accepts it — drift regression (#3561)"
        );
    }
}

/// #3561: no file outside `crates/clean-kernel/src/env/axiom_audit.rs` may
/// declare a `const FOUNDATIONAL_AXIOMS` array. The three drifted copies
/// (#3560 sorry_tracer, #3561 native_gate_helpers, and the original) were
/// all hard-coded const-array forks of the canonical list. This test scans
/// the repository for any re-declaration and fails if one exists.
#[test]
fn test_no_drifted_foundational_axioms_const_array() {
    use std::path::PathBuf;

    // Walk up from CARGO_MANIFEST_DIR (crates/clean-mathverse) to the workspace
    // root, which owns the `crates/` tree. Tests must not rely on a working
    // directory — cargo sets CARGO_MANIFEST_DIR to the crate directory.
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = crate_dir
        .parent() // crates/
        .and_then(|p| p.parent()) // repo root
        .expect("CARGO_MANIFEST_DIR has a workspace-root ancestor");
    let crates_dir = workspace_root.join("crates");

    // Canonical file — must contain exactly one declaration.
    let canonical = workspace_root.join("crates/clean-kernel/src/env/axiom_audit.rs");
    assert!(
        canonical.exists(),
        "canonical FOUNDATIONAL_AXIOMS file not found: {}",
        canonical.display()
    );

    // Collect every .rs file under crates/ that declares a `const` item
    // named by the canonical symbol. To avoid matching our own prose/doc
    // references to the symbol (or this test's own source), we build the
    // search needle at runtime from fragments so the literal declaration
    // form does not appear verbatim in this file. The canonical
    // declaration is `pub(crate) const <NAME>: &[&str] = &[...]`, so the
    // tokens `const`, the name, and the `:` type annotation together are
    // both necessary and sufficient evidence of a re-declaration.
    let needle: String = {
        let mut s = String::from("const ");
        s.push_str("FOUNDATIONAL");
        s.push('_');
        s.push_str("AXIOMS");
        s.push(':');
        s
    };
    let mut offenders: Vec<PathBuf> = Vec::new();
    fn walk(dir: &Path, needle: &str, out: &mut Vec<PathBuf>) {
        let entries = match fs::read_dir(dir) {
            Ok(e) => e,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                // Skip target/ build output — cargo may mirror sources there.
                if path.file_name().is_some_and(|n| n == "target") {
                    continue;
                }
                walk(&path, needle, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                if let Ok(body) = fs::read_to_string(&path) {
                    if body.contains(needle) {
                        out.push(path);
                    }
                }
            }
        }
    }
    walk(&crates_dir, &needle, &mut offenders);

    // Normalise for comparison (Path::canonicalize follows symlinks; use
    // component-wise equality via ends_with on the suffix instead).
    let canonical_suffix = Path::new("crates/clean-kernel/src/env/axiom_audit.rs");
    offenders.retain(|p| !p.ends_with(canonical_suffix));

    assert!(
        offenders.is_empty(),
        "FOUNDATIONAL_AXIOMS const array declared outside canonical \
         `crates/clean-kernel/src/env/axiom_audit.rs` — drift regression \
         (#3561). Offenders: {offenders:?}. All call sites must delegate to \
         `clean_kernel::is_foundational_axiom`."
    );
}
