// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the batch `.olean` import pipeline.

use std::path::{Path, PathBuf};

use clean_olean::expr::{BigNat, ParsedBinderInfo, ParsedExpr, ParsedLiteral};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

use super::*;
use crate::lean4::olean::alpha::{import_module, ImportStats};
use crate::shard::{ShardReader, ShardWriter};

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

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

fn rich_constant(
    name: &str,
    kind: ConstantKind,
    type_expr: ParsedExpr,
    value_expr: Option<ParsedExpr>,
) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: Some(type_expr),
        value: value_expr,
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
    }
}

fn prop() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Zero)
}

fn type0() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))
}

fn nat_const() -> ParsedExpr {
    ParsedExpr::Const("Nat".to_string(), vec![])
}

fn nat_to_nat() -> ParsedExpr {
    ParsedExpr::ForallE(
        "x".to_string(),
        Box::new(nat_const()),
        Box::new(nat_const()),
        ParsedBinderInfo::Default,
    )
}

fn nat_to_prop() -> ParsedExpr {
    ParsedExpr::ForallE(
        "x".to_string(),
        Box::new(nat_const()),
        Box::new(prop()),
        ParsedBinderInfo::Default,
    )
}

fn nat_id() -> ParsedExpr {
    ParsedExpr::Lam(
        "x".to_string(),
        Box::new(nat_const()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    )
}

// ---------------------------------------------------------------------------
// Constant batch builders
// ---------------------------------------------------------------------------

/// Build `n` constants of the given kind with a naming suffix.
fn make_batch(
    prefix: &str,
    suffix: &str,
    n: usize,
    kind: ConstantKind,
    ty: fn() -> ParsedExpr,
    val: Option<fn() -> ParsedExpr>,
) -> Vec<ParsedConstant> {
    (0..n)
        .map(|i| {
            rich_constant(
                &format!("{prefix}.{suffix}_{i}"),
                kind.clone(),
                ty(),
                val.map(|f| f()),
            )
        })
        .collect()
}

fn make_let_lit_defs(prefix: &str, n: usize) -> Vec<ParsedConstant> {
    (0..n)
        .map(|i| {
            let val = ParsedExpr::LetE(
                "x".into(),
                Box::new(nat_const()),
                Box::new(ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(
                    i as u64,
                )))),
                Box::new(ParsedExpr::BVar(0)),
                false,
            );
            rich_constant(
                &format!("{prefix}.letlit_{i}"),
                ConstantKind::Definition,
                nat_to_nat(),
                Some(val),
            )
        })
        .collect()
}

fn import_and_read(module: &ParsedModule) -> (ImportStats, Vec<u8>) {
    let mut writer = ShardWriter::new();
    let stats = import_module(module, &mut writer).expect("import_module failed");
    let mut buf = Vec::new();
    writer.write(&mut buf).expect("shard write failed");
    (stats, buf)
}

// ---------------------------------------------------------------------------
// Config tests
// ---------------------------------------------------------------------------

#[test]
fn test_batch_config_builder() {
    let cfg = Lean4BatchConfig::new(PathBuf::from("/tmp/lean"))
        .with_max_per_shard(1000)
        .with_deps()
        .with_filter(vec!["Init".to_string(), "Mathlib".to_string()]);

    assert_eq!(cfg.olean_root, PathBuf::from("/tmp/lean"));
    assert_eq!(cfg.max_constants_per_shard, 1000);
    assert!(cfg.extract_deps);
    assert_eq!(
        cfg.module_filter.as_deref(),
        Some(&["Init".to_string(), "Mathlib".to_string()][..])
    );
}

#[test]
fn test_batch_config_defaults() {
    let cfg = Lean4BatchConfig::new(PathBuf::from("/tmp"));
    assert_eq!(cfg.max_constants_per_shard, 50_000);
    assert!(!cfg.extract_deps);
    assert!(cfg.module_filter.is_none());
}

// ---------------------------------------------------------------------------
// path_to_module_name tests
// ---------------------------------------------------------------------------

#[test]
fn test_path_to_module_name_basic() {
    let root = Path::new("./.elan/lib/lean");
    let path = Path::new("./.elan/lib/lean/Init/Data/Nat/Basic.olean");
    assert_eq!(path_to_module_name(path, root), "Init.Data.Nat.Basic");
}

#[test]
fn test_path_to_module_name_top_level() {
    let root = Path::new("/lib");
    let path = Path::new("/lib/Prelude.olean");
    assert_eq!(path_to_module_name(path, root), "Prelude");
}

#[test]
fn test_path_to_module_name_no_match() {
    let root = Path::new("/other");
    let path = Path::new("/lib/Init/Core.olean");
    let name = path_to_module_name(path, root);
    assert!(
        name.contains("Init.Core"),
        "expected module name containing Init.Core, got: {name}"
    );
}

#[test]
fn test_path_to_module_name_deep_nesting() {
    let root = Path::new("/r");
    let path = Path::new("/r/A/B/C/D/E.olean");
    assert_eq!(path_to_module_name(path, root), "A.B.C.D.E");
}

// ---------------------------------------------------------------------------
// Large module import (100+ constants)
// ---------------------------------------------------------------------------

#[test]
fn test_large_module_import() {
    let mut constants = Vec::new();
    constants.extend(make_batch(
        "T",
        "thm",
        30,
        ConstantKind::Theorem,
        nat_to_prop,
        Some(nat_id),
    ));
    constants.extend(make_batch(
        "D",
        "def",
        20,
        ConstantKind::Definition,
        nat_to_nat,
        Some(nat_id),
    ));
    constants.extend(make_batch(
        "I",
        "Ind",
        10,
        ConstantKind::Inductive,
        type0,
        None,
    ));
    constants.extend(make_batch(
        "C",
        "ctor",
        10,
        ConstantKind::Constructor,
        nat_const,
        None,
    ));
    constants.extend(make_batch(
        "R",
        "rec",
        10,
        ConstantKind::Recursor,
        nat_to_nat,
        None,
    ));
    constants.extend(make_batch("A", "ax", 5, ConstantKind::Axiom, type0, None));
    constants.extend(make_batch(
        "O",
        "opaque",
        5,
        ConstantKind::Opaque,
        type0,
        None,
    ));
    constants.extend(make_batch("Q", "quot", 5, ConstantKind::Quot, type0, None));
    constants.extend(make_let_lit_defs("L", 5));
    assert_eq!(constants.len(), 100);

    let module = mock_module(constants);
    let (stats, buf) = import_and_read(&module);

    assert_eq!(stats.total, 100);
    // 30 thm + 20 def + 10 ind + 10 ctor + 10 rec + 5 quot + 5 letlit = 90
    assert_eq!(stats.kernel_verified, 90);
    // 5 axiom + 5 opaque = 10
    assert_eq!(stats.axiomatized, 10);
    assert_eq!(stats.skipped, 0);

    let reader = ShardReader::from_bytes(&buf).expect("shard read failed");
    assert_eq!(reader.header.constant_count, 100);
    assert_eq!(reader.constants.len(), 100);

    let name_at = |idx: usize| reader.strings[reader.constants[idx].name_idx as usize].as_str();
    assert_eq!(name_at(0), "T.thm_0");
    assert_eq!(name_at(30), "D.def_0");
    assert_eq!(name_at(50), "I.Ind_0");
    assert_eq!(name_at(60), "C.ctor_0");
    assert_eq!(name_at(70), "R.rec_0");
    assert_eq!(name_at(80), "A.ax_0");
    assert_eq!(name_at(85), "O.opaque_0");
    assert_eq!(name_at(90), "Q.quot_0");
    assert_eq!(name_at(95), "L.letlit_0");

    let ec = reader.header.expr_count;
    for (i, c) in reader.constants.iter().enumerate() {
        assert!(
            c.type_idx < ec,
            "constant {i} type_idx {} out of bounds (expr_count={ec})",
            c.type_idx,
        );
    }

    for c in &reader.constants {
        assert_eq!(c.source_system, crate::types::SourceSystem::Lean4 as u8);
    }
}

// ---------------------------------------------------------------------------
// Shard splitting
// ---------------------------------------------------------------------------

#[test]
fn test_shard_splitting() {
    let dir = tempfile::tempdir().expect("tempdir");
    let output_dir = dir.path().join("shards");
    std::fs::create_dir_all(&output_dir).unwrap();

    let mut writer = ShardWriter::new();
    let mut shard_constants: u32 = 0;
    let mut shard_paths: Vec<PathBuf> = Vec::new();
    let mut shard_idx: u32 = 0;
    let max_per_shard: u32 = 15;

    for batch in 0..3 {
        let constants = make_batch(
            &format!("Batch{batch}"),
            "thm",
            10,
            ConstantKind::Theorem,
            nat_to_prop,
            Some(nat_id),
        );
        let module = mock_module(constants);
        let stats = import_module(&module, &mut writer).expect("import failed");
        shard_constants += stats.total;

        if shard_constants >= max_per_shard {
            let p = output_dir.join(format!("shard_{shard_idx:04}.mathverse"));
            writer.write_to_file(&p).expect("write failed");
            shard_paths.push(p);
            writer = ShardWriter::new();
            shard_constants = 0;
            shard_idx += 1;
        }
    }
    if shard_constants > 0 {
        let p = output_dir.join(format!("shard_{shard_idx:04}.mathverse"));
        writer.write_to_file(&p).expect("write failed");
        shard_paths.push(p);
    }

    assert_eq!(shard_paths.len(), 2);

    let r0 = ShardReader::from_bytes(&std::fs::read(&shard_paths[0]).unwrap()).unwrap();
    assert_eq!(r0.header.constant_count, 20);

    let r1 = ShardReader::from_bytes(&std::fs::read(&shard_paths[1]).unwrap()).unwrap();
    assert_eq!(r1.header.constant_count, 10);
}

// ---------------------------------------------------------------------------
// Module filter
// ---------------------------------------------------------------------------

#[test]
fn test_module_filter() {
    let dir = tempfile::tempdir().expect("tempdir");
    let root = dir.path();

    for (sub, file) in [
        ("Init/Data", "Nat.olean"),
        ("Mathlib/Algebra", "Group.olean"),
        ("Other", "Foo.olean"),
    ] {
        let d = root.join(sub);
        std::fs::create_dir_all(&d).unwrap();
        std::fs::write(d.join(file), b"").unwrap();
    }

    let all = Lean4BatchImporter::new(Lean4BatchConfig::new(root.to_path_buf()))
        .discover_files()
        .unwrap();
    assert_eq!(all.len(), 3);

    let init = Lean4BatchImporter::new(
        Lean4BatchConfig::new(root.to_path_buf()).with_filter(vec!["Init".into()]),
    )
    .discover_files()
    .unwrap();
    assert_eq!(init.len(), 1);
    assert!(path_to_module_name(&init[0], root).starts_with("Init"));

    let both = Lean4BatchImporter::new(
        Lean4BatchConfig::new(root.to_path_buf())
            .with_filter(vec!["Init".into(), "Mathlib".into()]),
    )
    .discover_files()
    .unwrap();
    assert_eq!(both.len(), 2);
}

// ---------------------------------------------------------------------------
// Aggregate statistics
// ---------------------------------------------------------------------------

#[test]
fn test_aggregate_statistics() {
    let mut r = BatchImportResult::default();
    r.accum(&ImportStats {
        total: 10,
        kernel_verified: 8,
        kernel_verified_from_tc: 0,
        axiomatized: 2,
        skipped: 0,
    });
    r.accum(&ImportStats {
        total: 5,
        kernel_verified: 3,
        kernel_verified_from_tc: 0,
        axiomatized: 1,
        skipped: 1,
    });
    assert_eq!(r.total_constants, 15);
    assert_eq!(r.total_kernel_verified, 11);
    assert_eq!(r.total_axiomatized, 3);
    assert_eq!(r.total_skipped, 1);
}
