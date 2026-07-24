// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::provenance::ProvenanceSidecar;
use crate::shard::ShardReader;
use crate::types::{AxiomProfile, ImportConfidence, SourceSystem};

use clean_olean::expr::{ParsedBinderInfo, ParsedExpr};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mock_module_sb(constants: Vec<ParsedConstant>) -> ParsedModule {
    ParsedModule {
        const_names: constants.iter().map(|c| c.name.clone()).collect(),
        constants,
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

fn mock_constant_sb(name: &str, kind: ConstantKind, has_val: bool) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: Vec::new(),
        type_: None,
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

fn rich_constant_sb(
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

fn nat_const_sb() -> ParsedExpr {
    ParsedExpr::Const("Nat".to_string(), vec![])
}

fn nat_to_nat_sb() -> ParsedExpr {
    ParsedExpr::ForallE(
        "x".to_string(),
        Box::new(nat_const_sb()),
        Box::new(nat_const_sb()),
        ParsedBinderInfo::Default,
    )
}

fn nat_id_sb() -> ParsedExpr {
    ParsedExpr::Lam(
        "x".to_string(),
        Box::new(nat_const_sb()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    )
}

fn type0_sb() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))
}

// ---------------------------------------------------------------------------
// Builder construction tests
// ---------------------------------------------------------------------------

#[test]
fn test_builder_new_empty() {
    let builder = Lean4ShardBuilder::new();
    assert_eq!(builder.module_count(), 0);
    assert_eq!(builder.constant_count(), 0);
}

#[test]
fn test_builder_default() {
    let builder = Lean4ShardBuilder::default();
    assert_eq!(builder.module_count(), 0);
}

// ---------------------------------------------------------------------------
// Single module tests
// ---------------------------------------------------------------------------

#[test]
fn test_builder_add_single_module() {
    let module = mock_module_sb(vec![
        mock_constant_sb("Nat.add", ConstantKind::Definition, true),
        mock_constant_sb("propext", ConstantKind::Axiom, false),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    let stats = builder.add_module(&module, "Init.Core").unwrap();

    assert_eq!(stats.module_name, "Init.Core");
    assert_eq!(stats.total, 2);
    assert_eq!(stats.kernel_verified, 1);
    assert_eq!(stats.axiomatized, 1);
    assert_eq!(stats.definitions, 1);
    assert_eq!(stats.axioms, 1);
    assert_eq!(builder.module_count(), 1);
    assert_eq!(builder.constant_count(), 2);
}

#[test]
fn test_builder_add_empty_module() {
    let module = mock_module_sb(vec![]);
    let mut builder = Lean4ShardBuilder::new();
    let stats = builder.add_module(&module, "Empty").unwrap();

    assert_eq!(stats.total, 0);
    assert_eq!(builder.module_count(), 1);
    assert_eq!(builder.constant_count(), 0);
}

// ---------------------------------------------------------------------------
// Multi-module tests
// ---------------------------------------------------------------------------

#[test]
fn test_builder_add_multiple_modules() {
    let m1 = mock_module_sb(vec![
        rich_constant_sb(
            "Nat.add",
            ConstantKind::Definition,
            nat_to_nat_sb(),
            Some(nat_id_sb()),
        ),
        rich_constant_sb("Nat.zero", ConstantKind::Constructor, nat_const_sb(), None),
    ]);
    let m2 = mock_module_sb(vec![
        rich_constant_sb("Bool.true", ConstantKind::Constructor, type0_sb(), None),
        mock_constant_sb("Classical.choice", ConstantKind::Axiom, false),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&m1, "Init.Data.Nat").unwrap();
    builder.add_module(&m2, "Init.Data.Bool").unwrap();

    assert_eq!(builder.module_count(), 2);
    assert_eq!(builder.constant_count(), 4);
}

// ---------------------------------------------------------------------------
// Build shard tests
// ---------------------------------------------------------------------------

#[test]
fn test_builder_build_empty_shard() {
    let builder = Lean4ShardBuilder::new();
    let (buf, stats) = builder.build_shard().unwrap();

    assert_eq!(stats.total_constants, 0);
    assert_eq!(stats.total_provenance_records, 0);
    assert!(stats.modules.is_empty());
    assert!(stats.shard_size_bytes > 0); // Header + footer always present.

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_builder_build_shard_round_trip() {
    let m1 = mock_module_sb(vec![
        rich_constant_sb(
            "Nat.add",
            ConstantKind::Definition,
            nat_to_nat_sb(),
            Some(nat_id_sb()),
        ),
        mock_constant_sb("Classical.choice", ConstantKind::Axiom, false),
        rich_constant_sb("Nat", ConstantKind::Inductive, type0_sb(), None),
    ]);
    let m2 = mock_module_sb(vec![rich_constant_sb(
        "thm1",
        ConstantKind::Theorem,
        nat_to_nat_sb(),
        Some(nat_id_sb()),
    )]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&m1, "Init.Core").unwrap();
    builder.add_module(&m2, "Init.Thm").unwrap();

    let (buf, stats) = builder.build_shard().unwrap();

    assert_eq!(stats.total_constants, 4);
    assert_eq!(stats.total_kernel_verified, 3);
    assert_eq!(stats.total_axiomatized, 1);
    assert_eq!(stats.total_provenance_records, 4);
    assert_eq!(stats.modules.len(), 2);
    assert!(stats.shard_size_bytes > 0);

    // Verify shard.
    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 4);

    // Verify names.
    let names: Vec<&str> = reader
        .constants
        .iter()
        .map(|c| reader.strings[c.name_idx as usize].as_str())
        .collect();
    assert_eq!(names, vec!["Nat.add", "Classical.choice", "Nat", "thm1"]);

    // Verify source system.
    for c in &reader.constants {
        assert_eq!(c.source_system, SourceSystem::Lean4 as u8);
    }

    // Honesty contract: the builder runs the un-typechecked heuristic path
    // (no OUR-kernel check), so it must NEVER stamp KernelVerified. A
    // definition/theorem/inductive with structure is at most SourceVerified;
    // an axiom-without-value is Axiomatized.
    let conf = |i: usize| reader.constants[i].import_confidence;
    assert_eq!(conf(0), ImportConfidence::SourceVerified as u8, "Nat.add");
    assert_eq!(
        conf(1),
        ImportConfidence::Axiomatized as u8,
        "Classical.choice"
    );
    assert_eq!(conf(2), ImportConfidence::SourceVerified as u8, "Nat");
    assert_eq!(conf(3), ImportConfidence::SourceVerified as u8, "thm1");
    for c in &reader.constants {
        assert_ne!(
            c.import_confidence,
            ImportConfidence::KernelVerified as u8,
            "heuristic shard builder must never stamp KernelVerified without an OUR-kernel check"
        );
    }

    // Verify axiom profile for Classical.choice.
    let choice = &reader.constants[1];
    assert!(choice.profile().has(AxiomProfile::CHOICE));
    assert!(choice.profile().has(AxiomProfile::AXIOMATIZED));
    assert!(choice.is_trust_gated());

    // Verify name lookup.
    assert!(reader.lookup_name("Nat.add").is_some());
    assert!(reader.lookup_name("Classical.choice").is_some());
    assert!(reader.lookup_name("Nonexistent").is_none());
}

// ---------------------------------------------------------------------------
// Provenance tests
// ---------------------------------------------------------------------------

#[test]
fn test_builder_provenance_records() {
    let module = mock_module_sb(vec![
        mock_constant_sb("A.thm", ConstantKind::Theorem, true),
        mock_constant_sb("B.def", ConstantKind::Definition, true),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Mathlib.Topology").unwrap();
    let (buf, _stats) = builder.build_shard().unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();

    // Verify provenance sidecar is populated.
    assert!(!reader.provenance.is_empty());
    let sidecar = ProvenanceSidecar::from_bytes(&reader.provenance).unwrap();
    assert_eq!(sidecar.len(), 2);

    // Verify module path.
    let rec0 = sidecar.get(0).unwrap();
    assert_eq!(rec0.original_name, "A.thm");
    assert_eq!(rec0.module_path.as_deref(), Some("Mathlib.Topology"));
    assert!(rec0.import_timestamp > 0);

    let rec1 = sidecar.get(1).unwrap();
    assert_eq!(rec1.original_name, "B.def");
    assert_eq!(rec1.module_path.as_deref(), Some("Mathlib.Topology"));

    // Verify sidecar digests match.
    for c in &reader.constants {
        assert!(
            sidecar.verify_digest(c),
            "sidecar digest mismatch for constant at name_idx {}",
            c.name_idx
        );
    }
}

// ---------------------------------------------------------------------------
// Module statistics tests
// ---------------------------------------------------------------------------

#[test]
fn test_module_stats_kind_breakdown() {
    let module = mock_module_sb(vec![
        mock_constant_sb("thm1", ConstantKind::Theorem, true),
        mock_constant_sb("thm2", ConstantKind::Theorem, true),
        mock_constant_sb("def1", ConstantKind::Definition, true),
        mock_constant_sb("ind1", ConstantKind::Inductive, false),
        mock_constant_sb("ax1", ConstantKind::Axiom, false),
        mock_constant_sb("ax2", ConstantKind::Axiom, false),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    let stats = builder.add_module(&module, "Test").unwrap();

    assert_eq!(stats.theorems, 2);
    assert_eq!(stats.definitions, 1);
    assert_eq!(stats.inductives, 1);
    assert_eq!(stats.axioms, 2);
    assert_eq!(stats.total, 6);
    assert_eq!(stats.kernel_verified, 4); // 2 theorems + 1 def + 1 inductive
    assert_eq!(stats.axiomatized, 2); // 2 axioms
}

// ---------------------------------------------------------------------------
// Constant count matches input (acceptance criterion)
// ---------------------------------------------------------------------------

#[test]
fn test_builder_constant_count_matches_input() {
    let n_theorems = 37;
    let n_defs = 15;
    let n_axioms = 3;
    let n_inductives = 5;

    let mut constants = Vec::new();
    for i in 0..n_theorems {
        constants.push(rich_constant_sb(
            &format!("Thm.t{i}"),
            ConstantKind::Theorem,
            nat_to_nat_sb(),
            Some(nat_id_sb()),
        ));
    }
    for i in 0..n_defs {
        constants.push(rich_constant_sb(
            &format!("Def.d{i}"),
            ConstantKind::Definition,
            nat_to_nat_sb(),
            Some(nat_id_sb()),
        ));
    }
    for i in 0..n_axioms {
        constants.push(mock_constant_sb(
            &format!("Ax.a{i}"),
            ConstantKind::Axiom,
            false,
        ));
    }
    for i in 0..n_inductives {
        constants.push(rich_constant_sb(
            &format!("Ind.i{i}"),
            ConstantKind::Inductive,
            type0_sb(),
            None,
        ));
    }
    let total_input = constants.len();
    let module = mock_module_sb(constants);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "TestModule").unwrap();
    let (buf, stats) = builder.build_shard().unwrap();

    assert_eq!(
        stats.total_constants as usize, total_input,
        "Constant count must match .olean source"
    );

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(
        reader.header.constant_count as usize, total_input,
        "Shard constant count must match .olean source"
    );
}

// ---------------------------------------------------------------------------
// Has-value classification
// ---------------------------------------------------------------------------

#[test]
fn test_builder_has_value_classification() {
    let module = mock_module_sb(vec![
        rich_constant_sb(
            "thm_with_proof",
            ConstantKind::Theorem,
            type0_sb(),
            Some(nat_id_sb()),
        ),
        mock_constant_sb("thm_no_proof", ConstantKind::Theorem, false),
        rich_constant_sb(
            "def_with_val",
            ConstantKind::Definition,
            nat_to_nat_sb(),
            Some(nat_id_sb()),
        ),
        mock_constant_sb("axiom1", ConstantKind::Axiom, false),
        mock_constant_sb("ind1", ConstantKind::Inductive, false),
        mock_constant_sb("ctor1", ConstantKind::Constructor, false),
        mock_constant_sb("rec1", ConstantKind::Recursor, false),
        mock_constant_sb("quot1", ConstantKind::Quot, false),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Test").unwrap();
    let (buf, _) = builder.build_shard().unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    assert!(reader.constants[0].has_value()); // Theorem with proof
    assert!(!reader.constants[1].has_value()); // Theorem without proof
    assert!(reader.constants[2].has_value()); // Definition with value
    assert!(!reader.constants[3].has_value()); // Axiom
    assert!(reader.constants[4].has_value()); // Inductive (placeholder)
    assert!(reader.constants[5].has_value()); // Constructor (placeholder)
    assert!(reader.constants[6].has_value()); // Recursor (placeholder)
    assert!(reader.constants[7].has_value()); // Quot (placeholder)
}

// ---------------------------------------------------------------------------
// ShardBuildStats aggregation
// ---------------------------------------------------------------------------

#[test]
fn test_builder_stats_aggregate_across_modules() {
    let m1 = mock_module_sb(vec![
        mock_constant_sb("a", ConstantKind::Theorem, true),
        mock_constant_sb("b", ConstantKind::Axiom, false),
    ]);
    let m2 = mock_module_sb(vec![
        mock_constant_sb("c", ConstantKind::Definition, true),
        mock_constant_sb("d", ConstantKind::Theorem, true),
        mock_constant_sb("e", ConstantKind::Opaque, false),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&m1, "M1").unwrap();
    builder.add_module(&m2, "M2").unwrap();
    let (_buf, stats) = builder.build_shard().unwrap();

    assert_eq!(stats.total_constants, 5);
    assert_eq!(stats.total_kernel_verified, 3); // a, c, d
    assert_eq!(stats.total_axiomatized, 2); // b, e
    assert_eq!(stats.modules.len(), 2);
    assert_eq!(stats.modules[0].module_name, "M1");
    assert_eq!(stats.modules[0].total, 2);
    assert_eq!(stats.modules[1].module_name, "M2");
    assert_eq!(stats.modules[1].total, 3);
}

// ---------------------------------------------------------------------------
// Level params preservation tests (#3413)
// ---------------------------------------------------------------------------

/// Helper: create a constant with specific level_params.
fn mock_constant_with_levels(
    name: &str,
    kind: ConstantKind,
    has_val: bool,
    level_params: Vec<&str>,
) -> ParsedConstant {
    ParsedConstant {
        definition_safety: None,
        quot_kind: None,
        name: name.to_string(),
        kind,
        level_params: level_params.into_iter().map(String::from).collect(),
        type_: None,
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
fn test_shard_builder_preserves_single_level_param() {
    let module = mock_module_sb(vec![mock_constant_with_levels(
        "List.map",
        ConstantKind::Definition,
        true,
        vec!["u"],
    )]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Init.Data.List").unwrap();
    let (buf, _stats) = builder.build_shard().unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.constants.len(), 1);
    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 1);
    assert!(c.has_level_params());
    let lp_name = &reader.strings[c.level_params_start as usize];
    assert_eq!(lp_name, "u");
}

#[test]
fn test_shard_builder_preserves_multiple_level_params() {
    let module = mock_module_sb(vec![mock_constant_with_levels(
        "List.map",
        ConstantKind::Definition,
        true,
        vec!["u", "v"],
    )]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Init.Data.List").unwrap();
    let (buf, _stats) = builder.build_shard().unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 2);
    let start = c.level_params_start as usize;
    assert_eq!(&reader.strings[start], "u");
    assert_eq!(&reader.strings[start + 1], "v");
}

#[test]
fn test_shard_builder_zero_level_params_when_empty() {
    let module = mock_module_sb(vec![mock_constant_sb(
        "Nat.add",
        ConstantKind::Definition,
        true,
    )]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Init.Core").unwrap();
    let (buf, _stats) = builder.build_shard().unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 0);
    assert!(!c.has_level_params());
}

#[test]
fn test_shard_builder_level_params_mixed_constants() {
    // One with level params, one without — both in same module.
    let module = mock_module_sb(vec![
        mock_constant_with_levels("List.map", ConstantKind::Definition, true, vec!["u", "v"]),
        mock_constant_sb("Nat.add", ConstantKind::Definition, true),
        mock_constant_with_levels("Option.map", ConstantKind::Definition, true, vec!["w"]),
    ]);

    let mut builder = Lean4ShardBuilder::new();
    builder.add_module(&module, "Init").unwrap();
    let (buf, _stats) = builder.build_shard().unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.constants.len(), 3);

    // List.map: 2 level params [u, v]
    let c0 = &reader.constants[0];
    assert_eq!(c0.level_params_count, 2);
    assert_eq!(&reader.strings[c0.level_params_start as usize], "u");
    assert_eq!(&reader.strings[c0.level_params_start as usize + 1], "v");

    // Nat.add: 0 level params
    let c1 = &reader.constants[1];
    assert_eq!(c1.level_params_count, 0);

    // Option.map: 1 level param [w]
    let c2 = &reader.constants[2];
    assert_eq!(c2.level_params_count, 1);
    assert_eq!(&reader.strings[c2.level_params_start as usize], "w");
}
