// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::provenance::ProvenanceSidecar;
use crate::shard::ShardReader;
use crate::types::{AxiomProfile, SourceSystem};

use clean_olean::expr::{ParsedBinderInfo, ParsedExpr};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

// --- Helpers ---

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

fn mock_constant(name: &str, kind: ConstantKind, has_val: bool) -> ParsedConstant {
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

fn nat_id() -> ParsedExpr {
    ParsedExpr::Lam(
        "x".to_string(),
        Box::new(nat_const()),
        Box::new(ParsedExpr::BVar(0)),
        ParsedBinderInfo::Default,
    )
}

fn type0() -> ParsedExpr {
    ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)))
}

// --- Tests ---

#[test]
fn test_lean4_import_module_with_provenance_basic() {
    let constants = vec![
        mock_constant("Nat.add", ConstantKind::Definition, true),
        mock_constant("propext", ConstantKind::Axiom, false),
    ];
    let module = mock_module(constants);
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();

    let stats =
        import_module_with_provenance(&module, &mut writer, &mut sidecar, Some("Init.Core"))
            .unwrap();

    assert_eq!(stats.total, 2);
    assert_eq!(stats.kernel_verified, 1);
    assert_eq!(stats.axiomatized, 1);
    assert_eq!(sidecar.len(), 2);

    // Verify provenance records.
    let rec0 = sidecar.get(0).unwrap();
    assert_eq!(rec0.original_name, "Nat.add");
    assert_eq!(rec0.module_path.as_deref(), Some("Init.Core"));
    assert!(rec0.import_timestamp > 0);

    let rec1 = sidecar.get(1).unwrap();
    assert_eq!(rec1.original_name, "propext");
}

#[test]
fn test_lean4_import_module_with_provenance_sidecar_digest() {
    let constants = vec![mock_constant("test.thm", ConstantKind::Theorem, true)];
    let module = mock_module(constants);
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();

    import_module_with_provenance(&module, &mut writer, &mut sidecar, None).unwrap();

    // Write shard and verify sidecar digest wiring.
    let prov_bytes = sidecar.to_bytes().unwrap();
    writer.set_provenance(prov_bytes);

    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    assert_eq!(reader.header.constant_count, 1);
    let c0 = &reader.constants[0];
    // Digest should be non-zero (computed from provenance record).
    assert_ne!(c0.sidecar_digest, 0, "sidecar_digest should be set");
    assert_eq!(c0.provenance_idx, 0);

    // Verify digest matches the sidecar.
    let sidecar_restored = ProvenanceSidecar::from_bytes(&reader.provenance).unwrap();
    assert!(
        sidecar_restored.verify_digest(c0),
        "sidecar_digest should match provenance record"
    );
}

#[test]
fn test_lean4_convert_modules_to_mathverse() {
    let module1 = mock_module(vec![
        rich_constant(
            "Nat.add",
            ConstantKind::Definition,
            nat_to_nat(),
            Some(nat_id()),
        ),
        rich_constant("Nat.zero", ConstantKind::Constructor, nat_const(), None),
    ]);
    let module2 = mock_module(vec![
        rich_constant("Bool.true", ConstantKind::Constructor, type0(), None),
        rich_constant("Classical.choice", ConstantKind::Axiom, type0(), None),
    ]);

    let modules: Vec<(&str, &ParsedModule)> =
        vec![("Init.Data.Nat", &module1), ("Init.Data.Bool", &module2)];

    let (buf, result) = convert_modules_to_mathverse(&modules).unwrap();

    assert_eq!(result.total_constants, 4);
    assert_eq!(result.kernel_verified, 3);
    assert_eq!(result.axiomatized, 1);
    assert_eq!(result.provenance_records, 4);
    assert_eq!(result.modules, vec!["Init.Data.Nat", "Init.Data.Bool"]);
    assert!(result.failures.is_empty());

    // Verify the shard.
    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 4);

    // Check that all constants are Lean4 source.
    for c in &reader.constants {
        assert_eq!(c.source_system, SourceSystem::Lean4 as u8);
    }

    // Check names.
    let names: Vec<&str> = reader
        .constants
        .iter()
        .map(|c| reader.strings[c.name_idx as usize].as_str())
        .collect();
    assert_eq!(
        names,
        vec!["Nat.add", "Nat.zero", "Bool.true", "Classical.choice"]
    );

    // Verify axiom profile for Classical.choice.
    let choice = &reader.constants[3];
    assert!(choice.profile().has(AxiomProfile::CHOICE));
    assert!(choice.profile().has(AxiomProfile::AXIOMATIZED));
    assert!(choice.is_trust_gated());

    // Verify name lookup works.
    assert!(reader.lookup_name("Nat.add").is_some());
    assert!(reader.lookup_name("Classical.choice").is_some());
    assert!(reader.lookup_name("Nonexistent").is_none());

    // Verify provenance sidecar is populated.
    assert!(!reader.provenance.is_empty());
    let sidecar = ProvenanceSidecar::from_bytes(&reader.provenance).unwrap();
    assert_eq!(sidecar.len(), 4);

    // Verify sidecar digests.
    for c in &reader.constants {
        assert!(
            sidecar.verify_digest(c),
            "sidecar digest mismatch for constant at name_idx {}",
            c.name_idx
        );
    }
}

#[test]
fn test_lean4_convert_modules_empty() {
    let modules: Vec<(&str, &ParsedModule)> = vec![];
    let (buf, result) = convert_modules_to_mathverse(&modules).unwrap();

    assert_eq!(result.total_constants, 0);
    assert_eq!(result.provenance_records, 0);
    assert!(result.modules.is_empty());

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(reader.header.constant_count, 0);
}

#[test]
fn test_lean4_convert_result_accum() {
    let mut r = ConvertResult::default();
    r.accum_stats(&ImportStats {
        total: 10,
        kernel_verified: 8,
        axiomatized: 2,
        skipped: 0,
        kernel_verified_from_tc: 0,
    });
    r.accum_stats(&ImportStats {
        total: 5,
        kernel_verified: 3,
        axiomatized: 1,
        skipped: 1,
        kernel_verified_from_tc: 0,
    });
    assert_eq!(r.total_constants, 15);
    assert_eq!(r.kernel_verified, 11);
    assert_eq!(r.axiomatized, 3);
    assert_eq!(r.skipped, 1);
}

#[test]
fn test_lean4_convert_olean_dir_nonexistent() {
    let dir = std::path::PathBuf::from("/nonexistent/olean/dir");
    let out = std::path::PathBuf::from("/tmp/test_nonexistent.mathverse");
    let err = convert_olean_dir_to_mathverse(&dir, &out, None).unwrap_err();
    assert!(
        err.to_string().contains("not found"),
        "expected 'not found' error, got: {err}"
    );
}

#[test]
fn test_lean4_convert_olean_dir_empty() {
    let dir = tempfile::tempdir().unwrap();
    let out = dir.path().join("empty.mathverse");
    let result = convert_olean_dir_to_mathverse(dir.path(), &out, None).unwrap();
    assert_eq!(result.total_constants, 0);
    assert!(result.modules.is_empty());
    // Output file should not be created for 0 constants (write_to_file
    // writes an empty shard which is valid).
}

#[test]
fn test_lean4_axiom_profile_propagation_through_bridge() {
    // Verify that axiom profiles computed by the bridge match lean4_alpha.
    let constants = vec![
        mock_constant("Classical.choice", ConstantKind::Axiom, false),
        mock_constant("propext", ConstantKind::Axiom, false),
        mock_constant("Quot", ConstantKind::Quot, false),
        mock_constant("Quot.mk", ConstantKind::Quot, false),
        mock_constant("Nat.add", ConstantKind::Definition, true),
        mock_constant("SomeOpaque", ConstantKind::Opaque, false),
    ];
    let module = mock_module(constants);
    let modules: Vec<(&str, &ParsedModule)> = vec![("Init", &module)];

    let (buf, result) = convert_modules_to_mathverse(&modules).unwrap();
    assert_eq!(result.total_constants, 6);

    let reader = ShardReader::from_bytes(&buf).unwrap();
    let name_at = |i: usize| reader.strings[reader.constants[i].name_idx as usize].as_str();
    let prof_at = |i: usize| reader.constants[i].profile();

    // Classical.choice: CHOICE | CLASSICAL | AXIOMATIZED
    assert_eq!(name_at(0), "Classical.choice");
    assert!(prof_at(0).has(AxiomProfile::CHOICE));
    assert!(prof_at(0).has(AxiomProfile::CLASSICAL));
    assert!(prof_at(0).has(AxiomProfile::AXIOMATIZED));

    // propext: PROP_EXT | AXIOMATIZED
    assert_eq!(name_at(1), "propext");
    assert!(prof_at(1).has(AxiomProfile::PROP_EXT));
    assert!(prof_at(1).has(AxiomProfile::AXIOMATIZED));

    // Quot: QUOT only (no AXIOMATIZED since ConstantKind::Quot)
    assert_eq!(name_at(2), "Quot");
    assert!(prof_at(2).has(AxiomProfile::QUOT));
    assert!(!prof_at(2).has(AxiomProfile::AXIOMATIZED));

    // Quot.mk: QUOT only
    assert_eq!(name_at(3), "Quot.mk");
    assert!(prof_at(3).has(AxiomProfile::QUOT));

    // Nat.add: pure (no axiom bits)
    assert_eq!(name_at(4), "Nat.add");
    assert!(prof_at(4).is_pure());

    // SomeOpaque: AXIOMATIZED
    assert_eq!(name_at(5), "SomeOpaque");
    assert!(prof_at(5).has(AxiomProfile::AXIOMATIZED));
    assert!(prof_at(5).is_trust_gated());
}

#[test]
fn test_lean4_provenance_module_path_propagation() {
    let module = mock_module(vec![
        mock_constant("A.thm", ConstantKind::Theorem, true),
        mock_constant("B.thm", ConstantKind::Theorem, true),
    ]);

    let modules: Vec<(&str, &ParsedModule)> = vec![("Mathlib.Topology", &module)];
    let (buf, _) = convert_modules_to_mathverse(&modules).unwrap();

    let reader = ShardReader::from_bytes(&buf).unwrap();
    let sidecar = ProvenanceSidecar::from_bytes(&reader.provenance).unwrap();

    for i in 0..2u32 {
        let rec = sidecar.get(i).unwrap();
        assert_eq!(
            rec.module_path.as_deref(),
            Some("Mathlib.Topology"),
            "constant {i} should have module_path set"
        );
    }
}

#[test]
fn test_lean4_shard_name_lookup_across_modules() {
    // Two modules with distinct constants — verify lookup works for all.
    let m1 = mock_module(vec![
        mock_constant("Init.Core.id", ConstantKind::Definition, true),
        mock_constant("Init.Core.const", ConstantKind::Definition, true),
    ]);
    let m2 = mock_module(vec![
        mock_constant("Init.Data.Nat.add", ConstantKind::Definition, true),
        mock_constant("Init.Data.Nat.mul", ConstantKind::Definition, true),
    ]);

    let modules: Vec<(&str, &ParsedModule)> = vec![("Init.Core", &m1), ("Init.Data.Nat", &m2)];

    let (buf, result) = convert_modules_to_mathverse(&modules).unwrap();
    assert_eq!(result.total_constants, 4);

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert!(reader.lookup_name("Init.Core.id").is_some());
    assert!(reader.lookup_name("Init.Core.const").is_some());
    assert!(reader.lookup_name("Init.Data.Nat.add").is_some());
    assert!(reader.lookup_name("Init.Data.Nat.mul").is_some());
    assert!(reader.lookup_name("Init.Data.Nat.sub").is_none());
}

#[test]
fn test_lean4_theorem_count_matches_input() {
    // This is the acceptance criterion: "Theorem count matches .olean source"
    let n_theorems = 37;
    let n_defs = 15;
    let n_axioms = 3;
    let n_inductives = 5;

    let mut constants = Vec::new();
    for i in 0..n_theorems {
        constants.push(rich_constant(
            &format!("Thm.t{i}"),
            ConstantKind::Theorem,
            nat_to_nat(),
            Some(nat_id()),
        ));
    }
    for i in 0..n_defs {
        constants.push(rich_constant(
            &format!("Def.d{i}"),
            ConstantKind::Definition,
            nat_to_nat(),
            Some(nat_id()),
        ));
    }
    for i in 0..n_axioms {
        constants.push(mock_constant(
            &format!("Ax.a{i}"),
            ConstantKind::Axiom,
            false,
        ));
    }
    for i in 0..n_inductives {
        constants.push(rich_constant(
            &format!("Ind.i{i}"),
            ConstantKind::Inductive,
            type0(),
            None,
        ));
    }
    let total_input = constants.len();
    let module = mock_module(constants);

    let modules: Vec<(&str, &ParsedModule)> = vec![("TestModule", &module)];
    let (buf, result) = convert_modules_to_mathverse(&modules).unwrap();

    // Key acceptance criterion: total constants match input.
    assert_eq!(
        result.total_constants as usize, total_input,
        "Constant count must match .olean source"
    );

    let reader = ShardReader::from_bytes(&buf).unwrap();
    assert_eq!(
        reader.header.constant_count as usize, total_input,
        "Shard constant count must match .olean source"
    );

    // Verify breakdown.
    assert_eq!(
        result.kernel_verified,
        (n_theorems + n_defs + n_inductives) as u32
    );
    assert_eq!(result.axiomatized, n_axioms as u32);
}

#[test]
fn test_lean4_has_value_classification() {
    // Verify value/no-value classification through the bridge.
    let module = mock_module(vec![
        rich_constant(
            "thm_with_proof",
            ConstantKind::Theorem,
            type0(),
            Some(nat_id()),
        ),
        mock_constant("thm_no_proof", ConstantKind::Theorem, false),
        rich_constant(
            "def_with_val",
            ConstantKind::Definition,
            nat_to_nat(),
            Some(nat_id()),
        ),
        mock_constant("def_no_val", ConstantKind::Definition, false),
        mock_constant("axiom1", ConstantKind::Axiom, false),
        mock_constant("opaque1", ConstantKind::Opaque, false),
        mock_constant("ind1", ConstantKind::Inductive, false),
        mock_constant("ctor1", ConstantKind::Constructor, false),
        mock_constant("rec1", ConstantKind::Recursor, false),
        mock_constant("quot1", ConstantKind::Quot, false),
    ]);

    let modules: Vec<(&str, &ParsedModule)> = vec![("Test", &module)];
    let (buf, _) = convert_modules_to_mathverse(&modules).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let name_at = |i: usize| reader.strings[reader.constants[i].name_idx as usize].as_str();

    assert!(
        reader.constants[0].has_value(),
        "{} should have value",
        name_at(0)
    );
    assert!(
        !reader.constants[1].has_value(),
        "{} should NOT have value",
        name_at(1)
    );
    assert!(
        reader.constants[2].has_value(),
        "{} should have value",
        name_at(2)
    );
    assert!(
        !reader.constants[3].has_value(),
        "{} should NOT have value",
        name_at(3)
    );
    assert!(
        !reader.constants[4].has_value(),
        "{} should NOT have value",
        name_at(4)
    );
    assert!(
        !reader.constants[5].has_value(),
        "{} should NOT have value",
        name_at(5)
    );
    assert!(
        reader.constants[6].has_value(),
        "{} should have value",
        name_at(6)
    );
    assert!(
        reader.constants[7].has_value(),
        "{} should have value",
        name_at(7)
    );
    assert!(
        reader.constants[8].has_value(),
        "{} should have value",
        name_at(8)
    );
    assert!(
        reader.constants[9].has_value(),
        "{} should have value",
        name_at(9)
    );
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
fn test_bridge_preserves_single_level_param() {
    let module = mock_module(vec![mock_constant_with_levels(
        "List.length",
        ConstantKind::Definition,
        true,
        vec!["u"],
    )]);
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();

    import_module_with_provenance(&module, &mut writer, &mut sidecar, Some("Init")).unwrap();

    writer.set_provenance(sidecar.to_bytes().unwrap());
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 1);
    assert!(c.has_level_params());
    assert_eq!(&reader.strings[c.level_params_start as usize], "u");
}

#[test]
fn test_bridge_preserves_multiple_level_params() {
    let module = mock_module(vec![mock_constant_with_levels(
        "List.map",
        ConstantKind::Definition,
        true,
        vec!["u", "v"],
    )]);
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();

    import_module_with_provenance(&module, &mut writer, &mut sidecar, Some("Init")).unwrap();

    writer.set_provenance(sidecar.to_bytes().unwrap());
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 2);
    let start = c.level_params_start as usize;
    assert_eq!(&reader.strings[start], "u");
    assert_eq!(&reader.strings[start + 1], "v");
}

#[test]
fn test_bridge_zero_level_params_when_empty() {
    let module = mock_module(vec![mock_constant(
        "Nat.add",
        ConstantKind::Definition,
        true,
    )]);
    let mut writer = ShardWriter::new();
    let mut sidecar = ProvenanceSidecar::new();

    import_module_with_provenance(&module, &mut writer, &mut sidecar, Some("Init")).unwrap();

    writer.set_provenance(sidecar.to_bytes().unwrap());
    let mut buf = Vec::new();
    writer.write(&mut buf).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    let c = &reader.constants[0];
    assert_eq!(c.level_params_count, 0);
    assert!(!c.has_level_params());
}

#[test]
fn test_bridge_level_params_round_trip_via_convert_modules() {
    let module = mock_module(vec![
        mock_constant_with_levels("List.map", ConstantKind::Definition, true, vec!["u", "v"]),
        mock_constant("Nat.add", ConstantKind::Definition, true),
        mock_constant_with_levels("Option.some", ConstantKind::Constructor, false, vec!["w"]),
    ]);

    let modules: Vec<(&str, &ParsedModule)> = vec![("Init", &module)];
    let (buf, _result) = convert_modules_to_mathverse(&modules).unwrap();
    let reader = ShardReader::from_bytes(&buf).unwrap();

    // List.map: [u, v]
    let c0 = &reader.constants[0];
    assert_eq!(c0.level_params_count, 2);
    assert_eq!(&reader.strings[c0.level_params_start as usize], "u");
    assert_eq!(&reader.strings[c0.level_params_start as usize + 1], "v");

    // Nat.add: no level params
    let c1 = &reader.constants[1];
    assert_eq!(c1.level_params_count, 0);

    // Option.some: [w]
    let c2 = &reader.constants[2];
    assert_eq!(c2.level_params_count, 1);
    assert_eq!(&reader.strings[c2.level_params_start as usize], "w");
}
