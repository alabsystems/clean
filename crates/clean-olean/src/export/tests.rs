// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for .olean export functionality.

use super::*;
use crate::expr::ParsedExpr;
use crate::import::{load_module_direct_with_cache, parse_load_module, ExprInternCache};
use crate::level::ParsedLevel;
use crate::load_parsed_module;
use crate::module::{DefinitionSafety, ReducibilityHintsData};
use crate::payload::CleanPayload;
use crate::region::CompactedRegion;
use crate::{parse_header, parse_imports_only};
use clean_kernel::env::{ConstantInfo, Environment, Reducibility, TrustedEnvExt};
use clean_kernel::expr::Expr;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::quot::{QuotKind, QuotVal};

fn export_parse_import_single_definition(
    name: &str,
    reducibility: Reducibility,
    is_reducible: bool,
) -> (Option<ReducibilityHintsData>, ConstantInfo) {
    let mut src_env = Environment::default();
    src_env.extend_constants_unchecked(std::iter::once(ConstantInfo {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::type_(),
        value: Some(Expr::prop()),
        is_reducible,
        reducibility,
        kind: clean_kernel::env::ConstantKind::Definition,
    }));

    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&src_env, &[], &[])
        .expect("export write_module_data_with_env should succeed");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("f00ba40000000000000000000000000000000000")
        .expect("export finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    let parsed_hints = parsed
        .constants
        .iter()
        .find(|c| c.name == name)
        .and_then(|c| c.hints);

    let mut dst_env = Environment::default();
    load_parsed_module(&mut dst_env, &parsed, Some("Test.Roundtrip".to_string()))
        .expect("load_parsed_module should succeed");
    let imported = dst_env
        .get_const(&Name::from_string(name))
        .expect("imported constant should exist")
        .clone();

    (parsed_hints, imported)
}

#[test]
fn test_write_string() {
    let mut exp = OleanExporter::new();
    let offset = exp.write_string("hello");

    // Verify we can read it back
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let s = region.read_lean_string_at(offset).unwrap();
    assert_eq!(s, "hello");
}

#[test]
fn test_string_interning() {
    let mut exp = OleanExporter::new();
    let off1 = exp.write_string("test");
    let off2 = exp.write_string("test");
    assert_eq!(off1, off2, "same string should return same offset");
}

#[test]
fn test_write_name_simple() {
    let mut exp = OleanExporter::new();
    let offset = exp.write_name("Nat");

    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let name = region.read_name_at(offset).unwrap();
    assert_eq!(name, "Nat");
}

#[test]
fn test_write_name_hierarchical() {
    let mut exp = OleanExporter::new();
    let offset = exp.write_name("Nat.add");

    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let name = region.read_name_at(offset).unwrap();
    assert_eq!(name, "Nat.add");
}

#[test]
fn test_write_name_deep() {
    let mut exp = OleanExporter::new();
    let offset = exp.write_name("Lean.Meta.Tactic.simp");

    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let name = region.read_name_at(offset).unwrap();
    assert_eq!(name, "Lean.Meta.Tactic.simp");
}

#[test]
fn test_name_interning() {
    let mut exp = OleanExporter::new();
    let off1 = exp.write_name("Nat.add");
    let off2 = exp.write_name("Nat.add");
    assert_eq!(off1, off2, "same name should return same offset");
}

#[test]
fn test_export_minimal_roundtrip() {
    let git_hash = "0123456789abcdef0123456789abcdef01234567";

    let bytes = OleanExporter::export_minimal(
        &[("Init.Prelude", false), ("Init.Core", false)],
        &["MyDef", "MyTheorem"],
        &[],
        git_hash,
    )
    .unwrap();

    // Parse header
    let header = parse_header(&bytes).unwrap();
    assert_eq!(header.git_hash_str(), git_hash);

    // Parse imports
    let imports = parse_imports_only(&bytes).unwrap();
    assert_eq!(imports.len(), 2);
    assert_eq!(imports[0].module_name, "Init.Prelude");
    assert_eq!(imports[1].module_name, "Init.Core");
}

#[test]
fn test_export_empty_module() {
    let git_hash = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    let bytes = OleanExporter::export_minimal(&[], &[], &[], git_hash).unwrap();

    let header = parse_header(&bytes).unwrap();
    assert_eq!(header.git_hash_str(), git_hash);

    let imports = parse_imports_only(&bytes).unwrap();
    assert!(imports.is_empty());
}

#[test]
fn test_export_full_module_roundtrip() {
    use crate::parse_module;

    let git_hash = "1ea5000000000000000000000000000000000000"; // 40 hex chars

    // Export a module with imports and constants
    let bytes = OleanExporter::export_minimal(
        &[
            ("Init.Prelude", false),
            ("Init.Core", false),
            ("Mathlib.Algebra.Group", false),
        ],
        &[
            "MyModule.myDef",
            "MyModule.myTheorem",
            "MyModule.Helper.util",
        ],
        &[],
        git_hash,
    )
    .unwrap();

    // Parse the full module
    let module = parse_module(&bytes).unwrap();

    // Verify imports
    assert_eq!(module.imports.len(), 3);
    assert_eq!(module.imports[0].module_name, "Init.Prelude");
    assert_eq!(module.imports[1].module_name, "Init.Core");
    assert_eq!(module.imports[2].module_name, "Mathlib.Algebra.Group");

    // Verify constant names
    assert_eq!(module.const_names.len(), 3);
    assert_eq!(module.const_names[0], "MyModule.myDef");
    assert_eq!(module.const_names[1], "MyModule.myTheorem");
    assert_eq!(module.const_names[2], "MyModule.Helper.util");
}

#[test]
fn test_export_runtime_only_import() {
    let git_hash = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

    let bytes = OleanExporter::export_minimal(
        &[("Init.Data.String", true)], // runtime_only = true
        &[],
        &[],
        git_hash,
    )
    .unwrap();

    let imports = parse_imports_only(&bytes).unwrap();
    assert_eq!(imports.len(), 1);
    assert_eq!(imports[0].module_name, "Init.Data.String");
    assert!(imports[0].runtime_only);
}

#[test]
fn test_write_name_with_numbers() {
    let mut exp = OleanExporter::new();

    // Test names with numeric components (e.g., _hyg.123)
    let offset = exp.write_name("_hyg.123");

    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let name = region.read_name_at(offset).unwrap();
    assert_eq!(name, "_hyg.123");
}

#[test]
fn test_write_level_zero() {
    let mut exp = OleanExporter::new();
    let ptr = exp.write_level(&Level::zero());
    // Level.zero is encoded as scalar 0 (pointer value 1)
    assert_eq!(ptr, 1, "Level.zero should be scalar 0");
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let parsed = region
        .resolve_level_ptr(ptr, 0)
        .expect("scalar level pointer should decode");
    assert!(
        matches!(parsed, ParsedLevel::Zero),
        "Level.zero pointer should decode to ParsedLevel::Zero, got {parsed:?}"
    );
}

#[test]
fn test_write_level_succ() {
    let mut exp = OleanExporter::new();
    let ptr = exp.write_level(&Level::succ(Level::zero()));
    // Succ(Zero) should be a real pointer, not a scalar
    assert!(ptr > 1, "Level.succ should be a real pointer");

    // Roundtrip: read back and verify
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let parsed = region.read_level_at(offset).unwrap();
    assert!(
        matches!(&parsed, ParsedLevel::Succ(inner) if matches!(**inner, ParsedLevel::Zero)),
        "Expected Succ(Zero), got {parsed:?}"
    );
}

#[test]
fn test_write_level_param() {
    let mut exp = OleanExporter::new();
    let ptr = exp.write_level(&Level::param(Name::from_string("u")));
    assert!(ptr > 1, "Level.param should be a real pointer");

    // Roundtrip: read back and verify
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let parsed = region.read_level_at(offset).unwrap();
    assert!(
        matches!(&parsed, ParsedLevel::Param(name) if name == "u"),
        "Expected Param(\"u\"), got {parsed:?}"
    );
}

#[test]
fn test_write_expr_bvar() {
    let mut exp = OleanExporter::new();
    let ptr = exp.write_expr(&Expr::bvar(0)).unwrap();
    // BVar(0) is encoded as scalar 0 (pointer value 1)
    assert_eq!(ptr, 1, "BVar(0) should be scalar 0");
    assert!(crate::is_scalar(ptr), "BVar should be scalar-tagged");
    assert_eq!(
        crate::unbox_scalar(ptr),
        0,
        "BVar(0) should unbox to de Bruijn index 0"
    );
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let idx = region
        .read_bignat_value(ptr)
        .expect("scalar bvar should decode as nat")
        .to_u64();
    assert_eq!(idx, Some(0), "decoded scalar bvar index should be 0");
}

#[test]
fn test_write_expr_sort() {
    let mut exp = OleanExporter::new();
    let ptr = exp.write_expr(&Expr::sort(Level::zero())).unwrap();
    assert!(ptr > 1, "Sort should be a real pointer");

    // Roundtrip: read back and verify
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let parsed = region.read_expr_at(offset).unwrap();
    assert!(
        matches!(parsed, ParsedExpr::Sort(ParsedLevel::Zero)),
        "Expected Sort(Zero), got {parsed:?}"
    );
}

#[test]
fn test_write_expr_const() {
    use clean_kernel::expr::LevelVec;
    let mut exp = OleanExporter::new();
    let ptr = exp
        .write_expr(&Expr::const_(Name::from_string("Nat"), LevelVec::new()))
        .unwrap();
    assert!(ptr > 1, "Const should be a real pointer");

    // Roundtrip: read back and verify
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let parsed = region.read_expr_at(offset).unwrap();
    assert!(
        matches!(&parsed, ParsedExpr::Const(name, levels) if name == "Nat" && levels.is_empty()),
        "Expected Const(\"Nat\", []), got {parsed:?}"
    );
}

#[test]
fn test_write_constant_info_axiom() {
    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();
    let info = ConstantInfo {
        name: Name::from_string("myAxiom"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // Prop
        value: None,                      // Axiom has no value
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: clean_kernel::env::ConstantKind::Axiom,
    };
    let ptr = exp.write_constant_info(&info).unwrap();
    assert!(ptr > 1, "ConstantInfo should be a real pointer");

    // Verify data was actually written (not just a pointer returned)
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for ConstantInfo, only wrote {data_written} bytes"
    );

    // Verify the object header is readable at the pointer offset
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "ConstantInfo header should have fields, got {header:?}"
    );
}

#[test]
fn test_write_constant_info_definition() {
    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();
    let info = ConstantInfo {
        name: Name::from_string("myDef"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())), // Type
        value: Some(Expr::sort(Level::zero())),        // value = Prop
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: clean_kernel::env::ConstantKind::Definition,
    };
    let ptr = exp.write_constant_info(&info).unwrap();
    assert!(ptr > 1, "ConstantInfo should be a real pointer");

    // Verify data was actually written
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for ConstantInfo definition, only wrote {data_written} bytes"
    );

    // Definition should write more data than axiom (has value field)
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "ConstantInfo header should have fields, got {header:?}"
    );
}

#[test]
fn test_definition_hints_roundtrip_regular_height() {
    let (parsed_hints, imported) = export_parse_import_single_definition(
        "Test.regularHeight",
        Reducibility::Regular(17),
        false,
    );

    assert_eq!(parsed_hints, Some(ReducibilityHintsData::Regular(17)));
    assert_eq!(imported.reducibility, Reducibility::Regular(17));
    assert!(
        !imported.is_reducible,
        "Regular hints should remain non-abbreviation"
    );
}

#[test]
fn test_reducibility_hints_writer_uses_real_lean_abi() {
    let mut exporter = OleanExporter::new();

    assert_eq!(
        exporter.write_reducibility_hints(&Reducibility::Opaque),
        OleanExporter::scalar_ptr(0),
        "opaque is Lean's nullary scalar constructor"
    );
    assert_eq!(
        exporter.write_reducibility_hints(&Reducibility::Reducible),
        OleanExporter::scalar_ptr(1),
        "abbrev is Lean's nullary scalar constructor"
    );

    let ptr = exporter.write_reducibility_hints(&Reducibility::Regular(17));
    let region = CompactedRegion::new(&exporter.data, exporter.base_addr);
    let offset = region.ptr_to_offset(ptr).expect("regular pointer");
    let header = region.read_header_at(offset).expect("regular header");
    assert_eq!(header.tag, 2);
    assert_eq!(header.other, 0);
    assert_eq!(header.cs_sz, 16);
    assert_eq!(
        region.read_u64_at(offset + 8).expect("unboxed UInt32"),
        17,
        "regular height is raw UInt32, not a tagged scalar pointer"
    );
}

#[test]
fn test_definition_hints_roundtrip_abbrev() {
    let (parsed_hints, imported) =
        export_parse_import_single_definition("Test.abbrev", Reducibility::Reducible, true);

    assert_eq!(parsed_hints, Some(ReducibilityHintsData::Abbrev));
    assert_eq!(imported.reducibility, Reducibility::Reducible);
    assert!(
        imported.is_reducible,
        "Abbrev hints should set is_reducible"
    );
}

#[test]
fn test_definition_hints_roundtrip_opaque() {
    let (parsed_hints, imported) =
        export_parse_import_single_definition("Test.opaqueHint", Reducibility::Opaque, false);

    assert_eq!(parsed_hints, Some(ReducibilityHintsData::Opaque));
    assert_eq!(imported.reducibility, Reducibility::Opaque);
    assert!(
        !imported.is_reducible,
        "Opaque hints should remain non-reducible"
    );
}

// ---------------------------------------------------------------------------
// DefinitionSafety round-trips.
//
// The loader previously parsed the `value`, `hints`, and base ConstantVal of a
// `defnInfo`, but silently discarded the trailing `safety`
// (`DefinitionSafety`) scalar. These tests pin the field across the full
// export -> parse round-trip and exercise the loader directly for the
// `unsafe` / `partial` / unknown tags that the kernel-backed export path
// cannot produce (the kernel `ConstantInfo` has no safety flag).
// ---------------------------------------------------------------------------

/// A trivial `Definition` ConstantInfo used to drive safety round-trips.
fn safety_test_definition(name: &str) -> ConstantInfo {
    ConstantInfo {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Some(Expr::sort(Level::zero())),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: clean_kernel::env::ConstantKind::Definition,
    }
}

/// Export a single definition with the given `safety`, finalize, parse it back,
/// and return the parsed `definition_safety`.
fn parse_definition_safety(name: &str, safety: DefinitionSafety) -> Option<DefinitionSafety> {
    let info = safety_test_definition(name);
    let mut exporter = OleanExporter::new();
    let const_ptr = exporter
        .write_definition_with_safety(&info, safety)
        .expect("write_definition_with_safety should succeed");
    let module_offset = exporter.write_module_data_with_const_ptrs(&[name], &[const_ptr]);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe7900000000000000000000000000000000ff")
        .expect("finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    parsed
        .constants
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("definition {name} should be present"))
        .definition_safety
}

#[test]
fn test_definition_safety_roundtrip_production_path_is_safe() {
    // The kernel-backed export path always writes `safe`; confirm the loader
    // now surfaces it instead of dropping the slot entirely.
    let (_hints, _imported) =
        export_parse_import_single_definition("Test.prodSafe", Reducibility::Regular(0), false);

    let info = safety_test_definition("Test.prodSafe");
    let mut exporter = OleanExporter::new();
    let const_ptr = exporter
        .write_constant_info(&info)
        .expect("write_constant_info should succeed");
    let module_offset =
        exporter.write_module_data_with_const_ptrs(&["Test.prodSafe"], &[const_ptr]);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe7900000000000000000000000000000000aa")
        .expect("finalize should succeed");
    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    let safety = parsed
        .constants
        .iter()
        .find(|c| c.name == "Test.prodSafe")
        .and_then(|c| c.definition_safety);
    assert_eq!(
        safety,
        Some(DefinitionSafety::Safe),
        "production exporter writes safe definitions; loader must report Safe"
    );
}

#[test]
fn test_definition_safety_roundtrip_unsafe_is_preserved() {
    assert_eq!(
        parse_definition_safety("Test.unsafeDef", DefinitionSafety::Unsafe),
        Some(DefinitionSafety::Unsafe),
        "unsafe definition safety must survive the round-trip"
    );
}

#[test]
fn test_definition_safety_roundtrip_partial_is_preserved() {
    assert_eq!(
        parse_definition_safety("Test.partialDef", DefinitionSafety::Partial),
        Some(DefinitionSafety::Partial),
        "partial definition safety must survive the round-trip"
    );
}

#[test]
fn test_definition_safety_roundtrip_safe_explicit() {
    assert_eq!(
        parse_definition_safety("Test.safeDef", DefinitionSafety::Safe),
        Some(DefinitionSafety::Safe),
        "explicit safe definition safety must survive the round-trip"
    );
}

#[test]
fn test_constant_export_rejects_unrepresentable_authority_and_shapes() {
    let mut exporter = OleanExporter::new();

    let mut theorem = safety_test_definition("Test.UnsafeTheorem");
    theorem.kind = clean_kernel::env::ConstantKind::Theorem;
    assert!(exporter
        .write_constant_info_with_definition_safety(&theorem, DefinitionSafety::Unsafe)
        .is_err());

    let mut opaque = safety_test_definition("Test.PartialOpaque");
    opaque.kind = clean_kernel::env::ConstantKind::Opaque;
    assert!(exporter
        .write_constant_info_with_definition_safety(&opaque, DefinitionSafety::Partial)
        .is_err());

    let mut axiom = safety_test_definition("Test.PartialAxiom");
    axiom.kind = clean_kernel::env::ConstantKind::Axiom;
    axiom.value = None;
    assert!(exporter
        .write_constant_info_with_definition_safety(&axiom, DefinitionSafety::Partial)
        .is_err());

    let mut valueless_definition = safety_test_definition("Test.ValuelessDefinition");
    valueless_definition.value = None;
    assert!(exporter
        .write_constant_info_with_definition_safety(&valueless_definition, DefinitionSafety::Safe)
        .is_err());

    let mut valued_axiom = safety_test_definition("Test.ValuedAxiom");
    valued_axiom.kind = clean_kernel::env::ConstantKind::Axiom;
    assert!(exporter
        .write_constant_info_with_definition_safety(&valued_axiom, DefinitionSafety::Safe)
        .is_err());
}

#[test]
fn test_environment_export_preserves_unsafe_and_partial_in_both_import_paths() {
    let unsafe_name = Name::from_string("Test.EnvUnsafe");
    let partial_name = Name::from_string("Test.EnvPartial");
    let safe_name = Name::from_string("Test.EnvSafe");
    let mut source = Environment::new();
    for name in [&unsafe_name, &partial_name, &safe_name] {
        source.extend_constants_unchecked(std::iter::once(ConstantInfo {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            value: Some(Expr::prop()),
            is_reducible: false,
            reducibility: Reducibility::Regular(1),
            kind: clean_kernel::env::ConstantKind::Definition,
        }));
    }
    source.mark_unsafe(unsafe_name.clone());
    source.mark_partial(partial_name.clone());

    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&source, &[], &[])
        .expect("environment export");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe7900000000000000000000000000000000e0")
        .expect("finalize environment export");

    let parsed = crate::parse_module(&bytes).expect("parse exported module");
    let parsed_safety = |name: &str| {
        parsed
            .constants
            .iter()
            .find(|constant| constant.name == name)
            .and_then(|constant| constant.definition_safety)
    };
    assert_eq!(
        parsed_safety("Test.EnvUnsafe"),
        Some(DefinitionSafety::Unsafe)
    );
    assert_eq!(
        parsed_safety("Test.EnvPartial"),
        Some(DefinitionSafety::Partial)
    );
    assert_eq!(parsed_safety("Test.EnvSafe"), Some(DefinitionSafety::Safe));

    let mut parsed_env = Environment::new();
    load_parsed_module(
        &mut parsed_env,
        &parsed,
        Some("Test.EnvSafetyParsed".into()),
    )
    .expect("parsed import");
    assert!(parsed_env.is_unsafe(&unsafe_name));
    assert!(parsed_env.is_partial(&partial_name));
    assert!(!parsed_env.is_unsafe(&safe_name));
    assert!(!parsed_env.is_partial(&safe_name));

    let load_module = parse_load_module(bytes).expect("direct parse");
    let mut direct_env = Environment::new();
    let mut cache = ExprInternCache::default();
    load_module_direct_with_cache(
        &mut direct_env,
        &load_module,
        Some("Test.EnvSafetyDirect".into()),
        &mut cache,
    )
    .expect("direct import");
    assert!(direct_env.is_unsafe(&unsafe_name));
    assert!(direct_env.is_partial(&partial_name));
    assert!(!direct_env.is_unsafe(&safe_name));
    assert!(!direct_env.is_partial(&safe_name));
}

#[test]
fn test_environment_export_preserves_all_unsafe_declaration_kinds_in_both_import_paths() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let axiom_name = Name::from_string("Test.UnsafeAxiom");
    let opaque_name = Name::from_string("Test.UnsafeOpaque");
    let ind_name = Name::from_string("Test.UnsafeBool");
    let false_name = Name::from_string("Test.UnsafeBool.false");
    let true_name = Name::from_string("Test.UnsafeBool.true");
    let rec_name = Name::from_string("Test.UnsafeBool.rec");

    let mut source = Environment::new();
    source.extend_constants_unchecked(
        [
            ConstantInfo {
                name: axiom_name.clone(),
                level_params: vec![],
                type_: Expr::type_(),
                value: None,
                is_reducible: false,
                reducibility: Reducibility::Opaque,
                kind: clean_kernel::env::ConstantKind::Axiom,
            },
            ConstantInfo {
                name: opaque_name.clone(),
                level_params: vec![],
                type_: Expr::type_(),
                value: Some(Expr::prop()),
                is_reducible: false,
                reducibility: Reducibility::Opaque,
                kind: clean_kernel::env::ConstantKind::Opaque,
            },
        ]
        .into_iter(),
    );

    let bool_ref = Expr::const_(ind_name.clone(), vec![]);
    source
        .add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: ind_name.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: false_name.clone(),
                        type_: bool_ref.clone(),
                    },
                    Constructor {
                        name: true_name.clone(),
                        type_: bool_ref,
                    },
                ],
            }],
        })
        .expect("construct valid synthetic family");

    let unsafe_names = [
        axiom_name.clone(),
        opaque_name.clone(),
        ind_name.clone(),
        false_name.clone(),
        true_name.clone(),
        rec_name.clone(),
    ];
    for name in &unsafe_names {
        source.mark_unsafe(name.clone());
    }

    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&source, &[], &[])
        .expect("environment export");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe7900000000000000000000000000000000e1")
        .expect("finalize environment export");

    let parsed = crate::parse_module(&bytes).expect("parse exported module");
    let constant = |name: &str| {
        parsed
            .constants
            .iter()
            .find(|constant| constant.name == name)
            .unwrap_or_else(|| panic!("missing parsed constant {name}"))
    };
    assert_eq!(
        constant("Test.UnsafeAxiom").definition_safety,
        Some(DefinitionSafety::Unsafe)
    );
    assert_eq!(
        constant("Test.UnsafeOpaque").definition_safety,
        Some(DefinitionSafety::Unsafe)
    );
    assert!(
        constant("Test.UnsafeBool")
            .inductive_val
            .as_ref()
            .expect("inductive data")
            .is_unsafe
    );
    assert!(
        constant("Test.UnsafeBool.false")
            .constructor_val
            .as_ref()
            .expect("constructor data")
            .is_unsafe
    );
    assert!(
        constant("Test.UnsafeBool.true")
            .constructor_val
            .as_ref()
            .expect("constructor data")
            .is_unsafe
    );
    assert!(
        constant("Test.UnsafeBool.rec")
            .recursor_val
            .as_ref()
            .expect("recursor data")
            .is_unsafe
    );

    let assert_imported_marks = |env: &Environment| {
        for name in &unsafe_names {
            assert!(env.is_unsafe(name), "{} lost unsafe authority", name);
            assert!(!env.is_partial(name), "{} was spuriously partial", name);
        }
    };

    let mut parsed_env = Environment::new();
    load_parsed_module(
        &mut parsed_env,
        &parsed,
        Some("Test.AllSafetyParsed".into()),
    )
    .expect("parsed import");
    assert_imported_marks(&parsed_env);

    let load_module = parse_load_module(bytes).expect("direct parse");
    let mut direct_env = Environment::new();
    let mut cache = ExprInternCache::default();
    load_module_direct_with_cache(
        &mut direct_env,
        &load_module,
        Some("Test.AllSafetyDirect".into()),
        &mut cache,
    )
    .expect("direct import");
    assert_imported_marks(&direct_env);
}

#[test]
fn test_definition_safety_unknown_tag_fails_closed() {
    // Build a defnInfo whose safety scalar carries an out-of-range tag (7);
    // the loader must reject it rather than fabricate safe authority.
    let info = safety_test_definition("Test.weirdSafety");
    let mut exporter = OleanExporter::new();

    let name_offset = exporter.write_kernel_name(&info.name);
    let name_ptr = exporter.offset_to_ptr(name_offset);
    let level_params_ptr = exporter.write_level_params(&info.level_params);
    let type_ptr = exporter.write_expr(&info.type_).expect("type expr");
    let value_ptr = exporter
        .write_expr(info.value.as_ref().expect("value"))
        .expect("value expr");
    let hints_ptr = exporter.write_reducibility_hints(&info.reducibility);

    exporter.align8();
    let const_val_offset = exporter.current_offset();
    exporter.write_header(0, 3, 0);
    exporter.write_u64(name_ptr);
    exporter.write_u64(level_params_ptr);
    exporter.write_u64(type_ptr);
    let const_val_ptr = exporter.offset_to_ptr(const_val_offset);

    exporter.align8();
    let val_offset = exporter.current_offset();
    exporter.write_header(0, 4, 0);
    exporter.write_u64(const_val_ptr);
    exporter.write_u64(value_ptr);
    exporter.write_u64(hints_ptr);
    exporter.write_u64(OleanExporter::scalar_ptr(7)); // unknown safety tag
    let val_ptr = exporter.offset_to_ptr(val_offset);

    exporter.align8();
    let wrapper_offset = exporter.current_offset();
    exporter.write_header(1, 1, 0); // defnInfo
    exporter.write_u64(val_ptr);
    let const_ptr = exporter.offset_to_ptr(wrapper_offset);

    let module_offset =
        exporter.write_module_data_with_const_ptrs(&["Test.weirdSafety"], &[const_ptr]);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe79000000000000000000000000000000007e")
        .expect("finalize should succeed");
    assert!(
        crate::parse_module(&bytes).is_err(),
        "an unrecognized safety tag must reject the definition"
    );
}

#[test]
fn test_safe_axiom_declaration_safety_roundtrips() {
    let mut env = Environment::default();
    env.extend_constants_unchecked(std::iter::once(ConstantInfo {
        name: Name::from_string("Test.axiomNoSafety"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: clean_kernel::env::ConstantKind::Axiom,
    }));
    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&env, &[], &[])
        .expect("write_module_data_with_env should succeed");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("5afe790000000000000000000000000000000a00")
        .expect("finalize should succeed");
    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    let constant = parsed
        .constants
        .iter()
        .find(|c| c.name == "Test.axiomNoSafety")
        .expect("axiom should be present");
    assert_eq!(
        constant.definition_safety,
        Some(DefinitionSafety::Safe),
        "AxiomVal.isUnsafe=false must be represented explicitly as Safe"
    );
}

#[test]
fn test_definition_safety_tag_roundtrip_total() {
    assert_eq!(DefinitionSafety::Unsafe.to_tag(), 0);
    assert_eq!(DefinitionSafety::Safe.to_tag(), 1);
    assert_eq!(DefinitionSafety::Partial.to_tag(), 2);
    for safety in [
        DefinitionSafety::Safe,
        DefinitionSafety::Unsafe,
        DefinitionSafety::Partial,
    ] {
        assert_eq!(
            DefinitionSafety::from_tag(safety.to_tag()),
            Some(safety),
            "from_tag(to_tag(s)) must equal Some(s)"
        );
    }
    assert_eq!(DefinitionSafety::from_tag(3), None);
    assert_eq!(DefinitionSafety::from_tag(u64::MAX), None);
}

#[test]
fn test_export_with_env() {
    use crate::parse_module;
    use clean_kernel::expr::LevelVec;

    let git_hash = "c0de000000000000000000000000000000000001";

    // Create a minimal environment with one constant
    let mut env = Environment::default();
    let info = ConstantInfo {
        name: Name::from_string("TestModule.myDef"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())), // Type
        value: Some(Expr::const_(Name::from_string("Nat"), LevelVec::new())),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: clean_kernel::env::ConstantKind::Definition,
    };
    env.extend_constants_unchecked(std::iter::once(info));

    // Export using write_module_data_with_env
    let mut exporter = OleanExporter::new();
    let module_offset = exporter.write_module_data_with_env(&env, &[], &[]).unwrap();
    eprintln!("DEBUG: module_offset = {}", module_offset);
    eprintln!("DEBUG: data.len() = {}", exporter.data.len());
    exporter.set_root(module_offset);
    let bytes = exporter.finalize(git_hash).unwrap();
    eprintln!("DEBUG: bytes.len() = {}", bytes.len());
    eprintln!("DEBUG: root_ptr bytes = {:02x?}", &bytes[56..64]);
    let header = parse_header(&bytes).unwrap();
    eprintln!("DEBUG: header.base_addr = 0x{:x}", header.base_addr);

    // Parse the module and verify
    let module = parse_module(&bytes).unwrap();

    // Verify constant name was written
    assert_eq!(module.const_names.len(), 1);
    assert_eq!(module.const_names[0], "TestModule.myDef");
}

#[test]
fn test_export_with_payload_populates_constants() {
    use crate::parse_module;
    use clean_kernel::expr::LevelVec;

    let git_hash = "c0de000000000000000000000000000000000002";

    let info = ConstantInfo {
        name: Name::from_string("TestModule.payloadDef"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Some(Expr::const_(Name::from_string("Nat"), LevelVec::new())),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: clean_kernel::env::ConstantKind::Definition,
    };

    let payload = CleanPayload {
        constants: vec![info],
        inductives: vec![],
        constructors: vec![],
        recursors: vec![],
        structure_fields: vec![],
    };

    let bytes = OleanExporter::export_with_payload(
        &[],
        &["TestModule.payloadDef"],
        &[],
        git_hash,
        &payload,
    )
    .unwrap();

    let module = parse_module(&bytes).unwrap();

    assert_eq!(module.const_names.len(), 1);
    assert_eq!(module.constants.len(), 1);
    assert_eq!(module.const_names[0], "TestModule.payloadDef");
}

#[test]
fn test_export_with_inductive() {
    use crate::parse_module;
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let git_hash = "1a10c11e00000000000000000000000000000000";

    // Create environment with an inductive type (simplified Nat-like)
    let mut env = Environment::default();

    // Add a simple Bool inductive: inductive Bool : Type where | false | true
    let bool_name = Name::from_string("MyBool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyBool.true"),
                    type_: bool_ref,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("Failed to add inductive");

    // Export the environment
    let mut exporter = OleanExporter::new();
    let module_offset = exporter.write_module_data_with_env(&env, &[], &[]).unwrap();
    exporter.set_root(module_offset);
    let bytes = exporter.finalize(git_hash).unwrap();

    // Parse and verify
    let module = parse_module(&bytes).unwrap();

    // Should have: MyBool (inductive) + MyBool.false + MyBool.true (constructors)
    // + MyBool.rec (recursor)
    assert!(
        module.const_names.len() >= 4,
        "Expected at least 4 constants (inductive + 2 ctors + rec), got {}",
        module.const_names.len()
    );

    // Verify the names are present
    assert!(
        module.const_names.contains(&"MyBool".to_string()),
        "Missing MyBool inductive"
    );
    assert!(
        module.const_names.contains(&"MyBool.false".to_string()),
        "Missing MyBool.false constructor"
    );
    assert!(
        module.const_names.contains(&"MyBool.true".to_string()),
        "Missing MyBool.true constructor"
    );
    assert!(
        module.const_names.contains(&"MyBool.rec".to_string()),
        "Missing MyBool.rec recursor"
    );
}

#[test]
fn test_write_inductive_info() {
    // Direct test of write_inductive_info serialization
    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();

    let ind = InductiveVal {
        name: Name::from_string("TestInd"),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![Name::from_string("TestInd")],
        constructor_names: vec![Name::from_string("TestInd.mk")],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };

    let ptr = exp.write_inductive_info(&ind).unwrap();
    assert!(ptr > 1, "InductiveInfo should be a real pointer");

    // Verify substantial data was written
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for InductiveInfo, only wrote {data_written} bytes"
    );

    // Verify the object header is readable
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "InductiveInfo header should have fields, got {header:?}"
    );
}

// ---------------------------------------------------------------------------
// InductiveVal field round-trips.
//
// `write_inductive_info` previously laid `InductiveVal` out as nine boxed
// 8-byte scalar fields (numParams, numIndices, all, ctors, isRec, isUnsafe,
// isReflexive, isNested), but the loader's `read_inductive_val_data` (which
// is calibrated against real Lean `.olean` files) expects the Lean field
// order `numParams, numIndices, all, ctors, numNested` followed by the three
// trailing booleans `isRec`/`isUnsafe`/`isReflexive` packed as raw `u8`s in a
// single word. The two layouts disagreed: on read, `numNested` consumed the
// `isRec` slot and `isReflexive` was silently dropped (always parsed false).
// These tests pin every field across a full export -> parse round-trip and
// confirm the flags propagate into the kernel `InductiveVal` on load.
// ---------------------------------------------------------------------------

/// Build an `InductiveVal` with the given flags for round-trip exercises.
fn inductive_with_flags(
    name: &str,
    num_params: u32,
    num_indices: u32,
    is_recursive: bool,
    is_reflexive: bool,
    is_nested: bool,
) -> InductiveVal {
    InductiveVal {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::type_(),
        num_params,
        num_indices,
        all_names: vec![Name::from_string(name)],
        constructor_names: vec![Name::from_string(&format!("{name}.mk"))],
        is_recursive,
        is_reflexive,
        is_large_elim: true,
        is_nested,
    }
}

/// Export a single inductive, finalize, parse it back, and return the parsed
/// `InductiveValData`.
fn parse_inductive_val(ind: &InductiveVal) -> crate::module::InductiveValData {
    let mut exporter = OleanExporter::new();
    let const_ptr = exporter
        .write_inductive_info(ind)
        .expect("write_inductive_info should succeed");
    let name = ind.name.to_string();
    let module_offset = exporter.write_module_data_with_const_ptrs(&[&name], &[const_ptr]);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("1d00000000000000000000000000000000000000")
        .expect("finalize should succeed");
    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    parsed
        .constants
        .iter()
        .find(|c| c.name == name)
        .unwrap_or_else(|| panic!("inductive {name} should be present"))
        .inductive_val
        .clone()
        .unwrap_or_else(|| panic!("inductive {name} should carry inductive_val data"))
}

#[test]
fn test_inductive_val_roundtrip_all_flags_set() {
    let ind = inductive_with_flags("Test.IndAllSet", 3, 2, true, true, true);
    let iv = parse_inductive_val(&ind);
    assert_eq!(iv.num_params, 3, "numParams must round-trip");
    assert_eq!(iv.num_indices, 2, "numIndices must round-trip");
    assert!(iv.is_rec, "isRec must round-trip true");
    assert!(
        !iv.is_unsafe,
        "isUnsafe is exported false and must stay false"
    );
    assert!(
        iv.is_reflexive,
        "isReflexive must round-trip true (regression: was dropped)"
    );
    assert!(
        iv.is_nested,
        "isNested must round-trip true (regression: read isRec's slot)"
    );
    assert_eq!(iv.all, vec!["Test.IndAllSet".to_string()]);
    assert_eq!(iv.ctors, vec!["Test.IndAllSet.mk".to_string()]);
}

#[test]
fn test_inductive_val_roundtrip_all_flags_clear() {
    let ind = inductive_with_flags("Test.IndAllClear", 0, 0, false, false, false);
    let iv = parse_inductive_val(&ind);
    assert_eq!(iv.num_params, 0);
    assert_eq!(iv.num_indices, 0);
    assert!(!iv.is_rec, "isRec must round-trip false");
    assert!(!iv.is_unsafe);
    assert!(!iv.is_reflexive, "isReflexive must round-trip false");
    assert!(!iv.is_nested, "isNested must round-trip false");
}

#[test]
fn test_inductive_val_roundtrip_reflexive_independent_of_rec() {
    // The previous layout collapsed isReflexive onto a dropped slot, so a
    // reflexive-but-not-recursive inductive lost its reflexivity. Pin the two
    // flags as independent.
    let ind = inductive_with_flags("Test.IndReflexiveOnly", 1, 0, false, true, false);
    let iv = parse_inductive_val(&ind);
    assert!(!iv.is_rec, "isRec should be false");
    assert!(
        iv.is_reflexive,
        "isReflexive must survive even when isRec is false"
    );
    assert!(!iv.is_nested, "isNested should be false");
}

#[test]
fn test_inductive_val_roundtrip_nested_independent_of_rec() {
    // numNested must not be confused with isRec: a non-recursive but nested
    // inductive must report is_nested=true and is_rec=false.
    let ind = inductive_with_flags("Test.IndNestedOnly", 2, 1, false, false, true);
    let iv = parse_inductive_val(&ind);
    assert!(
        !iv.is_rec,
        "isRec should be false for a nested-only inductive"
    );
    assert!(iv.is_nested, "isNested must round-trip true independently");
    assert_eq!(
        iv.num_params, 2,
        "numParams must not be shifted by numNested"
    );
    assert_eq!(
        iv.num_indices, 1,
        "numIndices must not be shifted by numNested"
    );
}

#[test]
fn test_inductive_val_roundtrip_flags_propagate_to_kernel() {
    // End-to-end: the parsed flags must survive the kernel load. Only
    // is_large_elim is recomputed by the loader; is_recursive / is_reflexive /
    // is_nested flow straight through.
    let ind = inductive_with_flags("Test.IndKernel", 1, 0, true, true, true);
    let mut exporter = OleanExporter::new();
    let const_ptr = exporter
        .write_inductive_info(&ind)
        .expect("write_inductive_info should succeed");
    let module_offset =
        exporter.write_module_data_with_const_ptrs(&["Test.IndKernel"], &[const_ptr]);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("1d00000000000000000000000000000000000001")
        .expect("finalize should succeed");
    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");

    let mut env = Environment::default();
    load_parsed_module(&mut env, &parsed, Some("Test.IndRoundtrip".to_string()))
        .expect("load_parsed_module should succeed");

    let loaded = env
        .get_inductive(&Name::from_string("Test.IndKernel"))
        .expect("loaded inductive should exist");
    assert_eq!(loaded.num_params, 1, "kernel num_params must match");
    assert_eq!(loaded.num_indices, 0, "kernel num_indices must match");
    assert!(loaded.is_recursive, "kernel is_recursive must round-trip");
    assert!(loaded.is_reflexive, "kernel is_reflexive must round-trip");
    assert!(loaded.is_nested, "kernel is_nested must round-trip");
}

#[test]
fn test_pack_bools3_byte_layout() {
    // The packed word must place b0/b1/b2 in bytes 0/1/2 so the loader's raw
    // byte reads at +56/+57/+58 recover them.
    assert_eq!(OleanExporter::pack_bools3(false, false, false), 0);
    assert_eq!(OleanExporter::pack_bools3(true, false, false), 0x00_00_01);
    assert_eq!(OleanExporter::pack_bools3(false, true, false), 0x00_01_00);
    assert_eq!(OleanExporter::pack_bools3(false, false, true), 0x01_00_00);
    assert_eq!(OleanExporter::pack_bools3(true, true, true), 0x01_01_01);
    let word = OleanExporter::pack_bools3(true, false, true);
    let bytes = word.to_le_bytes();
    assert_eq!(bytes[0], 1, "byte 0 is b0 (isRec)");
    assert_eq!(bytes[1], 0, "byte 1 is b1 (isUnsafe)");
    assert_eq!(bytes[2], 1, "byte 2 is b2 (isReflexive)");
}

#[test]
fn test_write_constructor_info() {
    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();

    let ctor = ConstructorVal {
        name: Name::from_string("TestInd.mk"),
        inductive_name: Name::from_string("TestInd"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("TestInd"), vec![]),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };

    let ptr = exp.write_constructor_info(&ctor).unwrap();
    assert!(ptr > 1, "ConstructorInfo should be a real pointer");

    // Verify substantial data was written
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for ConstructorInfo, only wrote {data_written} bytes"
    );

    // Verify the object header is readable
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "ConstructorInfo header should have fields, got {header:?}"
    );
}

#[test]
fn test_write_recursor_info() {
    use clean_kernel::inductive::RecursorArgOrder;

    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();

    let rec = RecursorVal {
        name: Name::from_string("TestInd.rec"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(), // Simplified
        inductive_name: Name::from_string("TestInd"),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            constructor_name: Name::from_string("TestInd.mk"),
            num_fields: 0,
            recursive_fields: vec![],
            rhs: Expr::bvar(0),
        }],
        is_k: false,
    };

    let ptr = exp.write_recursor_info(&rec).unwrap();
    assert!(ptr > 1, "RecursorInfo should be a real pointer");

    // Verify substantial data was written
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for RecursorInfo, only wrote {data_written} bytes"
    );

    // Verify the object header is readable
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "RecursorInfo header should have fields, got {header:?}"
    );
}

/// Build a single-rule `RecursorVal` for round-trip exercises.
fn recursor_for_roundtrip(
    name: &str,
    arg_order: clean_kernel::inductive::RecursorArgOrder,
) -> RecursorVal {
    let inductive = name
        .strip_suffix(".rec")
        .or_else(|| name.strip_suffix(".recOn"))
        .unwrap_or(name);
    RecursorVal {
        name: Name::from_string(name),
        arg_order,
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        inductive_name: Name::from_string(inductive),
        num_params: 1,
        num_indices: 0,
        num_motives: 1,
        num_minors: 1,
        rules: vec![RecursorRule {
            constructor_name: Name::from_string(&format!("{inductive}.mk")),
            num_fields: 0,
            recursive_fields: vec![],
            rhs: Expr::bvar(0),
        }],
        is_k: false,
    }
}

/// A recursor carried in a CleanPayload must round-trip its `arg_order` even
/// when the name does NOT match the `recOn` heuristic. The bare Lean-4
/// `.olean` `RecursorVal` layout has no `arg_order` slot, so name-based
/// inference would corrupt a custom-named `MajorAfterMotive` recursor. The
/// CleanPayload is the lossless carrier, and the loader must prefer it.
#[test]
fn test_recursor_arg_order_custom_name_survives_payload_roundtrip() {
    use clean_kernel::inductive::RecursorArgOrder;

    let git_hash = "abcdef0000000000000000000000000000000000";

    // A recursor whose name would be inferred as MajorAfterMinors, but whose
    // actual layout is MajorAfterMotive. Only the payload can preserve this.
    let rec = recursor_for_roundtrip("Foo.customElim", RecursorArgOrder::MajorAfterMotive);
    let rec_name = rec.name.clone();

    let payload = CleanPayload {
        constants: vec![],
        inductives: vec![],
        constructors: vec![],
        recursors: vec![rec],
        structure_fields: vec![],
    };

    let bytes =
        OleanExporter::export_with_payload(&[], &["Foo.customElim"], &[], git_hash, &payload)
            .expect("export with payload");

    // Write to a temp file and load through the full file-import path, which
    // decodes the CleanPayload and registers its recursors.
    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("Foo.olean");
    std::fs::write(&path, &bytes).expect("write olean");

    let mut env = Environment::default();
    crate::load_olean_file(&mut env, &path).expect("load olean file");

    let loaded = env
        .get_recursor(&rec_name)
        .expect("custom recursor must be registered from payload");
    assert_eq!(
        loaded.arg_order,
        RecursorArgOrder::MajorAfterMotive,
        "custom-named recursor's MajorAfterMotive arg_order must survive the \
         payload round-trip (name-based inference alone would corrupt it)"
    );
}

/// The standard `T.rec` recursor round-trips as `MajorAfterMinors` through the
/// payload path, confirming the lossless contract for the common case too.
#[test]
fn test_recursor_arg_order_standard_rec_survives_payload_roundtrip() {
    use clean_kernel::inductive::RecursorArgOrder;

    let git_hash = "fedcba0000000000000000000000000000000000";

    let rec = recursor_for_roundtrip("Foo.rec", RecursorArgOrder::MajorAfterMinors);
    let rec_name = rec.name.clone();

    let payload = CleanPayload {
        constants: vec![],
        inductives: vec![],
        constructors: vec![],
        recursors: vec![rec],
        structure_fields: vec![],
    };

    let bytes = OleanExporter::export_with_payload(&[], &["Foo.rec"], &[], git_hash, &payload)
        .expect("export with payload");

    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("Foo.olean");
    std::fs::write(&path, &bytes).expect("write olean");

    let mut env = Environment::default();
    crate::load_olean_file(&mut env, &path).expect("load olean file");

    let loaded = env
        .get_recursor(&rec_name)
        .expect("standard recursor must be registered from payload");
    assert_eq!(
        loaded.arg_order,
        RecursorArgOrder::MajorAfterMinors,
        "standard T.rec arg_order must survive the payload round-trip"
    );
}

#[test]
fn test_write_quotient_info() {
    let mut exp = OleanExporter::new();
    let data_before = exp.data.len();

    let quot = QuotVal {
        name: Name::from_string("Quot"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(), // Simplified
        kind: QuotKind::Type,
    };

    let ptr = exp.write_quotient_info(&quot).unwrap();
    assert!(ptr > 1, "QuotientInfo should be a real pointer");

    // Verify substantial data was written
    let data_written = exp.data.len() - data_before;
    assert!(
        data_written > 8,
        "Expected substantial data for QuotientInfo, only wrote {data_written} bytes"
    );

    // Verify the object header is readable
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert!(
        header.num_fields() > 0,
        "QuotientInfo header should have fields, got {header:?}"
    );
}

#[test]
fn test_export_quotient_roundtrip() {
    use crate::parse_module;

    let git_hash = "9007500000000000000000000000000000000000";

    // Create environment with quotient primitives
    let mut env = Environment::default();
    env.init_quot();

    // Export the environment
    let mut exporter = OleanExporter::new();
    let module_offset = exporter.write_module_data_with_env(&env, &[], &[]).unwrap();
    exporter.set_root(module_offset);
    let bytes = exporter.finalize(git_hash).unwrap();

    // Parse and verify
    let module = parse_module(&bytes).unwrap();

    // Should have 4 quotient primitives: Quot, Quot.mk, Quot.lift, Quot.ind
    assert!(
        module.const_names.len() >= 4,
        "Expected at least 4 quotient constants, got {}",
        module.const_names.len()
    );

    // Verify the names are present
    let names: Vec<&str> = module.const_names.iter().map(|s| s.as_str()).collect();
    assert!(names.contains(&"Quot"), "Missing Quot");
    assert!(names.contains(&"Quot.mk"), "Missing Quot.mk");
    assert!(names.contains(&"Quot.lift"), "Missing Quot.lift");
    assert!(names.contains(&"Quot.ind"), "Missing Quot.ind");

    // Verify constants array matches
    assert_eq!(
        module.constants.len(),
        module.const_names.len(),
        "constants and const_names should have same length"
    );

    // The QuotVal.kind discriminant must survive the round-trip: each
    // quotient constant should parse back with kind Quot and recover the
    // exact ParsedQuotKind it was exported with (regression: the kind was
    // previously read only as the bare `Quot` constant kind and dropped).
    use crate::module::{ConstantKind, ParsedQuotKind};
    let expected_kind = |name: &str| -> Option<ParsedQuotKind> {
        match name {
            "Quot" => Some(ParsedQuotKind::Type),
            "Quot.mk" => Some(ParsedQuotKind::Mk),
            "Quot.lift" => Some(ParsedQuotKind::Lift),
            "Quot.ind" => Some(ParsedQuotKind::Ind),
            "Quot.sound" => Some(ParsedQuotKind::Sound),
            _ => None,
        }
    };
    let mut checked = 0usize;
    for c in &module.constants {
        if let Some(want) = expected_kind(&c.name) {
            assert_eq!(
                c.kind,
                ConstantKind::Quot,
                "{} should parse as ConstantKind::Quot",
                c.name
            );
            assert_eq!(
                c.quot_kind,
                Some(want),
                "{} should recover quot_kind {want:?}",
                c.name
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 4,
        "expected to check at least the 4 core quotient primitives, checked {checked}"
    );
}

// ---------------------------------------------------------------------------
// ConstantKind (defn / theorem / opaque) round-trips.
//
// `write_constant_info` previously encoded every value-carrying constant as
// `defnInfo` (tag 1) regardless of `info.kind`, silently downgrading
// theorems and opaque constants to plain definitions on re-import. The
// kernel `ConstantInfo` documents that this distinction "cannot be encoded
// by reducibility alone" (both Theorem and Opaque map to
// `Reducibility::Opaque`), so the outer wrapper tag is the only carrier.
// These tests pin the kind across the full export -> parse -> import path.
// ---------------------------------------------------------------------------

/// Build a value-carrying `ConstantInfo` of the given kind. The value is a
/// distinctive `Const` reference so value survival can be asserted too.
fn kind_test_constant(name: &str, kind: clean_kernel::env::ConstantKind) -> ConstantInfo {
    use clean_kernel::expr::LevelVec;
    ConstantInfo {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // Prop
        value: Some(Expr::const_(
            Name::from_string("KindRoundtrip.body"),
            LevelVec::new(),
        )),
        is_reducible: false,
        reducibility: Reducibility::Opaque,
        kind,
    }
}

/// Export a single value-carrying constant through the production env path,
/// parse it back, and return the parsed constant.
fn export_parse_single_constant(info: ConstantInfo) -> crate::module::ParsedConstant {
    let name = info.name.to_string();
    let mut src_env = Environment::default();
    src_env.extend_constants_unchecked(std::iter::once(info));

    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&src_env, &[], &[])
        .expect("export write_module_data_with_env should succeed");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("c0de450000000000000000000000000000000001")
        .expect("export finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    parsed
        .constants
        .into_iter()
        .find(|c| c.name == name)
        .expect("exported constant should parse back")
}

#[test]
fn test_export_theorem_kind_preserved_through_parse() {
    use crate::module::ConstantKind as ParsedKind;
    let parsed = export_parse_single_constant(kind_test_constant(
        "Test.kindThm",
        clean_kernel::env::ConstantKind::Theorem,
    ));
    assert_eq!(
        parsed.kind,
        ParsedKind::Theorem,
        "a theorem must parse back as ConstantKind::Theorem, not Definition"
    );
    assert!(
        parsed.value.is_some(),
        "the theorem's proof value must survive the round-trip"
    );
}

#[test]
fn test_export_opaque_kind_preserved_through_parse() {
    use crate::module::ConstantKind as ParsedKind;
    let parsed = export_parse_single_constant(kind_test_constant(
        "Test.kindOpaque",
        clean_kernel::env::ConstantKind::Opaque,
    ));
    assert_eq!(
        parsed.kind,
        ParsedKind::Opaque,
        "an opaque constant must parse back as ConstantKind::Opaque, not Definition"
    );
    assert!(
        parsed.value.is_some(),
        "the opaque constant's value must survive the round-trip"
    );
}

#[test]
fn test_export_definition_kind_still_definition_after_parse() {
    use crate::module::ConstantKind as ParsedKind;
    let parsed = export_parse_single_constant(kind_test_constant(
        "Test.kindDef",
        clean_kernel::env::ConstantKind::Definition,
    ));
    assert_eq!(
        parsed.kind,
        ParsedKind::Definition,
        "a definition must still parse back as ConstantKind::Definition"
    );
    assert!(
        parsed.value.is_some(),
        "the definition's value must survive the round-trip"
    );
}

#[test]
fn test_export_theorem_kind_preserved_through_import() {
    let info = kind_test_constant(
        "Test.kindThmImport",
        clean_kernel::env::ConstantKind::Theorem,
    );

    let mut src_env = Environment::default();
    src_env.extend_constants_unchecked(std::iter::once(info));
    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&src_env, &[], &[])
        .expect("export should succeed");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("c0de450000000000000000000000000000000002")
        .expect("finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    let mut dst_env = Environment::default();
    load_parsed_module(
        &mut dst_env,
        &parsed,
        Some("Test.KindRoundtrip".to_string()),
    )
    .expect("load_parsed_module should succeed");

    let imported = dst_env
        .get_const(&Name::from_string("Test.kindThmImport"))
        .expect("imported constant should exist")
        .clone();
    assert_eq!(
        imported.kind,
        clean_kernel::env::ConstantKind::Theorem,
        "theorem kind must survive export -> parse -> import end-to-end"
    );
}

#[test]
fn test_export_opaque_kind_preserved_through_import() {
    let info = kind_test_constant(
        "Test.kindOpaqueImport",
        clean_kernel::env::ConstantKind::Opaque,
    );

    let mut src_env = Environment::default();
    src_env.extend_constants_unchecked(std::iter::once(info));
    let mut exporter = OleanExporter::new();
    let module_offset = exporter
        .write_module_data_with_env(&src_env, &[], &[])
        .expect("export should succeed");
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("c0de450000000000000000000000000000000003")
        .expect("finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");
    let mut dst_env = Environment::default();
    load_parsed_module(
        &mut dst_env,
        &parsed,
        Some("Test.KindRoundtrip".to_string()),
    )
    .expect("load_parsed_module should succeed");

    let imported = dst_env
        .get_const(&Name::from_string("Test.kindOpaqueImport"))
        .expect("imported constant should exist")
        .clone();
    assert_eq!(
        imported.kind,
        clean_kernel::env::ConstantKind::Opaque,
        "opaque kind must survive export -> parse -> import end-to-end"
    );
}

#[test]
fn test_export_theorem_wrapper_tag_is_thm_info() {
    // The outer ConstantInfo wrapper tag is the load-bearing discriminant:
    // 2 = thmInfo. Verify the exporter actually writes tag 2 (not tag 1).
    let info = kind_test_constant("Test.kindThmTag", clean_kernel::env::ConstantKind::Theorem);
    let mut exp = OleanExporter::new();
    let ptr = exp
        .write_constant_info(&info)
        .expect("write_constant_info should succeed");
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert_eq!(
        header.tag, 2,
        "thmInfo wrapper must use tag 2, got {header:?}"
    );
}

#[test]
fn test_export_opaque_wrapper_tag_is_opaque_info() {
    // 3 = opaqueInfo.
    let info = kind_test_constant(
        "Test.kindOpaqueTag",
        clean_kernel::env::ConstantKind::Opaque,
    );
    let mut exp = OleanExporter::new();
    let ptr = exp
        .write_constant_info(&info)
        .expect("write_constant_info should succeed");
    let region = CompactedRegion::new(&exp.data, exp.base_addr);
    let offset = region.ptr_to_offset(ptr).unwrap();
    let header = region.read_header_at(offset).unwrap();
    assert_eq!(
        header.tag, 3,
        "opaqueInfo wrapper must use tag 3, got {header:?}"
    );
}

// ---------------------------------------------------------------------------
// Mutual-inductive round-trips (real-Mathlib-import prerequisite).
//
// Lean 4 stdlib/Mathlib relies on MUTUAL inductive blocks (e.g. the
// Even/Odd pair, or the Expr/Level group). A mutual block is two or more
// inductives that:
//   * share the SAME `all_names` list (every inductive in the block lists
//     all the block's type names, in declaration order), and
//   * cross-reference each other through their constructors, so neither can
//     be elaborated in isolation.
//
// Their recursors carry one motive PER inductive in the block, so
// `num_motives` equals the block size (2 for Even/Odd) rather than 1 as for
// a standalone inductive.
//
// These tests pin that the export -> .olean -> re-import path preserves the
// mutual structure: both inductives present, `all_names` round-tripping on
// BOTH of them, and both recursors present with `num_motives == 2`. Without
// them this critical import path was unvalidated.
// ---------------------------------------------------------------------------

/// Construct the `Even`/`Odd` mutual inductive block as kernel values.
///
/// Mirrors the natural-number even/odd predicates:
/// ```text
/// mutual
///   inductive Even : Nat → Prop where
///     | zero : Even 0
///     | succ_odd : {n : Nat} → Odd n → Even (n + 1)
///   inductive Odd : Nat → Prop where
///     | succ_even : {n : Nat} → Even n → Odd (n + 1)
/// end
/// ```
///
/// Returns `(even_ind, odd_ind, ctors, recursors)`. Every inductive carries
/// the SAME `all_names = [Even, Odd]`, and each recursor carries
/// `num_motives = 2` (one motive per inductive in the block).
fn mutual_even_odd() -> (
    InductiveVal,
    InductiveVal,
    Vec<ConstructorVal>,
    Vec<RecursorVal>,
) {
    use clean_kernel::inductive::RecursorArgOrder;

    let even = Name::from_string("Even");
    let odd = Name::from_string("Odd");
    // Shared, order-stable `all` list for the whole mutual block.
    let all_names = vec![even.clone(), odd.clone()];

    // Constructor names.
    let even_zero = even.clone().str("zero");
    let even_succ_odd = even.clone().str("succ_odd");
    let odd_succ_even = odd.clone().str("succ_even");

    // Nat → Prop type former (kept simple; exactness is not what we pin here).
    let nat_to_prop = Expr::type_();

    let even_ind = InductiveVal {
        name: even.clone(),
        level_params: vec![],
        type_: nat_to_prop.clone(),
        num_params: 0,
        num_indices: 1,
        all_names: all_names.clone(),
        constructor_names: vec![even_zero.clone(), even_succ_odd.clone()],
        is_recursive: true,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    };
    let odd_ind = InductiveVal {
        name: odd.clone(),
        level_params: vec![],
        type_: nat_to_prop,
        num_params: 0,
        num_indices: 1,
        all_names: all_names.clone(),
        constructor_names: vec![odd_succ_even.clone()],
        is_recursive: true,
        is_reflexive: false,
        is_large_elim: false,
        is_nested: false,
    };

    // Constructors cross-reference the sibling inductive: Even.succ_odd takes
    // an `Odd n`, Odd.succ_even takes an `Even n`.
    let ctors = vec![
        ConstructorVal {
            name: even_zero,
            inductive_name: even.clone(),
            level_params: vec![],
            type_: Expr::const_(even.clone(), vec![]),
            num_params: 0,
            num_fields: 0,
            constructor_idx: 0,
        },
        ConstructorVal {
            name: even_succ_odd,
            inductive_name: even.clone(),
            level_params: vec![],
            // field of type `Odd n` — cross-reference into the sibling.
            type_: Expr::const_(odd.clone(), vec![]),
            num_params: 0,
            num_fields: 1,
            constructor_idx: 1,
        },
        ConstructorVal {
            name: odd_succ_even,
            inductive_name: odd.clone(),
            level_params: vec![],
            // field of type `Even n` — cross-reference into the sibling.
            type_: Expr::const_(even.clone(), vec![]),
            num_params: 0,
            num_fields: 1,
            constructor_idx: 0,
        },
    ];

    // Mutual recursors: one motive per inductive in the block (2).
    let even_rec = RecursorVal {
        name: even.clone().str("rec"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        inductive_name: even.clone(),
        num_params: 0,
        num_indices: 1,
        num_motives: 2,
        num_minors: 2,
        rules: vec![],
        is_k: false,
    };
    let odd_rec = RecursorVal {
        name: odd.clone().str("rec"),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![Name::from_string("u")],
        type_: Expr::type_(),
        inductive_name: odd,
        num_params: 0,
        num_indices: 1,
        num_motives: 2,
        num_minors: 2,
        rules: vec![],
        is_k: false,
    };

    (even_ind, odd_ind, ctors, vec![even_rec, odd_rec])
}

/// End-to-end: a mutual Even/Odd block must survive
/// export (`export_with_payload`) -> .olean file -> `load_olean_file`
/// with both inductives, both recursors, the shared `all_names`, and the
/// per-block `num_motives` intact.
#[test]
fn test_mutual_inductive_roundtrip_kernel_payload_path() {
    let git_hash = "0dd00dd000000000000000000000000000000000";
    let (even_ind, odd_ind, ctors, recursors) = mutual_even_odd();

    let even_name = even_ind.name.clone();
    let odd_name = odd_ind.name.clone();
    let even_rec_name = even_name.clone().str("rec");
    let odd_rec_name = odd_name.clone().str("rec");

    // const_names must list every constant carried in the payload so the
    // Lean-4 constants array and constNames stay aligned.
    let const_names: Vec<String> = std::iter::once(even_name.to_string())
        .chain(std::iter::once(odd_name.to_string()))
        .chain(ctors.iter().map(|c| c.name.to_string()))
        .chain(recursors.iter().map(|r| r.name.to_string()))
        .collect();
    let const_name_refs: Vec<&str> = const_names.iter().map(String::as_str).collect();

    let payload = CleanPayload {
        constants: vec![],
        inductives: vec![even_ind, odd_ind],
        constructors: ctors,
        recursors,
        structure_fields: vec![],
    };

    let bytes = OleanExporter::export_with_payload(&[], &const_name_refs, &[], git_hash, &payload)
        .expect("export with payload should succeed");

    let dir = tempfile::TempDir::new().expect("tempdir");
    let path = dir.path().join("EvenOdd.olean");
    std::fs::write(&path, &bytes).expect("write olean");

    let mut env = Environment::default();
    crate::load_olean_file(&mut env, &path).expect("load olean file should succeed");

    // (1) Both inductives are present in the re-imported environment.
    let loaded_even = env
        .get_inductive(&even_name)
        .expect("Even inductive must be re-imported from the mutual block");
    let loaded_odd = env
        .get_inductive(&odd_name)
        .expect("Odd inductive must be re-imported from the mutual block");

    // (2) all_names round-trips on BOTH inductives, identically and in order.
    let expected_all = vec![even_name.clone(), odd_name.clone()];
    assert_eq!(
        loaded_even.all_names, expected_all,
        "Even.all_names must round-trip as the full mutual block [Even, Odd]"
    );
    assert_eq!(
        loaded_odd.all_names, expected_all,
        "Odd.all_names must round-trip as the full mutual block [Even, Odd]"
    );
    assert_eq!(
        loaded_even.all_names, loaded_odd.all_names,
        "both members of a mutual block must share the same all_names list"
    );

    // (3) Both recursors are present with one motive per inductive (2).
    let loaded_even_rec = env
        .get_recursor(&even_rec_name)
        .expect("Even.rec recursor must be re-imported");
    let loaded_odd_rec = env
        .get_recursor(&odd_rec_name)
        .expect("Odd.rec recursor must be re-imported");
    assert_eq!(
        loaded_even_rec.num_motives, 2,
        "Even.rec is a mutual recursor: num_motives must be 2 (one per block member)"
    );
    assert_eq!(
        loaded_odd_rec.num_motives, 2,
        "Odd.rec is a mutual recursor: num_motives must be 2 (one per block member)"
    );

    // Constructor cross-references survive too (sanity on the mutual shape).
    assert!(
        env.get_constructor(&even_name.clone().str("succ_odd"))
            .is_some(),
        "Even.succ_odd (references Odd) must be re-imported"
    );
    assert!(
        env.get_constructor(&odd_name.clone().str("succ_even"))
            .is_some(),
        "Odd.succ_even (references Even) must be re-imported"
    );
}

/// Lean-4 constants-array path: `write_inductive_info` / `write_recursor_info`
/// must serialize the mutual `all_names` and per-block `num_motives` so the
/// parser recovers them. This exercises the compacted-region encoding
/// independently of the CleanPayload carrier.
#[test]
fn test_mutual_inductive_roundtrip_lean4_constants_array_path() {
    let (even_ind, odd_ind, _ctors, recursors) = mutual_even_odd();
    let even_name = even_ind.name.to_string();
    let odd_name = odd_ind.name.to_string();
    let even_rec_name = recursors[0].name.to_string();
    let odd_rec_name = recursors[1].name.to_string();

    let mut exporter = OleanExporter::new();
    let even_ptr = exporter
        .write_inductive_info(&even_ind)
        .expect("write Even inductive");
    let odd_ptr = exporter
        .write_inductive_info(&odd_ind)
        .expect("write Odd inductive");
    let even_rec_ptr = exporter
        .write_recursor_info(&recursors[0])
        .expect("write Even.rec");
    let odd_rec_ptr = exporter
        .write_recursor_info(&recursors[1])
        .expect("write Odd.rec");

    let names = [
        even_name.as_str(),
        odd_name.as_str(),
        even_rec_name.as_str(),
        odd_rec_name.as_str(),
    ];
    let ptrs = [even_ptr, odd_ptr, even_rec_ptr, odd_rec_ptr];
    let module_offset = exporter.write_module_data_with_const_ptrs(&names, &ptrs);
    exporter.set_root(module_offset);
    let bytes = exporter
        .finalize("0dd00dd000000000000000000000000000000001")
        .expect("finalize should succeed");

    let parsed = crate::parse_module(&bytes).expect("parse_module should succeed");

    let find_ind = |name: &str| {
        parsed
            .constants
            .iter()
            .find(|c| c.name == name)
            .unwrap_or_else(|| panic!("{name} should be present"))
            .inductive_val
            .clone()
            .unwrap_or_else(|| panic!("{name} should carry inductive_val data"))
    };
    let find_rec = |name: &str| {
        parsed
            .constants
            .iter()
            .find(|c| c.name == name)
            .unwrap_or_else(|| panic!("{name} should be present"))
            .recursor_val
            .clone()
            .unwrap_or_else(|| panic!("{name} should carry recursor_val data"))
    };

    // (1)+(2): both inductives present with the shared all_names [Even, Odd].
    let even_data = find_ind(&even_name);
    let odd_data = find_ind(&odd_name);
    let expected_all = vec![even_name.clone(), odd_name.clone()];
    assert_eq!(
        even_data.all, expected_all,
        "Even.all must round-trip the full mutual block through the compacted region"
    );
    assert_eq!(
        odd_data.all, expected_all,
        "Odd.all must round-trip the full mutual block through the compacted region"
    );

    // (3): both recursors present with num_motives == 2 (one per block member).
    let even_rec_data = find_rec(&even_rec_name);
    let odd_rec_data = find_rec(&odd_rec_name);
    assert_eq!(
        even_rec_data.num_motives, 2,
        "Even.rec num_motives must round-trip as 2 for the mutual block"
    );
    assert_eq!(
        odd_rec_data.num_motives, 2,
        "Odd.rec num_motives must round-trip as 2 for the mutual block"
    );
}

// ---------------------------------------------------------------------------
// Lean 4.8 `InductiveVal` shape (other=5, cs_sz=56) — the four-flag layout.
//
// Two real Lean layouts exist and they disagree about `isNested`:
//   >= 4.9  (6, 64): `numNested : Nat` is the 6th OBJECT field at +48, the
//                    three flags follow at +56, and `isNested = numNested > 0`.
//   <= 4.8  (5, 56): there is no `numNested`. Declaration.lean v4.8.0:220-258
//                    ends `isRec, isUnsafe, isReflexive, isNested` — FOUR raw
//                    flag bytes, and they are the scalar area at +48.
//
// This matters because the pinned bridge toolchain IS v4.8.0
// (vendor/lean-core-oleans, commit df668f00e6c0) and every core inductive it
// ships uses the 4.8 shape: 674 of them across the vendored set. Before the
// exact-layout guard landed, the reader took the >=4.9 offsets on those bytes
// and read all three flags from PAST THE END of a 56-byte object, where
// `.unwrap_or(0)` turned every one into `false`. The guard caught that; this
// test pins the decode that replaced it, including the fourth flag, which the
// first repair still derived from a hardcoded `numNested = 0` and therefore
// always read as `false`.
// ---------------------------------------------------------------------------

/// Assemble one Lean-4.8-shaped `InductiveVal` object and decode it.
///
/// Byte-exact, not produced by our own writer: the point is to pin the layout
/// REAL Lean emits, so a round-trip through Clean's exporter could not catch a
/// disagreement with it.
fn decode_lean48_inductive(flags: [u8; 4]) -> crate::module::InductiveValData {
    const BASE: u64 = 0x1000;
    // Object map: +0 InductiveVal(other=5, cs_sz=56) | +56 ConstantVal(other=3, cs_sz=32)
    let mut data = vec![0u8; 96];
    // InductiveVal header: rc=0, cs_sz=56, other=5, tag=0
    data[4..6].copy_from_slice(&56u16.to_le_bytes());
    data[6] = 5;
    // +8 toConstantVal -> the ConstantVal object at file offset 56
    data[8..16].copy_from_slice(&(BASE + 56).to_le_bytes());
    // +16 numParams, +24 numIndices: boxed scalars, Lean tags them `(n << 1) | 1`
    data[16..24].copy_from_slice(&((2u64 << 1) | 1).to_le_bytes());
    data[24..32].copy_from_slice(&((1u64 << 1) | 1).to_le_bytes());
    // +32 all, +40 ctors: `List.nil` is the tagged scalar 0, not a pointer
    data[32..40].copy_from_slice(&1u64.to_le_bytes());
    data[40..48].copy_from_slice(&1u64.to_le_bytes());
    // +48.. the FOUR flags: isRec, isUnsafe, isReflexive, isNested
    data[48..52].copy_from_slice(&flags);
    // ConstantVal header at +56: rc=0, cs_sz=32, other=3
    data[60..62].copy_from_slice(&32u16.to_le_bytes());
    data[62] = 3;

    let region = CompactedRegion::new(&data, BASE);
    region
        .read_inductive_val_data(0)
        .expect("Lean 4.8 InductiveVal must decode")
}

#[test]
fn lean48_inductive_val_decodes_all_four_flags() {
    // All clear — the common case (655 of the 674 vendored 4.8 inductives).
    let d = decode_lean48_inductive([0, 0, 0, 0]);
    assert_eq!(
        (d.is_rec, d.is_unsafe, d.is_reflexive, d.is_nested),
        (false, false, false, false)
    );
    assert_eq!(
        (d.num_params, d.num_indices),
        (2, 1),
        "scalars must survive the 4.8 offsets"
    );

    // Each flag independently, so a wrong offset shows up as the WRONG flag
    // rather than as a blanket failure. `isUnsafe` is the one that carries
    // kernel-declaration authority.
    for (i, name) in ["isRec", "isUnsafe", "isReflexive", "isNested"]
        .iter()
        .enumerate()
    {
        let mut flags = [0u8; 4];
        flags[i] = 1;
        let d = decode_lean48_inductive(flags);
        let got = [d.is_rec, d.is_unsafe, d.is_reflexive, d.is_nested];
        for (j, actual) in got.iter().enumerate() {
            assert_eq!(
                *actual,
                i == j,
                "setting {name} (flag byte +{i}) lit flag {j} instead; the 4.8 flag \
                 offsets are misaligned"
            );
        }
    }

    // The two multi-flag shapes that actually occur in the vendored set:
    // `01 00 01 00` (isRec + isReflexive, x2 in Init/WF — well-founded
    // recursion's `Acc` is reflexive) and `01 00 00 01` (isRec + isNested, x1
    // in Init/Prelude). The second is the case the first repair got wrong.
    let d = decode_lean48_inductive([1, 0, 1, 0]);
    assert_eq!((d.is_rec, d.is_reflexive, d.is_nested), (true, true, false));
    let d = decode_lean48_inductive([1, 0, 0, 1]);
    assert_eq!(
        (d.is_rec, d.is_reflexive, d.is_nested),
        (true, false, true),
        "isNested must come from the fourth flag byte, not from a hardcoded numNested = 0"
    );
}

#[test]
fn lean48_inductive_val_rejects_a_non_bool_flag() {
    // Fail closed on anything outside {0, 1}: the whole reason the exact-domain
    // check exists is that an unrecognized encoding must not resolve to
    // `isUnsafe = false`.
    const BASE: u64 = 0x1000;
    let mut data = vec![0u8; 96];
    data[4..6].copy_from_slice(&56u16.to_le_bytes());
    data[6] = 5;
    data[8..16].copy_from_slice(&(BASE + 56).to_le_bytes());
    data[16..24].copy_from_slice(&1u64.to_le_bytes());
    data[24..32].copy_from_slice(&1u64.to_le_bytes());
    data[32..40].copy_from_slice(&1u64.to_le_bytes());
    data[40..48].copy_from_slice(&1u64.to_le_bytes());
    data[49] = 2; // isUnsafe = 2 is not a Bool
    data[60..62].copy_from_slice(&32u16.to_le_bytes());
    data[62] = 3;
    let region = CompactedRegion::new(&data, BASE);
    let err = region
        .read_inductive_val_data(0)
        .expect_err("a non-Bool flag must fail closed");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("isUnsafe"),
        "the error must name the offending flag: {msg}"
    );
}
