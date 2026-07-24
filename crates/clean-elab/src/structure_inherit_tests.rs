// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structure inheritance resolution.

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_inherit::{FieldInfo, InheritError, InheritanceResolver};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn type_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn nat_type(env: &mut Environment) -> Expr {
    if env.get_inductive(&Name::from_string("Nat")).is_none() {
        env.init_nat().ok();
    }
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn simple_field(name: &str, type_: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: None,
        binder_info: BinderInfo::Default,
        auto_param: false,
    }
}

fn simple_struct(name: &str, fields: Vec<StructField>) -> StructDef {
    StructDef {
        name: Name::from_string(name),
        universe_params: vec![],
        params: vec![],
        fields,
        parents: vec![],
        is_class: false,
    }
}

fn mk_own_field(name: &str, type_expr: Expr) -> FieldInfo {
    FieldInfo {
        name: Name::from_string(name),
        type_expr,
        default_value: None,
        is_inherited: false,
        source_struct: None,
    }
}

fn register_struct(env: &mut Environment, name: &str, fields: Vec<StructField>) {
    elaborate_structure(&simple_struct(name, fields), env)
        .unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

// ---------------------------------------------------------------------------
// Single parent
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_single_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let parents = resolver
        .resolve_parents(&[Name::from_string("Base")])
        .expect("resolve parents");

    assert_eq!(parents.len(), 1);
    assert_eq!(parents[0].name, Name::from_string("Base"));
    assert_eq!(parents[0].fields.len(), 1);
    assert_eq!(parents[0].fields[0].name, Name::from_string("x"));
    assert!(parents[0].fields[0].is_inherited);
}

#[test]
fn test_single_parent_inheritance_result() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Parent", vec![simple_field("a", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let own = vec![mk_own_field("b", nat)];
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Child"),
            &[Name::from_string("Parent")],
            &own,
        )
        .expect("resolve inheritance");

    assert_eq!(result.all_fields.len(), 2);
    assert_eq!(result.all_fields[0].name, Name::from_string("a"));
    assert!(result.all_fields[0].is_inherited);
    assert_eq!(result.all_fields[1].name, Name::from_string("b"));
    assert!(!result.all_fields[1].is_inherited);
}

#[test]
fn test_single_parent_projection() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Mono", vec![simple_field("op", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let own = vec![mk_own_field("inv", nat)];
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Group"),
            &[Name::from_string("Mono")],
            &own,
        )
        .expect("resolve");

    assert_eq!(result.parent_projections.len(), 1);
    let proj = &result.parent_projections[0];
    assert!(proj.name.to_string().contains("toMono"));
    assert_eq!(proj.parent, Name::from_string("Mono"));
    assert_eq!(proj.field_indices, vec![0]);
}

#[test]
fn test_single_parent_coercion() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("val", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Derived"),
            &[Name::from_string("Base")],
            &[mk_own_field("extra", nat)],
        )
        .expect("resolve");

    assert_eq!(result.coercions.len(), 1);
    let coe = &result.coercions[0];
    assert_eq!(coe.from, Name::from_string("Derived"));
    assert_eq!(coe.to, Name::from_string("Base"));
    assert!(coe.projection_name.to_string().contains("toBase"));
}

// ---------------------------------------------------------------------------
// Multiple parents
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_parents() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a_val", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b_val", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("C"),
            &[Name::from_string("A"), Name::from_string("B")],
            &[mk_own_field("c_val", nat)],
        )
        .expect("resolve");

    assert_eq!(result.all_fields.len(), 3);
    assert_eq!(result.parent_projections.len(), 2);
    assert_eq!(result.coercions.len(), 2);
}

#[test]
fn test_multiple_parents_field_ordering() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "P1",
        vec![
            simple_field("f1", nat.clone()),
            simple_field("f2", nat.clone()),
        ],
    );
    register_struct(&mut env, "P2", vec![simple_field("f3", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Kid"),
            &[Name::from_string("P1"), Name::from_string("P2")],
            &[mk_own_field("f4", nat)],
        )
        .expect("resolve");

    let names: Vec<String> = result
        .all_fields
        .iter()
        .map(|f| f.name.to_string())
        .collect();
    assert_eq!(names, vec!["f1", "f2", "f3", "f4"]);
}

// ---------------------------------------------------------------------------
// Field override
// ---------------------------------------------------------------------------

#[test]
fn test_field_override_replaces_inherited() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let custom_type = Expr::sort(Level::zero()); // Prop instead of Nat
    let own = vec![mk_own_field("x", custom_type.clone())];
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Over"),
            &[Name::from_string("Base")],
            &own,
        )
        .expect("resolve");

    assert_eq!(result.all_fields.len(), 1);
    assert!(
        !result.all_fields[0].is_inherited,
        "overridden should not be marked inherited"
    );
    assert_eq!(result.all_fields[0].type_expr, custom_type);
}

#[test]
fn test_field_override_with_additional_own_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Cfg", vec![simple_field("width", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let own = vec![
        mk_own_field("width", Expr::nat_lit(100)),
        mk_own_field("height", nat),
    ];
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Screen"),
            &[Name::from_string("Cfg")],
            &own,
        )
        .expect("resolve");

    assert_eq!(result.all_fields.len(), 2);
    assert_eq!(result.all_fields[0].name, Name::from_string("width"));
    assert_eq!(result.all_fields[1].name, Name::from_string("height"));
}

// ---------------------------------------------------------------------------
// Field conflict detection
// ---------------------------------------------------------------------------

#[test]
fn test_ambiguous_field_from_different_parents_different_types() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let prop = Expr::sort(Level::zero());
    register_struct(&mut env, "L", vec![simple_field("shared", nat)]);
    register_struct(&mut env, "R", vec![simple_field("shared", prop)]);

    let resolver = InheritanceResolver::new(&env);
    // The two parents have "shared" with different types — should be an error
    // because collect_inherited_fields deduplicates by name (first wins), but
    // check_field_conflicts detects the type mismatch when we build the map
    // including all parents' fields before dedup.

    // We test via the low-level API: supply non-deduplicated fields.
    let parents = resolver
        .resolve_parents(&[Name::from_string("L"), Name::from_string("R")])
        .expect("resolve parents");

    // Build full list without dedup for conflict check.
    let all_inherited: Vec<FieldInfo> = parents.iter().flat_map(|p| p.fields.clone()).collect();
    let result = resolver.check_field_conflicts(&[], &all_inherited);
    assert!(result.is_err(), "should detect ambiguous field");
    match result.unwrap_err() {
        InheritError::AmbiguousField { field, .. } => {
            assert_eq!(field, Name::from_string("shared"));
        }
        other => panic!("unexpected error: {other}"),
    }
}

#[test]
fn test_same_field_same_type_no_conflict() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "X", vec![simple_field("v", nat.clone())]);
    register_struct(&mut env, "Y", vec![simple_field("v", nat)]);

    let resolver = InheritanceResolver::new(&env);
    let parents = resolver
        .resolve_parents(&[Name::from_string("X"), Name::from_string("Y")])
        .expect("resolve");
    let all_inherited: Vec<FieldInfo> = parents.iter().flat_map(|p| p.fields.clone()).collect();
    let result = resolver.check_field_conflicts(&[], &all_inherited);
    assert!(result.is_ok(), "same type should not conflict");
}

// ---------------------------------------------------------------------------
// Diamond inheritance
// ---------------------------------------------------------------------------

#[test]
fn test_diamond_deduplicates_shared_field() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Top", vec![simple_field("root", nat.clone())]);
    register_struct(
        &mut env,
        "Left",
        vec![
            simple_field("root", nat.clone()),
            simple_field("l", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "Right",
        vec![
            simple_field("root", nat.clone()),
            simple_field("r", nat.clone()),
        ],
    );

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Bottom"),
            &[Name::from_string("Left"), Name::from_string("Right")],
            &[mk_own_field("own", nat)],
        )
        .expect("resolve diamond");

    let names: Vec<String> = result
        .all_fields
        .iter()
        .map(|f| f.name.to_string())
        .collect();
    // "root" appears once (from Left), "l", "r", "own"
    assert_eq!(names.len(), 4);
    assert_eq!(names.iter().filter(|n| *n == "root").count(), 1);
}

#[test]
fn test_diamond_projections_correct() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "DL",
        vec![
            simple_field("shared", nat.clone()),
            simple_field("dl", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "DR",
        vec![
            simple_field("shared", nat.clone()),
            simple_field("dr", nat.clone()),
        ],
    );

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("DB"),
            &[Name::from_string("DL"), Name::from_string("DR")],
            &[],
        )
        .expect("resolve");

    // Fields: shared(0), dl(1), dr(2)
    assert_eq!(result.parent_projections.len(), 2);
    let left_proj = &result.parent_projections[0];
    assert_eq!(left_proj.field_indices, vec![0, 1]); // shared, dl
    let right_proj = &result.parent_projections[1];
    assert_eq!(right_proj.field_indices, vec![0, 2]); // shared, dr
}

// ---------------------------------------------------------------------------
// Deep chains
// ---------------------------------------------------------------------------

#[test]
fn test_deep_inheritance_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "L0", vec![simple_field("f0", nat.clone())]);
    register_struct(
        &mut env,
        "L1",
        vec![
            simple_field("f0", nat.clone()),
            simple_field("f1", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "L2",
        vec![
            simple_field("f0", nat.clone()),
            simple_field("f1", nat.clone()),
            simple_field("f2", nat.clone()),
        ],
    );

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("L3"),
            &[Name::from_string("L2")],
            &[mk_own_field("f3", nat)],
        )
        .expect("resolve chain");

    assert_eq!(result.all_fields.len(), 4);
    let names: Vec<String> = result
        .all_fields
        .iter()
        .map(|f| f.name.to_string())
        .collect();
    assert_eq!(names, vec!["f0", "f1", "f2", "f3"]);
}

// ---------------------------------------------------------------------------
// Empty parent
// ---------------------------------------------------------------------------

#[test]
fn test_empty_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Empty", vec![]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Child"),
            &[Name::from_string("Empty")],
            &[mk_own_field("x", nat)],
        )
        .expect("resolve");

    assert_eq!(result.all_fields.len(), 1);
    assert_eq!(result.parent_projections.len(), 1);
    assert!(result.parent_projections[0].field_indices.is_empty());
}

// ---------------------------------------------------------------------------
// No parents (pass-through)
// ---------------------------------------------------------------------------

#[test]
fn test_no_parents_returns_own_fields() {
    let env = Environment::new();
    let resolver = InheritanceResolver::new(&env);
    let own = vec![mk_own_field("solo", Expr::sort(Level::zero()))];
    let result = resolver
        .resolve_inheritance(&Name::from_string("Solo"), &[], &own)
        .expect("resolve");

    assert_eq!(result.all_fields.len(), 1);
    assert!(result.parent_projections.is_empty());
    assert!(result.coercions.is_empty());
    assert!(result.parents.is_empty());
}

// ---------------------------------------------------------------------------
// Error cases
// ---------------------------------------------------------------------------

#[test]
fn test_unknown_parent_error() {
    let env = Environment::new();
    let resolver = InheritanceResolver::new(&env);
    let result = resolver.resolve_parents(&[Name::from_string("DoesNotExist")]);
    assert!(result.is_err());
    match result.unwrap_err() {
        InheritError::UnknownParent { name } => {
            assert_eq!(name, Name::from_string("DoesNotExist"));
        }
        other => panic!("unexpected: {other}"),
    }
}

#[test]
fn test_circular_inheritance_detected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "SelfRef", vec![simple_field("val", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver.resolve_inheritance(
        &Name::from_string("SelfRef"),
        &[Name::from_string("SelfRef")],
        &[],
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        InheritError::CircularInheritance { name } => {
            assert_eq!(name, Name::from_string("SelfRef"));
        }
        other => panic!("unexpected: {other}"),
    }
}

// ---------------------------------------------------------------------------
// Universe parameter inheritance
// ---------------------------------------------------------------------------

#[test]
fn test_universe_params_inherited() {
    let mut env = Environment::new();
    let def = StructDef {
        name: Name::from_string("UParent"),
        universe_params: vec![Name::from_string("u")],
        params: vec![(Name::from_string("α"), type_expr(), BinderInfo::Implicit)],
        fields: vec![simple_field("val", Expr::bvar(0))],
        parents: vec![],
        is_class: false,
    };
    elaborate_structure(&def, &mut env).expect("elaborate UParent");

    let resolver = InheritanceResolver::new(&env);
    let parents = resolver
        .resolve_parents(&[Name::from_string("UParent")])
        .expect("resolve");

    assert_eq!(parents[0].universe_params, vec![Name::from_string("u")]);
    assert_eq!(parents[0].num_params, 1);
}

// ---------------------------------------------------------------------------
// Projection naming
// ---------------------------------------------------------------------------

#[test]
fn test_projection_naming_convention() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Monoid", vec![simple_field("op", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Group"),
            &[Name::from_string("Monoid")],
            &[mk_own_field("inv", nat)],
        )
        .expect("resolve");

    assert_eq!(
        result.parent_projections[0].name.to_string(),
        "Group.toMonoid"
    );
}

// ---------------------------------------------------------------------------
// Coercion metadata completeness
// ---------------------------------------------------------------------------

#[test]
fn test_coercion_from_to_correct() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Src", vec![simple_field("s", nat.clone())]);
    register_struct(&mut env, "Src2", vec![simple_field("s2", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Dst"),
            &[Name::from_string("Src"), Name::from_string("Src2")],
            &[mk_own_field("d", nat)],
        )
        .expect("resolve");

    for coe in &result.coercions {
        assert_eq!(coe.from, Name::from_string("Dst"));
    }
    assert_eq!(result.coercions[0].to, Name::from_string("Src"));
    assert_eq!(result.coercions[1].to, Name::from_string("Src2"));
}

// ---------------------------------------------------------------------------
// Inherited field source tracking
// ---------------------------------------------------------------------------

#[test]
fn test_inherited_field_tracks_source() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Origin",
        vec![simple_field("traced", nat.clone())],
    );

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Dest"),
            &[Name::from_string("Origin")],
            &[mk_own_field("local", nat)],
        )
        .expect("resolve");

    let inherited = &result.all_fields[0];
    assert_eq!(
        inherited.source_struct.as_ref(),
        Some(&Name::from_string("Origin"))
    );
    let local = &result.all_fields[1];
    assert!(local.source_struct.is_none());
}

// ---------------------------------------------------------------------------
// Parent info contents
// ---------------------------------------------------------------------------

#[test]
fn test_parent_info_contains_all_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Multi",
        vec![
            simple_field("a", nat.clone()),
            simple_field("b", nat.clone()),
            simple_field("c", nat),
        ],
    );

    let resolver = InheritanceResolver::new(&env);
    let parents = resolver
        .resolve_parents(&[Name::from_string("Multi")])
        .expect("resolve");

    assert_eq!(parents[0].fields.len(), 3);
    let names: Vec<String> = parents[0]
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .collect();
    assert_eq!(names, vec!["a", "b", "c"]);
}

// ---------------------------------------------------------------------------
// Multiple coercion projections distinct
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_parent_projections_have_distinct_names() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Alpha", vec![simple_field("a", nat.clone())]);
    register_struct(&mut env, "Beta", vec![simple_field("b", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(
            &Name::from_string("Gamma"),
            &[Name::from_string("Alpha"), Name::from_string("Beta")],
            &[mk_own_field("g", nat)],
        )
        .expect("resolve");

    let proj_names: Vec<String> = result
        .parent_projections
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    assert_eq!(proj_names.len(), 2);
    assert_ne!(proj_names[0], proj_names[1]);
    assert!(proj_names[0].contains("toAlpha"));
    assert!(proj_names[1].contains("toBeta"));
}

// ---------------------------------------------------------------------------
// Default value propagation
// ---------------------------------------------------------------------------

#[test]
fn test_inherited_field_no_default_value() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Def", vec![simple_field("x", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let result = resolver
        .resolve_inheritance(&Name::from_string("Sub"), &[Name::from_string("Def")], &[])
        .expect("resolve");

    // Inherited fields from the environment do not carry default values
    // (defaults are surface-level, not stored in the kernel inductive).
    assert!(result.all_fields[0].default_value.is_none());
}

// ---------------------------------------------------------------------------
// Resolve inheritance is idempotent
// ---------------------------------------------------------------------------

#[test]
fn test_resolve_twice_same_result() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Idem", vec![simple_field("v", nat.clone())]);

    let resolver = InheritanceResolver::new(&env);
    let own = vec![mk_own_field("w", nat)];
    let r1 = resolver
        .resolve_inheritance(&Name::from_string("T"), &[Name::from_string("Idem")], &own)
        .expect("first");
    let r2 = resolver
        .resolve_inheritance(&Name::from_string("T"), &[Name::from_string("Idem")], &own)
        .expect("second");

    assert_eq!(r1.all_fields.len(), r2.all_fields.len());
    assert_eq!(r1.parent_projections.len(), r2.parent_projections.len());
    assert_eq!(r1.coercions.len(), r2.coercions.len());
}
