// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structure and class command elaboration.

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_extend::{
    detect_circular_extension, flatten_parents, generate_parent_coercions,
};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

fn type_expr() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn nat_type(env: &mut Environment) -> Expr {
    if env.get_inductive(&Name::from_string("Nat")).is_none() {
        env.init_nat().ok();
    }
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Helper: create a StructField with default binder info and no default value.
fn simple_field(name: &str, type_: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: None,
        binder_info: BinderInfo::Default,
        auto_param: false,
    }
}

/// Helper: create a simple non-class StructDef with no params/parents.
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

#[test]
fn test_simple_structure_generates_inductive_and_projections() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = simple_struct(
        "Point",
        vec![simple_field("x", nat.clone()), simple_field("y", nat)],
    );

    let decls = elaborate_structure(&def, &mut env).expect("should elaborate");
    assert_eq!(decls.len(), 2, "expected 2 projections");

    let ind = env
        .get_inductive(&Name::from_string("Point"))
        .expect("Point inductive");
    assert_eq!(ind.num_params, 0);
    assert_eq!(ind.constructor_names.len(), 1);
    assert_eq!(ind.constructor_names[0], Name::from_string("Point.mk"));

    let fields = env
        .get_structure_field_names(&Name::from_string("Point"))
        .expect("Point fields");
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0], Name::from_string("x"));
    assert_eq!(fields[1], Name::from_string("y"));
}

#[test]
fn test_structure_with_default_values() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = StructDef {
        name: Name::from_string("Config"),
        universe_params: vec![],
        params: vec![],
        fields: vec![
            StructField {
                default_value: Some(Expr::nat_lit(80)),
                ..simple_field("width", nat.clone())
            },
            StructField {
                default_value: Some(Expr::nat_lit(24)),
                ..simple_field("height", nat)
            },
        ],
        parents: vec![],
        is_class: false,
    };

    let decls = elaborate_structure(&def, &mut env).expect("elaborate with defaults");
    assert_eq!(decls.len(), 2);
    assert!(env.get_inductive(&Name::from_string("Config")).is_some());
}

#[test]
fn test_class_structure_registers_as_typeclass() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = StructDef {
        is_class: true,
        ..simple_struct("MyClass", vec![simple_field("val", nat)])
    };

    elaborate_structure(&def, &mut env).expect("elaborate class");
    assert!(env.is_class(&Name::from_string("MyClass")));
}

#[test]
fn test_structure_extends_parent_includes_parent_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    elaborate_structure(
        &simple_struct("Base", vec![simple_field("id", nat)]),
        &mut env,
    )
    .expect("elaborate Base");

    let parent_fields = flatten_parents(&[Name::from_string("Base")], &env).expect("flatten");
    assert_eq!(parent_fields.len(), 1);
    assert_eq!(parent_fields[0].name, Name::from_string("id"));
}

#[test]
fn test_multiple_parent_extension() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    elaborate_structure(
        &simple_struct("ParentA", vec![simple_field("a_field", nat.clone())]),
        &mut env,
    )
    .expect("elaborate ParentA");
    elaborate_structure(
        &simple_struct("ParentB", vec![simple_field("b_field", nat)]),
        &mut env,
    )
    .expect("elaborate ParentB");

    let fields = flatten_parents(
        &[Name::from_string("ParentA"), Name::from_string("ParentB")],
        &env,
    )
    .expect("flatten multiple");
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].name, Name::from_string("a_field"));
    assert_eq!(fields[1].name, Name::from_string("b_field"));
}

#[test]
fn test_diamond_inheritance_deduplicates_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);

    // Two parents each have "shared" + unique field
    let left_fields = vec![
        simple_field("shared", nat.clone()),
        simple_field("left_only", nat.clone()),
    ];
    let right_fields = vec![
        simple_field("shared", nat.clone()),
        simple_field("right_only", nat),
    ];
    elaborate_structure(&simple_struct("Left", left_fields), &mut env).expect("elaborate Left");
    elaborate_structure(&simple_struct("Right", right_fields), &mut env).expect("elaborate Right");

    let fields = flatten_parents(
        &[Name::from_string("Left"), Name::from_string("Right")],
        &env,
    )
    .expect("flatten diamond");

    // "shared" from Left, "left_only", "right_only" (shared deduplicated)
    assert_eq!(fields.len(), 3);
    let names: Vec<String> = fields.iter().map(|f| f.name.to_string()).collect();
    assert!(names.contains(&"shared".to_string()));
    assert!(names.contains(&"left_only".to_string()));
    assert!(names.contains(&"right_only".to_string()));
}

#[test]
fn test_projection_declarations_have_correct_names() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = simple_struct(
        "Pair",
        vec![simple_field("fst", nat.clone()), simple_field("snd", nat)],
    );

    let decls = elaborate_structure(&def, &mut env).expect("elaborate Pair");
    assert_eq!(decls.len(), 2);

    let names: Vec<String> = decls
        .iter()
        .map(|d| match d {
            clean_kernel::Declaration::Definition { name, .. } => name.to_string(),
            _ => String::new(),
        })
        .collect();
    assert!(
        names.iter().any(|n| n.contains("fst")),
        "missing fst: {names:?}"
    );
    assert!(
        names.iter().any(|n| n.contains("snd")),
        "missing snd: {names:?}"
    );
}

#[test]
fn test_circular_extension_detected() {
    let env = Environment::new();
    let result = detect_circular_extension(
        &Name::from_string("SelfRef"),
        &[Name::from_string("SelfRef")],
        &env,
    );
    assert!(result.is_err(), "should detect direct circular extension");
}

#[test]
fn test_flatten_unknown_parent_returns_error() {
    let env = Environment::new();
    let result = flatten_parents(&[Name::from_string("NonExistent")], &env);
    assert!(result.is_err(), "should error on unknown parent");
}

#[test]
fn test_parametric_structure_with_type_param() {
    let mut env = Environment::new();
    let def = StructDef {
        name: Name::from_string("Wrapper"),
        universe_params: vec![],
        params: vec![(Name::from_string("α"), type_expr(), BinderInfo::Implicit)],
        fields: vec![simple_field("val", Expr::bvar(0))],
        parents: vec![],
        is_class: false,
    };

    let decls = elaborate_structure(&def, &mut env).expect("elaborate parametric");
    assert_eq!(decls.len(), 1);

    let ind = env
        .get_inductive(&Name::from_string("Wrapper"))
        .expect("Wrapper inductive");
    assert_eq!(ind.num_params, 1);
}

#[test]
fn test_parent_coercion_generation() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);

    elaborate_structure(
        &simple_struct("Animal", vec![simple_field("legs", nat.clone())]),
        &mut env,
    )
    .expect("elaborate Animal");

    let child_def = StructDef {
        parents: vec![Name::from_string("Animal")],
        ..simple_struct(
            "Dog",
            vec![
                simple_field("legs", nat.clone()),
                simple_field("breed", nat),
            ],
        )
    };
    elaborate_structure(&child_def, &mut env).expect("elaborate Dog");

    let coercions = generate_parent_coercions(
        &Name::from_string("Dog"),
        &[],
        &[],
        &[Name::from_string("Animal")],
        &env,
    );
    assert_eq!(coercions.len(), 1, "should generate 1 coercion");

    match &coercions[0] {
        clean_kernel::Declaration::Definition { name, .. } => {
            assert!(name.to_string().contains("toAnimal"), "got: {name}");
        }
        _ => panic!("expected Definition declaration"),
    }
}
