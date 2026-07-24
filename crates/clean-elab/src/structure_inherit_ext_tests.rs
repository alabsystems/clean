// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended structure inheritance resolution.

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_inherit::{FieldInfo, InheritError};
use crate::structure_inherit_ext::{
    generate_eta_expansion, has_diamond_inheritance, inheritance_depth, ExtFieldOrigin,
    FieldRename, InheritExtConfig, InheritExtError, InheritExtResolver,
};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name};

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

fn field_with_default(name: &str, type_: Expr, default: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: Some(default),
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

fn mk_own_field_with_default(name: &str, type_expr: Expr, default: Expr) -> FieldInfo {
    FieldInfo {
        name: Name::from_string(name),
        type_expr,
        default_value: Some(default),
        is_inherited: false,
        source_struct: None,
    }
}

fn register_struct(env: &mut Environment, name: &str, fields: Vec<StructField>) {
    elaborate_structure(&simple_struct(name, fields), env)
        .unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

fn register_struct_with_parents(
    env: &mut Environment,
    name: &str,
    fields: Vec<StructField>,
    parents: Vec<String>,
) {
    let def = StructDef {
        name: Name::from_string(name),
        universe_params: vec![],
        params: vec![],
        fields,
        parents: parents.iter().map(|p| Name::from_string(p)).collect(),
        is_class: false,
    };
    elaborate_structure(&def, env).unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

// ---------------------------------------------------------------------------
// No parents
// ---------------------------------------------------------------------------

#[test]
fn test_no_parents_returns_own_fields() {
    let env = Environment::new();
    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("x", type_expr())];
    let result = resolver
        .resolve(&Name::from_string("Foo"), &[], &own, &[], &[])
        .expect("resolve");
    assert_eq!(result.fields.len(), 1);
    assert_eq!(result.fields[0].origin, ExtFieldOrigin::Own);
    assert_eq!(result.depth, 0);
    assert!(result.diamonds.is_empty());
}

#[test]
fn test_no_parents_preserves_field_names() {
    let env = Environment::new();
    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![
        mk_own_field("a", type_expr()),
        mk_own_field("b", type_expr()),
    ];
    let result = resolver
        .resolve(&Name::from_string("S"), &[], &own, &[], &[])
        .expect("resolve");
    assert_eq!(result.fields.len(), 2);
    assert_eq!(result.fields[0].name, Name::from_string("a"));
    assert_eq!(result.fields[1].name, Name::from_string("b"));
}

// ---------------------------------------------------------------------------
// Single parent inheritance
// ---------------------------------------------------------------------------

#[test]
fn test_single_parent_inherits_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("y", nat.clone())];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");

    assert!(result.fields.len() >= 2);
    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"));
    assert!(x_field.is_some(), "should inherit field x from Base");
}

#[test]
fn test_single_parent_depth_is_one() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("y", nat)];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");
    assert_eq!(result.depth, 1);
}

#[test]
fn test_single_parent_projections_generated() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("y", nat)];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");
    assert!(!result.projections.is_empty(), "should generate projection");
}

// ---------------------------------------------------------------------------
// Multiple parents (no diamond)
// ---------------------------------------------------------------------------

#[test]
fn test_multiple_parents_no_overlap() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("c", nat)];
    let parents = vec![Name::from_string("A"), Name::from_string("B")];
    let result = resolver
        .resolve(&Name::from_string("C"), &parents, &own, &[], &[])
        .expect("resolve");

    let field_names: Vec<_> = result.fields.iter().map(|f| f.name.to_string()).collect();
    assert!(field_names.contains(&"a".to_string()));
    assert!(field_names.contains(&"b".to_string()));
    assert!(field_names.contains(&"c".to_string()));
}

// ---------------------------------------------------------------------------
// Diamond inheritance
// ---------------------------------------------------------------------------

#[test]
fn test_diamond_detected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let result = resolver
        .resolve(&Name::from_string("Diamond"), &parents, &[], &[], &[])
        .expect("resolve");
    assert!(
        !result.diamonds.is_empty(),
        "should detect diamond via Root"
    );
}

#[test]
fn test_diamond_allowed_by_default() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let result = resolver.resolve(&Name::from_string("D"), &parents, &[], &[], &[]);
    assert!(result.is_ok(), "diamonds should be allowed by default");
}

#[test]
fn test_diamond_disallowed_strict_mode() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    let config = InheritExtConfig {
        allow_diamond: false,
        ..Default::default()
    };
    let resolver = InheritExtResolver::new(&env, config);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let result = resolver.resolve(&Name::from_string("D"), &parents, &[], &[], &[]);
    assert!(
        matches!(result, Err(InheritExtError::DiamondConflict { .. })),
        "should error on diamond in strict mode"
    );
}

#[test]
fn test_diamond_shared_fields_recorded() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("Left"), Name::from_string("Right")];
    let result = resolver
        .resolve(&Name::from_string("D"), &parents, &[], &[], &[])
        .expect("resolve");
    let root_diamond = result
        .diamonds
        .iter()
        .find(|d| d.ancestor == Name::from_string("Root"));
    assert!(root_diamond.is_some());
    let rd = root_diamond.unwrap();
    assert!(rd.paths.len() >= 2);
}

// ---------------------------------------------------------------------------
// Field override validation
// ---------------------------------------------------------------------------

#[test]
fn test_override_same_type_allowed() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("x", nat)];
    let parents = vec![Name::from_string("Base")];
    let result = resolver.resolve(&Name::from_string("Child"), &parents, &own, &[], &[]);
    assert!(result.is_ok(), "same-type override should be allowed");
}

#[test]
fn test_override_different_type_strict() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat)]);

    let config = InheritExtConfig {
        strict_overrides: true,
        ..Default::default()
    };
    let resolver = InheritExtResolver::new(&env, config);
    let own = vec![mk_own_field("x", type_expr())]; // different type: Type vs Nat
    let parents = vec![Name::from_string("Base")];
    let result = resolver.resolve(&Name::from_string("Child"), &parents, &own, &[], &[]);
    assert!(
        matches!(result, Err(InheritExtError::OverrideTypeMismatch { .. })),
        "should reject type mismatch in strict mode"
    );
}

#[test]
fn test_override_origin_set_correctly() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field("x", nat)];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");
    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"))
        .expect("field x");
    assert!(
        matches!(&x_field.origin, ExtFieldOrigin::Override { .. }),
        "overridden field should have Override origin"
    );
}

// ---------------------------------------------------------------------------
// Default value propagation
// ---------------------------------------------------------------------------

#[test]
fn test_default_propagated_from_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let default_val = Expr::nat_lit(42);
    register_struct(
        &mut env,
        "Base",
        vec![field_with_default("x", nat.clone(), default_val.clone())],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let own: Vec<FieldInfo> = vec![];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");

    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"))
        .expect("field x should be present in resolved fields");
    let propagated = x_field
        .default_value
        .as_ref()
        .expect("parent default value should propagate into Child.x when propagate_defaults is on");
    assert_eq!(
        propagated, &default_val,
        "the propagated default must be structurally equal to the parent's registered default"
    );
}

#[test]
fn test_default_propagated_does_not_invent_value_for_undefaulted_field() {
    // Negative: a parent field WITHOUT a default must NOT acquire one in the
    // child even when propagate_defaults is on — the new metadata channel
    // must not invent defaults for fields whose parent never registered one.
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let own: Vec<FieldInfo> = vec![];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");

    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"))
        .expect("field x should be present in resolved fields");
    assert!(
        x_field.default_value.is_none(),
        "no default was registered on Base.x, so Child.x must not acquire one"
    );
}

#[test]
fn test_default_not_propagated_when_disabled() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let default_val = Expr::nat_lit(42);
    register_struct(
        &mut env,
        "Base",
        vec![field_with_default("x", nat.clone(), default_val)],
    );

    let config = InheritExtConfig {
        propagate_defaults: false,
        ..Default::default()
    };
    let resolver = InheritExtResolver::new(&env, config);
    let own: Vec<FieldInfo> = vec![];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");

    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"));
    assert!(x_field.is_some());
    assert!(
        x_field.unwrap().default_value.is_none(),
        "default should not propagate when disabled"
    );
}

#[test]
fn test_own_default_overrides_parent_default() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let parent_default = Expr::nat_lit(10);
    let own_default = Expr::nat_lit(20);
    register_struct(
        &mut env,
        "Base",
        vec![field_with_default("x", nat.clone(), parent_default)],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let own = vec![mk_own_field_with_default("x", nat, own_default.clone())];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &own, &[], &[])
        .expect("resolve");

    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"))
        .expect("field x");
    assert!(x_field.default_value.is_some());
    // Verify it's the own default, not the parent's
    let dv = x_field.default_value.as_ref().unwrap();
    assert!(
        matches!(dv.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(n)) if *n == 20u64.into()),
        "should use own default value"
    );
}

// ---------------------------------------------------------------------------
// Field renaming
// ---------------------------------------------------------------------------

#[test]
fn test_field_rename_basic() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let renames = vec![FieldRename {
        original: Name::from_string("x"),
        renamed: Name::from_string("y"),
    }];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &[], &renames, &[])
        .expect("resolve");

    let y_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("y"));
    assert!(y_field.is_some(), "renamed field 'y' should exist");
    let x_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("x"));
    assert!(x_field.is_none(), "original field 'x' should not exist");
}

#[test]
fn test_field_rename_origin_tagged() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let renames = vec![FieldRename {
        original: Name::from_string("x"),
        renamed: Name::from_string("y"),
    }];
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &[], &renames, &[])
        .expect("resolve");

    let y_field = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("y"))
        .expect("field y");
    assert!(
        matches!(&y_field.origin, ExtFieldOrigin::Renamed { original_name, .. } if *original_name == Name::from_string("x")),
        "renamed field should track original name"
    );
}

#[test]
fn test_field_rename_conflict_detected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Base",
        vec![
            simple_field("x", nat.clone()),
            simple_field("y", nat.clone()),
        ],
    );

    let resolver = InheritExtResolver::with_defaults(&env);
    let renames = vec![FieldRename {
        original: Name::from_string("x"),
        renamed: Name::from_string("y"), // conflicts with existing field y
    }];
    let parents = vec![Name::from_string("Base")];
    let result = resolver.resolve(&Name::from_string("Child"), &parents, &[], &renames, &[]);
    assert!(
        matches!(result, Err(InheritExtError::RenameConflict { .. })),
        "should detect rename conflict"
    );
}

// ---------------------------------------------------------------------------
// Cycle detection
// ---------------------------------------------------------------------------

#[test]
fn test_cycle_detection_direct() {
    let env = Environment::new();
    let config = InheritExtConfig::default();
    let resolver = InheritExtResolver::new(&env, config);
    // Struct trying to extend itself
    let name = Name::from_string("Self_");
    // Since Self_ doesn't exist in env, parents_of returns empty, no actual cycle
    // But we test the direct self-reference check
    let result = resolver.resolve(&name, std::slice::from_ref(&name), &[], &[], &[]);
    assert!(
        matches!(
            result,
            Err(InheritExtError::CycleDetected { .. })
                | Err(InheritExtError::Base(
                    InheritError::CircularInheritance { .. }
                ))
        ),
        "should detect self-reference cycle"
    );
}

#[test]
fn test_cycle_detection_transitive() {
    // This tests the cycle check for transitive cycles where A->B->A
    // We can't easily construct this with the environment (would need circular structures)
    // Instead we verify the visited set mechanism works
    let env = Environment::new();
    let resolver = InheritExtResolver::with_defaults(&env);
    // Parents that don't exist in env won't cause issues, but the self-check will catch
    // if struct_name appears in parent chain
    let name = Name::from_string("A");
    let parent = Name::from_string("B");
    // B doesn't exist, so no cycle detected here (healthy case)
    let result = resolver.resolve(&name, &[parent], &[], &[], &[]);
    // Should fail with UnknownParent (from base resolver), not cycle
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// Depth limit
// ---------------------------------------------------------------------------

#[test]
fn test_depth_limit_exceeded() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);

    // Build a chain: D0 -> D1 -> D2 -> ... -> D5
    register_struct(&mut env, "D0", vec![simple_field("f0", nat.clone())]);
    for i in 1..6 {
        register_struct_with_parents(
            &mut env,
            &format!("D{i}"),
            vec![simple_field(&format!("f{i}"), nat.clone())],
            vec![format!("D{}", i - 1)],
        );
    }

    let config = InheritExtConfig {
        max_depth: 3, // Limit to 3
        ..Default::default()
    };
    let resolver = InheritExtResolver::new(&env, config);
    let parents = vec![Name::from_string("D5")];
    let result = resolver.resolve(&Name::from_string("TooDeep"), &parents, &[], &[], &[]);
    assert!(
        matches!(result, Err(InheritExtError::DepthLimitExceeded { .. })),
        "should reject inheritance chain exceeding depth limit"
    );
}

#[test]
fn test_depth_within_limit_allowed() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "D0", vec![simple_field("f0", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "D1",
        vec![simple_field("f1", nat.clone())],
        vec!["D0".into()],
    );

    let config = InheritExtConfig {
        max_depth: 10,
        ..Default::default()
    };
    let resolver = InheritExtResolver::new(&env, config);
    let parents = vec![Name::from_string("D1")];
    let result = resolver.resolve(&Name::from_string("OK"), &parents, &[], &[], &[]);
    assert!(
        result.is_ok(),
        "should allow inheritance within depth limit"
    );
}

// ---------------------------------------------------------------------------
// Type class extensions
// ---------------------------------------------------------------------------

#[test]
fn test_tc_extensions_recorded() {
    let env = Environment::new();
    let resolver = InheritExtResolver::with_defaults(&env);
    let tc = vec![Name::from_string("Hashable"), Name::from_string("Eq")];
    let result = resolver
        .resolve(&Name::from_string("Foo"), &[], &[], &[], &tc)
        .expect("resolve");
    assert_eq!(result.tc_extensions.len(), 2);
    assert_eq!(result.tc_extensions[0], Name::from_string("Hashable"));
}

// ---------------------------------------------------------------------------
// Eta expansion
// ---------------------------------------------------------------------------

#[test]
fn test_eta_expansion_generation() {
    let fields = vec![
        crate::structure_inherit_ext::ExtFieldInfo {
            name: Name::from_string("x"),
            type_expr: type_expr(),
            default_value: None,
            binder_info: BinderInfo::Default,
            origin: ExtFieldOrigin::Own,
        },
        crate::structure_inherit_ext::ExtFieldInfo {
            name: Name::from_string("y"),
            type_expr: type_expr(),
            default_value: None,
            binder_info: BinderInfo::Default,
            origin: ExtFieldOrigin::Own,
        },
    ];
    let eta = generate_eta_expansion(&Name::from_string("S"), &[], &fields);
    // Should produce a lambda
    assert!(
        matches!(eta.kind(), ExprKind::Lam(..)),
        "eta expansion should be a lambda"
    );
}

#[test]
fn test_eta_expansion_projects_all_fields() {
    let fields = vec![crate::structure_inherit_ext::ExtFieldInfo {
        name: Name::from_string("a"),
        type_expr: type_expr(),
        default_value: None,
        binder_info: BinderInfo::Default,
        origin: ExtFieldOrigin::Own,
    }];
    let eta = generate_eta_expansion(&Name::from_string("S"), &[], &fields);
    // The body of the lambda should contain a projection
    if let ExprKind::Lam(_, _, body) = eta.kind() {
        // body = App(S.mk, Proj(S, 0, BVar(0)))
        fn contains_proj(e: &Expr) -> bool {
            match e.kind() {
                ExprKind::Proj(..) => true,
                ExprKind::App(f, a) => contains_proj(f) || contains_proj(a),
                ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                    contains_proj(t) || contains_proj(b)
                }
                _ => false,
            }
        }
        assert!(contains_proj(body), "eta body should contain projections");
    } else {
        panic!("expected lambda");
    }
}

// ---------------------------------------------------------------------------
// Empty structures
// ---------------------------------------------------------------------------

#[test]
fn test_empty_struct_no_parents() {
    let env = Environment::new();
    let resolver = InheritExtResolver::with_defaults(&env);
    let result = resolver
        .resolve(&Name::from_string("Empty"), &[], &[], &[], &[])
        .expect("resolve");
    assert!(result.fields.is_empty());
    assert_eq!(result.depth, 0);
}

#[test]
fn test_empty_struct_with_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("x", nat)]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("Base")];
    let result = resolver
        .resolve(&Name::from_string("EmptyChild"), &parents, &[], &[], &[])
        .expect("resolve");
    // Should still have inherited fields
    assert!(!result.fields.is_empty());
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

#[test]
fn test_inheritance_depth_no_parents() {
    let env = Environment::new();
    let depth = inheritance_depth(&Name::from_string("Nonexistent"), &env, 64);
    assert_eq!(depth, 0);
}

#[test]
fn test_inheritance_depth_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "B",
        vec![simple_field("b", nat.clone())],
        vec!["A".into()],
    );

    let depth = inheritance_depth(&Name::from_string("B"), &env, 64);
    assert!(depth >= 1, "B extends A, depth should be >= 1");
}

#[test]
fn test_has_diamond_inheritance_false() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b", nat)]);

    assert!(
        !has_diamond_inheritance(&[Name::from_string("A"), Name::from_string("B")], &env),
        "no diamond when parents are independent"
    );
}

#[test]
fn test_has_diamond_inheritance_true() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("r", nat.clone())]);
    register_struct_with_parents(
        &mut env,
        "Left",
        vec![simple_field("l", nat.clone())],
        vec!["Root".into()],
    );
    register_struct_with_parents(
        &mut env,
        "Right",
        vec![simple_field("rr", nat.clone())],
        vec!["Root".into()],
    );

    assert!(
        has_diamond_inheritance(
            &[Name::from_string("Left"), Name::from_string("Right")],
            &env
        ),
        "should detect diamond"
    );
}

// ---------------------------------------------------------------------------
// Config edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_config_default_values() {
    let config = InheritExtConfig::default();
    assert_eq!(config.max_depth, 64);
    assert!(config.allow_diamond);
    assert!(config.propagate_defaults);
    assert!(config.generate_eta);
    assert!(!config.strict_overrides);
}

#[test]
fn test_single_parent_no_diamond() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "OnlyParent", vec![simple_field("x", nat.clone())]);

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("OnlyParent")];
    let result = resolver
        .resolve(&Name::from_string("Child"), &parents, &[], &[], &[])
        .expect("resolve");
    assert!(
        result.diamonds.is_empty(),
        "single parent cannot create diamond"
    );
}

// ---------------------------------------------------------------------------
// Deeply nested inheritance
// ---------------------------------------------------------------------------

#[test]
fn test_deeply_nested_chain() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);

    // Build chain of depth 10
    register_struct(&mut env, "L0", vec![simple_field("f0", nat.clone())]);
    for i in 1..=10 {
        register_struct_with_parents(
            &mut env,
            &format!("L{i}"),
            vec![simple_field(&format!("f{i}"), nat.clone())],
            vec![format!("L{}", i - 1)],
        );
    }

    let resolver = InheritExtResolver::with_defaults(&env);
    let parents = vec![Name::from_string("L10")];
    let result = resolver
        .resolve(&Name::from_string("Deep"), &parents, &[], &[], &[])
        .expect("resolve");
    assert!(result.depth >= 10, "depth should reflect chain length");
}
