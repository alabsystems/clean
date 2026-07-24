// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended structure command elaboration.

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_cmd_ext::{
    collect_subobjects, constructor_name, elaborate_field_update, elaborate_fields,
    elaborate_structure_ext, eta_expand, eta_reduce, generate_constructor_type,
    generate_projectors, generate_recursor_type, merge_inherited_fields, recursor_name,
    reset_stats, resolve_anon_constructor, stats, ElaboratedField, FieldUpdate,
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

fn elab_field(name: &str, type_: Expr) -> ElaboratedField {
    ElaboratedField {
        name: Name::from_string(name),
        type_,
        default_value: None,
        binder_info: BinderInfo::Default,
        is_subobject: false,
    }
}

// ===== 1. Field elaboration =====

#[test]
fn test_elaborate_fields_simple() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = simple_struct(
        "Point",
        vec![simple_field("x", nat.clone()), simple_field("y", nat)],
    );
    let fields = elaborate_fields(&def, &env).expect("should elaborate fields");
    assert_eq!(fields.len(), 2);
    assert_eq!(fields[0].name, Name::from_string("x"));
    assert_eq!(fields[1].name, Name::from_string("y"));
}

#[test]
fn test_elaborate_fields_with_default() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = StructDef {
        name: Name::from_string("Config"),
        universe_params: vec![],
        params: vec![],
        fields: vec![StructField {
            default_value: Some(Expr::nat_lit(42)),
            ..simple_field("width", nat)
        }],
        parents: vec![],
        is_class: false,
    };
    let fields = elaborate_fields(&def, &env).expect("should elaborate with default");
    assert_eq!(fields.len(), 1);
    assert!(fields[0].default_value.is_some());
}

#[test]
fn test_elaborate_fields_subobject_detection() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    elaborate_structure(
        &simple_struct("Inner", vec![simple_field("val", nat.clone())]),
        &mut env,
    )
    .unwrap();

    let inner_type = Expr::const_(Name::from_string("Inner"), vec![]);
    let def = simple_struct(
        "Outer",
        vec![simple_field("data", inner_type), simple_field("count", nat)],
    );
    let fields = elaborate_fields(&def, &env).unwrap();
    assert!(
        fields[0].is_subobject,
        "inner struct field should be subobject"
    );
    assert!(!fields[1].is_subobject, "nat field should not be subobject");
}

#[test]
fn test_elaborate_fields_empty_struct() {
    let env = Environment::new();
    let def = simple_struct("Empty", vec![]);
    let fields = elaborate_fields(&def, &env).expect("should handle empty");
    assert!(fields.is_empty());
}

// ===== 2. Constructor generation =====

#[test]
fn test_constructor_name_generation() {
    let name = constructor_name(&Name::from_string("Point"));
    assert_eq!(name, Name::from_string("Point.mk"));
}

#[test]
fn test_generate_constructor_type_simple() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![elab_field("x", nat.clone()), elab_field("y", nat)];
    let ctor_type = generate_constructor_type(&Name::from_string("Point"), &[], &[], &fields);
    // Should be a pi type wrapping two fields
    match ctor_type.kind() {
        clean_kernel::ExprKind::Pi(_, _, _) => {} // expected
        other => panic!("expected Pi type, got {other:?}"),
    }
}

#[test]
fn test_generate_constructor_type_with_params() {
    let fields = vec![elab_field("val", Expr::bvar(0))];
    let params = vec![(
        Name::from_string("alpha"),
        type_expr(),
        BinderInfo::Implicit,
    )];
    let ctor_type = generate_constructor_type(&Name::from_string("Wrapper"), &[], &params, &fields);
    // Outermost binder should be implicit (param)
    match ctor_type.kind() {
        clean_kernel::ExprKind::Pi(bi, _, _) => {
            assert_eq!(*bi, BinderInfo::Implicit.into());
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

// ===== 3. Projection generation =====

#[test]
fn test_generate_projectors_count() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![elab_field("x", nat.clone()), elab_field("y", nat)];
    let projs = generate_projectors(&Name::from_string("Point"), &[], &[], &fields);
    assert_eq!(projs.len(), 2);
}

#[test]
fn test_generate_projectors_names() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![elab_field("fst", nat.clone()), elab_field("snd", nat)];
    let projs = generate_projectors(&Name::from_string("Pair"), &[], &[], &fields);
    let names: Vec<String> = projs.iter().map(|p| p.name.to_string()).collect();
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
fn test_generate_projectors_field_indices() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![
        elab_field("a", nat.clone()),
        elab_field("b", nat.clone()),
        elab_field("c", nat),
    ];
    let projs = generate_projectors(&Name::from_string("Triple"), &[], &[], &fields);
    assert_eq!(projs[0].field_idx, 0);
    assert_eq!(projs[1].field_idx, 1);
    assert_eq!(projs[2].field_idx, 2);
}

#[test]
fn test_generate_projectors_with_universe_params() {
    let fields = vec![elab_field("val", Expr::bvar(0))];
    let params = vec![(
        Name::from_string("alpha"),
        type_expr(),
        BinderInfo::Implicit,
    )];
    let projs = generate_projectors(
        &Name::from_string("Box"),
        &[Name::from_string("u")],
        &params,
        &fields,
    );
    assert_eq!(projs.len(), 1);
    match &projs[0].decl {
        clean_kernel::Declaration::Definition { level_params, .. } => {
            assert_eq!(level_params.len(), 1);
        }
        _ => panic!("expected Definition"),
    }
}

// ===== 4. Inheritance field merging =====

#[test]
fn test_merge_inherited_fields_no_overlap() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let parent = vec![simple_field("a", nat.clone())];
    let child = vec![simple_field("b", nat)];
    let merged = merge_inherited_fields(&parent, &child, &Name::from_string("Child")).unwrap();
    assert_eq!(merged.len(), 2);
    assert_eq!(merged[0].name, Name::from_string("a"));
    assert_eq!(merged[1].name, Name::from_string("b"));
}

#[test]
fn test_merge_inherited_fields_override() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let parent = vec![simple_field("x", nat.clone())];
    let child = vec![simple_field("x", type_expr())]; // override with Type
    let merged = merge_inherited_fields(&parent, &child, &Name::from_string("Child")).unwrap();
    assert_eq!(merged.len(), 1);
    // Should have the child's type (Type), not parent's (Nat)
    match merged[0].type_.kind() {
        clean_kernel::ExprKind::Sort(_) => {} // expected: Type is Sort
        other => panic!("expected Sort from override, got {other:?}"),
    }
}

#[test]
fn test_merge_inherited_fields_mixed() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let parent = vec![
        simple_field("id", nat.clone()),
        simple_field("name", type_expr()),
    ];
    let child = vec![
        simple_field("name", nat.clone()), // override
        simple_field("extra", nat),
    ];
    let merged = merge_inherited_fields(&parent, &child, &Name::from_string("Child")).unwrap();
    assert_eq!(merged.len(), 3);
    assert_eq!(merged[0].name, Name::from_string("id"));
    assert_eq!(merged[1].name, Name::from_string("name")); // overridden in place
    assert_eq!(merged[2].name, Name::from_string("extra"));
}

// ===== 5. Structure eta expansion =====

#[test]
fn test_eta_expand_produces_constructor_app() {
    let struct_name = Name::from_string("Point");
    let s = Expr::bvar(0);
    let expanded = eta_expand(&struct_name, &[], 2, s);
    // Should be an application of Point.mk with two proj arguments
    let (head, args) = collect_test_app_args(&expanded);
    assert_eq!(args.len(), 2, "eta expansion should have 2 args");
    match head.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Point.mk"));
        }
        _ => panic!("expected Const head"),
    }
}

#[test]
fn test_eta_reduce_round_trip() {
    let struct_name = Name::from_string("Pair");
    let s = Expr::bvar(0);
    let expanded = eta_expand(&struct_name, &[], 2, s.clone());
    let reduced = eta_reduce(&struct_name, 2, &expanded);
    assert!(reduced.is_some(), "should eta-reduce back");
}

#[test]
fn test_eta_reduce_non_eta_returns_none() {
    let struct_name = Name::from_string("Point");
    // Not a valid eta form
    let expr = Expr::nat_lit(42);
    assert!(eta_reduce(&struct_name, 2, &expr).is_none());
}

#[test]
fn test_eta_reduce_wrong_field_count() {
    let struct_name = Name::from_string("Point");
    let s = Expr::bvar(0);
    let expanded = eta_expand(&struct_name, &[], 2, s);
    // Ask for 3 fields — should fail
    assert!(eta_reduce(&struct_name, 3, &expanded).is_none());
}

// ===== 6. Anonymous constructor =====

#[test]
fn test_resolve_anon_constructor_correct_arity() {
    let args = vec![Expr::nat_lit(1), Expr::nat_lit(2)];
    let result = resolve_anon_constructor(&Name::from_string("Point"), &[], &args, 2);
    assert!(result.is_ok());
}

#[test]
fn test_resolve_anon_constructor_wrong_arity() {
    let args = vec![Expr::nat_lit(1)];
    let result = resolve_anon_constructor(&Name::from_string("Point"), &[], &args, 2);
    assert!(result.is_err(), "should reject wrong arity");
}

#[test]
fn test_resolve_anon_constructor_empty() {
    let result = resolve_anon_constructor(&Name::from_string("Unit"), &[], &[], 0);
    assert!(result.is_ok(), "empty struct anon ctor should work");
}

#[test]
fn test_resolve_anon_constructor_produces_named_ctor() {
    let args = vec![Expr::nat_lit(10)];
    let result = resolve_anon_constructor(&Name::from_string("Wrap"), &[], &args, 1).unwrap();
    let (head, app_args) = collect_test_app_args(&result);
    assert_eq!(app_args.len(), 1);
    match head.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Wrap.mk"));
        }
        _ => panic!("expected Const"),
    }
}

// ===== 7. Subobject handling =====

#[test]
fn test_collect_subobjects_detects_nested() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    elaborate_structure(
        &simple_struct("Inner", vec![simple_field("val", nat.clone())]),
        &mut env,
    )
    .unwrap();

    let fields = vec![
        ElaboratedField {
            name: Name::from_string("inner"),
            type_: Expr::const_(Name::from_string("Inner"), vec![]),
            default_value: None,
            binder_info: BinderInfo::Default,
            is_subobject: true,
        },
        elab_field("count", nat),
    ];

    let subs = collect_subobjects(&fields, &env);
    assert_eq!(subs.len(), 1);
    assert_eq!(subs[0].field_name, Name::from_string("inner"));
    assert_eq!(subs[0].target_struct, Name::from_string("Inner"));
    assert_eq!(subs[0].target_field_count, 1);
}

#[test]
fn test_collect_subobjects_empty_when_no_structs() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![elab_field("x", nat.clone()), elab_field("y", nat)];
    let subs = collect_subobjects(&fields, &env);
    assert!(subs.is_empty());
}

// ===== 8. Recursor generation =====

#[test]
fn test_recursor_name_generation() {
    let name = recursor_name(&Name::from_string("Point"));
    assert_eq!(name, Name::from_string("Point.rec"));
}

#[test]
fn test_generate_recursor_type_shape() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let fields = vec![elab_field("x", nat.clone()), elab_field("y", nat)];
    let rec_type = generate_recursor_type(&Name::from_string("Point"), &[], &[], &fields);
    // Should be a Pi type (implicit motive -> minor -> major)
    match rec_type.kind() {
        clean_kernel::ExprKind::Pi(bi, _, _) => {
            assert_eq!(
                *bi,
                BinderInfo::Implicit.into(),
                "motive should be implicit"
            );
        }
        other => panic!("expected Pi for recursor type, got {other:?}"),
    }
}

#[test]
fn test_generate_recursor_type_empty_struct() {
    let fields: Vec<ElaboratedField> = vec![];
    let rec_type = generate_recursor_type(&Name::from_string("Unit"), &[], &[], &fields);
    // Should still produce a Pi type
    match rec_type.kind() {
        clean_kernel::ExprKind::Pi(_, _, _) => {} // ok
        other => panic!("expected Pi, got {other:?}"),
    }
}

// ===== 9. Field update syntax =====

#[test]
fn test_field_update_single() {
    let fields = vec![
        elab_field("x", Expr::const_(Name::from_string("Nat"), vec![])),
        elab_field("y", Expr::const_(Name::from_string("Nat"), vec![])),
    ];
    let source = Expr::bvar(0);
    let updates = vec![FieldUpdate {
        field_name: Name::from_string("x"),
        new_value: Expr::nat_lit(99),
    }];
    let result =
        elaborate_field_update(&Name::from_string("Point"), &[], &fields, source, &updates)
            .unwrap();

    let (head, args) = collect_test_app_args(&result);
    assert_eq!(args.len(), 2);
    match head.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Point.mk"));
        }
        _ => panic!("expected Point.mk"),
    }
}

#[test]
fn test_field_update_unknown_field_errors() {
    let fields = vec![elab_field(
        "x",
        Expr::const_(Name::from_string("Nat"), vec![]),
    )];
    let updates = vec![FieldUpdate {
        field_name: Name::from_string("nonexistent"),
        new_value: Expr::nat_lit(0),
    }];
    let result = elaborate_field_update(
        &Name::from_string("S"),
        &[],
        &fields,
        Expr::bvar(0),
        &updates,
    );
    assert!(result.is_err(), "should reject unknown field");
}

#[test]
fn test_field_update_no_updates() {
    let fields = vec![elab_field(
        "a",
        Expr::const_(Name::from_string("Nat"), vec![]),
    )];
    let source = Expr::bvar(0);
    let result =
        elaborate_field_update(&Name::from_string("S"), &[], &fields, source, &[]).unwrap();
    // With no updates, all args should be projections
    let (_, args) = collect_test_app_args(&result);
    assert_eq!(args.len(), 1);
}

#[test]
fn test_field_update_all_fields() {
    let fields = vec![
        elab_field("x", Expr::const_(Name::from_string("Nat"), vec![])),
        elab_field("y", Expr::const_(Name::from_string("Nat"), vec![])),
    ];
    let updates = vec![
        FieldUpdate {
            field_name: Name::from_string("x"),
            new_value: Expr::nat_lit(1),
        },
        FieldUpdate {
            field_name: Name::from_string("y"),
            new_value: Expr::nat_lit(2),
        },
    ];
    let result = elaborate_field_update(
        &Name::from_string("Point"),
        &[],
        &fields,
        Expr::bvar(0),
        &updates,
    )
    .unwrap();
    let (_, args) = collect_test_app_args(&result);
    assert_eq!(args.len(), 2);
}

// ===== 10. Statistics =====

#[test]
fn test_stats_initial_zero() {
    reset_stats();
    let s = stats();
    assert_eq!(s.structures_elaborated, 0);
    assert_eq!(s.fields_processed, 0);
    assert_eq!(s.projectors_generated, 0);
}

#[test]
fn test_stats_incremented_by_elaboration() {
    reset_stats();
    let baseline = stats();
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = simple_struct(
        "StatTest",
        vec![simple_field("a", nat.clone()), simple_field("b", nat)],
    );
    elaborate_structure_ext(&def, &env).expect("should elaborate");
    let s = stats();
    // Counters are thread-local and reset above, so deltas are exact.
    assert_eq!(s.structures_elaborated, baseline.structures_elaborated + 1);
    assert_eq!(s.fields_processed, baseline.fields_processed + 2);
    assert_eq!(s.projectors_generated, baseline.projectors_generated + 2);
}

#[test]
fn test_stats_accumulate() {
    reset_stats();
    let baseline = stats();
    let mut env = Environment::new();
    let nat = nat_type(&mut env);

    let def1 = simple_struct("S1", vec![simple_field("x", nat.clone())]);
    elaborate_structure_ext(&def1, &env).unwrap();

    let def2 = simple_struct(
        "S2",
        vec![simple_field("a", nat.clone()), simple_field("b", nat)],
    );
    elaborate_structure_ext(&def2, &env).unwrap();

    // Counters are thread-local and reset above, so deltas are exact.
    let s = stats();
    assert_eq!(s.structures_elaborated, baseline.structures_elaborated + 2);
    assert_eq!(s.fields_processed, baseline.fields_processed + 3);
    assert_eq!(s.projectors_generated, baseline.projectors_generated + 3);
}

#[test]
fn test_reset_stats_clears() {
    // Run something first to ensure non-zero
    let env = Environment::new();
    let def = simple_struct("Dummy", vec![]);
    elaborate_structure_ext(&def, &env).unwrap();

    reset_stats();
    let s = stats();
    assert_eq!(s.structures_elaborated, 0);
    assert_eq!(s.fields_processed, 0);
    assert_eq!(s.projectors_generated, 0);
}

// ===== Full pipeline =====

#[test]
fn test_elaborate_structure_ext_full_pipeline() {
    reset_stats();
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = simple_struct(
        "FullTest",
        vec![
            simple_field("x", nat.clone()),
            simple_field("y", nat.clone()),
            simple_field("z", nat),
        ],
    );
    let result = elaborate_structure_ext(&def, &env).expect("full pipeline");
    assert_eq!(result.fields.len(), 3);
    assert_eq!(result.projectors.len(), 3);
    assert!(result.subobjects.is_empty());
    assert_eq!(result.stats.structures_elaborated, 1);
}

#[test]
fn test_elaborate_structure_ext_empty() {
    reset_stats();
    let env = Environment::new();
    let def = simple_struct("Unit", vec![]);
    let result = elaborate_structure_ext(&def, &env).unwrap();
    assert!(result.fields.is_empty());
    assert!(result.projectors.is_empty());
    assert!(result.subobjects.is_empty());
}

#[test]
fn test_elaborate_structure_ext_with_subobject() {
    reset_stats();
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    elaborate_structure(
        &simple_struct("Base", vec![simple_field("id", nat.clone())]),
        &mut env,
    )
    .unwrap();

    let def = simple_struct(
        "Derived",
        vec![
            StructField {
                name: Name::from_string("base"),
                type_: Expr::const_(Name::from_string("Base"), vec![]),
                default_value: None,
                binder_info: BinderInfo::Default,
                auto_param: false,
            },
            simple_field("extra", nat),
        ],
    );
    let result = elaborate_structure_ext(&def, &env).unwrap();
    assert_eq!(result.fields.len(), 2);
    assert_eq!(result.subobjects.len(), 1);
    assert_eq!(
        result.subobjects[0].target_struct,
        Name::from_string("Base")
    );
}

// ===== Additional coverage tests =====

#[test]
fn test_elaborate_fields_preserves_binder_info() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let def = StructDef {
        name: Name::from_string("S"),
        universe_params: vec![],
        params: vec![],
        fields: vec![StructField {
            name: Name::from_string("inst"),
            type_: nat,
            default_value: None,
            binder_info: BinderInfo::InstImplicit,
            auto_param: false,
        }],
        parents: vec![],
        is_class: false,
    };
    let fields = elaborate_fields(&def, &env).unwrap();
    assert_eq!(fields[0].binder_info, BinderInfo::InstImplicit);
}

#[test]
fn test_merge_inherited_fields_empty_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let child = vec![simple_field("x", nat)];
    let merged = merge_inherited_fields(&[], &child, &Name::from_string("S")).unwrap();
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].name, Name::from_string("x"));
}

#[test]
fn test_merge_inherited_fields_empty_child() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let parent = vec![simple_field("x", nat)];
    let merged = merge_inherited_fields(&parent, &[], &Name::from_string("S")).unwrap();
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].name, Name::from_string("x"));
}

#[test]
fn test_eta_expand_single_field() {
    let struct_name = Name::from_string("Wrap");
    let s = Expr::bvar(0);
    let expanded = eta_expand(&struct_name, &[], 1, s);
    let (head, args) = collect_test_app_args(&expanded);
    assert_eq!(args.len(), 1);
    match head.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Wrap.mk"));
        }
        _ => panic!("expected Const"),
    }
}

#[test]
fn test_eta_expand_zero_fields() {
    let struct_name = Name::from_string("Unit");
    let s = Expr::bvar(0);
    let expanded = eta_expand(&struct_name, &[], 0, s);
    // Should just be the constructor with no args
    match expanded.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            assert_eq!(*name, Name::from_string("Unit.mk"));
        }
        _ => panic!("expected bare constructor for zero-field struct"),
    }
}

// ===== Helper =====

fn collect_test_app_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let clean_kernel::ExprKind::App(func, arg) = current.kind() {
        args.push(arg.as_ref());
        current = func;
    }
    args.reverse();
    (current, args)
}
