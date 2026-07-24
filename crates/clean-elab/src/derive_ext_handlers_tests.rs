// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended derive handler registry and handlers.

use clean_kernel::{
    BinderInfo, Environment, Expr, InductiveDecl, InductiveType, InductiveVal, Level, Name,
};

use crate::derive::DeriveError;
use crate::derive_ext_handlers::{
    extract_constructor_info, ConstructorInfo, DeriveBEqExt, DeriveDecidableEqExt,
    DeriveHandlerRegistry, DeriveHashableExt, DeriveInhabitedExt, DeriveOrdExt, DeriveReprExt,
    ExtDeriveHandler,
};

// ---------------------------------------------------------------------------
// Test environment helpers
// ---------------------------------------------------------------------------

/// Build a two-constructor enum: `inductive Color | Red | Blue`.
fn make_color_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    let color_name = Name::from_string("Color");
    let red_name = Name::from_string("Color.Red");
    let blue_name = Name::from_string("Color.Blue");
    let color_type = Expr::sort(Level::succ(Level::zero()));

    let ind_type = InductiveType {
        name: color_name.clone(),
        type_: color_type,
        constructors: vec![
            clean_kernel::Constructor {
                name: red_name,
                type_: Expr::const_(color_name.clone(), vec![]),
            },
            clean_kernel::Constructor {
                name: blue_name,
                type_: Expr::const_(color_name.clone(), vec![]),
            },
        ],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Color inductive");
    let ind_val = env.get_inductive(&color_name).unwrap().clone();
    (env, ind_val)
}

/// Build a single-constructor struct: `structure Point := (x : Nat) (y : Nat)`.
fn make_point_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    env.init_nat().expect("should init Nat");

    let point_name = Name::from_string("Point");
    let mk_name = Name::from_string("Point.mk");
    let nat = Expr::const_str("Nat");
    let point_type = Expr::sort(Level::succ(Level::zero()));

    let mk_type = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::const_(point_name.clone(), vec![]),
        ),
    );

    let ind_type = InductiveType {
        name: point_name.clone(),
        type_: point_type,
        constructors: vec![clean_kernel::Constructor {
            name: mk_name,
            type_: mk_type,
        }],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Point inductive");
    let ind_val = env.get_inductive(&point_name).unwrap().clone();
    (env, ind_val)
}

/// Build an empty inductive (no constructors).
fn make_empty_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    let empty_name = Name::from_string("Empty");

    let ind_type = InductiveType {
        name: empty_name.clone(),
        type_: Expr::sort(Level::succ(Level::zero())),
        constructors: vec![],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl)
        .expect("should add Empty inductive");
    let ind_val = env.get_inductive(&empty_name).unwrap().clone();
    (env, ind_val)
}

/// Build a three-constructor enum: `inductive Traffic | Red | Yellow | Green`.
fn make_traffic_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    let name = Name::from_string("Traffic");
    let ty = Expr::sort(Level::succ(Level::zero()));

    let ind_type = InductiveType {
        name: name.clone(),
        type_: ty,
        constructors: vec![
            clean_kernel::Constructor {
                name: Name::from_string("Traffic.Red"),
                type_: Expr::const_(name.clone(), vec![]),
            },
            clean_kernel::Constructor {
                name: Name::from_string("Traffic.Yellow"),
                type_: Expr::const_(name.clone(), vec![]),
            },
            clean_kernel::Constructor {
                name: Name::from_string("Traffic.Green"),
                type_: Expr::const_(name.clone(), vec![]),
            },
        ],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl).expect("should add Traffic");
    let ind_val = env.get_inductive(&name).unwrap().clone();
    (env, ind_val)
}

/// Build a single-constructor, single-field wrapper: `structure Wrapper := (val : Nat)`.
fn make_wrapper_env() -> (Environment, InductiveVal) {
    let mut env = Environment::new();
    env.init_nat().expect("should init Nat");

    let wrapper_name = Name::from_string("Wrapper");
    let mk_name = Name::from_string("Wrapper.mk");
    let nat = Expr::const_str("Nat");

    let mk_type = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::const_(wrapper_name.clone(), vec![]),
    );

    let ind_type = InductiveType {
        name: wrapper_name.clone(),
        type_: Expr::sort(Level::succ(Level::zero())),
        constructors: vec![clean_kernel::Constructor {
            name: mk_name,
            type_: mk_type,
        }],
    };

    let ind_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![ind_type],
    };

    env.add_inductive(ind_decl).expect("should add Wrapper");
    let ind_val = env.get_inductive(&wrapper_name).unwrap().clone();
    (env, ind_val)
}

/// Build ConstructorInfo slices directly (without env) for unit testing handlers.
fn color_ctors() -> Vec<ConstructorInfo> {
    vec![
        ConstructorInfo {
            name: Name::from_string("Color.Red"),
            fields: vec![],
            is_recursive: false,
        },
        ConstructorInfo {
            name: Name::from_string("Color.Blue"),
            fields: vec![],
            is_recursive: false,
        },
    ]
}

fn point_ctors() -> Vec<ConstructorInfo> {
    let nat = Expr::const_str("Nat");
    vec![ConstructorInfo {
        name: Name::from_string("Point.mk"),
        fields: vec![
            (Name::from_string("x"), nat.clone()),
            (Name::from_string("y"), nat),
        ],
        is_recursive: false,
    }]
}

fn empty_ctors() -> Vec<ConstructorInfo> {
    vec![]
}

fn recursive_ctors() -> Vec<ConstructorInfo> {
    vec![ConstructorInfo {
        name: Name::from_string("Tree.node"),
        fields: vec![
            (Name::from_string("left"), Expr::const_str("Tree")),
            (Name::from_string("right"), Expr::const_str("Tree")),
        ],
        is_recursive: true,
    }]
}

fn single_nullary_ctor() -> Vec<ConstructorInfo> {
    vec![ConstructorInfo {
        name: Name::from_string("Unit.unit"),
        fields: vec![],
        is_recursive: false,
    }]
}

fn assert_unsupported<T: std::fmt::Debug>(result: Result<T, DeriveError>, class_name: &str) {
    match result {
        Err(DeriveError::Unsupported {
            class_name: got, ..
        }) => assert_eq!(got, class_name),
        other => panic!("expected Unsupported for {class_name}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Registry tests
// ---------------------------------------------------------------------------

#[test]
fn test_default_registry_has_all_handlers() {
    let reg = DeriveHandlerRegistry::default_registry();
    assert!(reg.has_handler("BEq"));
    assert!(reg.has_handler("Hashable"));
    assert!(reg.has_handler("Repr"));
    assert!(reg.has_handler("Ord"));
    assert!(reg.has_handler("Inhabited"));
    assert!(reg.has_handler("DecidableEq"));
}

#[test]
fn test_default_registry_has_6_handlers() {
    let reg = DeriveHandlerRegistry::default_registry();
    assert_eq!(reg.registered_classes().len(), 6);
}

#[test]
fn test_registry_no_handler_returns_false() {
    let reg = DeriveHandlerRegistry::new();
    assert!(!reg.has_handler("BEq"));
    assert!(!reg.has_handler("Functor"));
}

#[test]
fn test_registry_register_custom_handler() {
    let mut reg = DeriveHandlerRegistry::new();
    reg.register(Name::from_string("BEq"), Box::new(DeriveBEqExt));
    assert!(reg.has_handler("BEq"));
    assert!(!reg.has_handler("Hashable"));
}

#[test]
fn test_registry_derive_all_unknown_class_error() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));
    let ctors = color_ctors();

    let result = reg.derive_all(
        &type_name,
        &type_expr,
        &ctors,
        &[Name::from_string("Functor")],
        0,
        &[],
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::NoHandler(name) => assert_eq!(name, "Functor"),
        other => panic!("expected NoHandler, got {other:?}"),
    }
}

#[test]
fn test_registry_derive_all_multiple_classes() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Unit");
    let type_expr = Expr::sort(Level::succ(Level::zero()));
    let ctors = single_nullary_ctor();

    let classes = vec![Name::from_string("BEq"), Name::from_string("Inhabited")];

    let decls = reg
        .derive_all(&type_name, &type_expr, &ctors, &classes, 0, &[])
        .expect("derive_all should succeed");

    assert_eq!(decls.len(), 2);
    let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
    assert!(names.contains(&"instBEqUnit".to_string()));
    assert!(names.contains(&"instInhabitedUnit".to_string()));
}

#[test]
fn test_registry_derive_all_single_class() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Unit");
    let type_expr = Expr::sort(Level::succ(Level::zero()));
    let ctors = single_nullary_ctor();

    let decls = reg
        .derive_all(
            &type_name,
            &type_expr,
            &ctors,
            &[Name::from_string("Inhabited")],
            0,
            &[],
        )
        .expect("should derive Inhabited");

    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instInhabitedUnit");
    assert!(decls[0].is_instance);
}

#[test]
fn test_registry_derive_all_empty_classes_list() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = reg
        .derive_all(&type_name, &type_expr, &color_ctors(), &[], 0, &[])
        .expect("empty classes should succeed");

    assert!(decls.is_empty());
}

#[test]
fn test_registry_debug_format() {
    let reg = DeriveHandlerRegistry::default_registry();
    let debug_str = format!("{reg:?}");
    assert!(debug_str.contains("DeriveHandlerRegistry"));
}

// ---------------------------------------------------------------------------
// DeriveBEqExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_beq_ext_multi_ctor_enum_fails_closed() {
    let handler = DeriveBEqExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &color_ctors(), 0, &[]);
    assert_unsupported(result, "BEq");
}

#[test]
fn test_beq_ext_single_nullary_ctor_true() {
    let handler = DeriveBEqExt;
    let type_name = Name::from_string("Unit");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = handler
        .derive(&type_name, &type_expr, &single_nullary_ctor(), 0, &[])
        .expect("BEq for Unit should succeed");

    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instBEqUnit");
}

#[test]
fn test_beq_ext_empty_type() {
    let handler = DeriveBEqExt;
    let type_name = Name::from_string("Empty");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = handler
        .derive(&type_name, &type_expr, &empty_ctors(), 0, &[])
        .expect("BEq for Empty should succeed");

    assert_eq!(decls.len(), 1);
}

#[test]
fn test_beq_ext_recursive_rejected() {
    let handler = DeriveBEqExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported { class_name, .. } => assert_eq!(class_name, "BEq"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_beq_ext_struct_with_fields_fails_closed() {
    let handler = DeriveBEqExt;
    let type_name = Name::from_string("Point");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &point_ctors(), 0, &[]);
    assert_unsupported(result, "BEq");
}

// ---------------------------------------------------------------------------
// DeriveHashableExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_hashable_ext_enum_fails_closed() {
    let handler = DeriveHashableExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &color_ctors(), 0, &[]);
    assert_unsupported(result, "Hashable");
}

#[test]
fn test_hashable_ext_recursive_rejected() {
    let handler = DeriveHashableExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_hashable_ext_empty_type_fails_closed() {
    let handler = DeriveHashableExt;
    let type_name = Name::from_string("Empty");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &empty_ctors(), 0, &[]);
    assert_unsupported(result, "Hashable");
}

// ---------------------------------------------------------------------------
// DeriveReprExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_repr_ext_enum_fails_closed() {
    let handler = DeriveReprExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &color_ctors(), 0, &[]);
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr_ext_recursive_fails_closed() {
    let handler = DeriveReprExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Repr");
}

#[test]
fn test_repr_ext_struct_fails_closed() {
    let handler = DeriveReprExt;
    let type_name = Name::from_string("Point");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &point_ctors(), 0, &[]);
    assert_unsupported(result, "Repr");
}

// ---------------------------------------------------------------------------
// DeriveOrdExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_ord_ext_nonempty_enum_fails_closed() {
    let handler = DeriveOrdExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &color_ctors(), 0, &[]);
    assert_unsupported(result, "Ord");
}

#[test]
fn test_ord_ext_empty_type() {
    let handler = DeriveOrdExt;
    let type_name = Name::from_string("Empty");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = handler
        .derive(&type_name, &type_expr, &empty_ctors(), 0, &[])
        .expect("Ord for Empty should succeed");

    assert_eq!(decls.len(), 1);
}

#[test]
fn test_ord_ext_recursive_rejected() {
    let handler = DeriveOrdExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported { class_name, .. } => assert_eq!(class_name, "Ord"),
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// DeriveInhabitedExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_inhabited_ext_enum() {
    let handler = DeriveInhabitedExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = handler
        .derive(&type_name, &type_expr, &color_ctors(), 0, &[])
        .expect("Inhabited derive should succeed");

    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name.to_string(), "instInhabitedColor");
    assert!(decls[0].is_instance);
}

#[test]
fn test_inhabited_ext_no_constructors_error() {
    let handler = DeriveInhabitedExt;
    let type_name = Name::from_string("Empty");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &empty_ctors(), 0, &[]);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Inhabited");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

#[test]
fn test_inhabited_ext_struct_with_fields_fails_closed() {
    let handler = DeriveInhabitedExt;
    let type_name = Name::from_string("Point");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &point_ctors(), 0, &[]);
    assert_unsupported(result, "Inhabited");
}

#[test]
fn test_inhabited_ext_single_nullary_ctor() {
    let handler = DeriveInhabitedExt;
    let type_name = Name::from_string("Unit");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let decls = handler
        .derive(&type_name, &type_expr, &single_nullary_ctor(), 0, &[])
        .expect("Inhabited for Unit should succeed");

    assert_eq!(decls.len(), 1);
}

#[test]
fn test_inhabited_ext_recursive_field_ctor_fails_closed() {
    let handler = DeriveInhabitedExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert_unsupported(result, "Inhabited");
}

// ---------------------------------------------------------------------------
// DeriveDecidableEqExt tests
// ---------------------------------------------------------------------------

#[test]
fn test_deceq_ext_enum_fails_closed() {
    let handler = DeriveDecidableEqExt;
    let type_name = Name::from_string("Color");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &color_ctors(), 0, &[]);
    assert_unsupported(result, "DecidableEq");
}

#[test]
fn test_deceq_ext_recursive_rejected() {
    let handler = DeriveDecidableEqExt;
    let type_name = Name::from_string("Tree");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &recursive_ctors(), 0, &[]);
    assert!(result.is_err());
}

#[test]
fn test_deceq_ext_struct_fails_closed() {
    let handler = DeriveDecidableEqExt;
    let type_name = Name::from_string("Point");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let result = handler.derive(&type_name, &type_expr, &point_ctors(), 0, &[]);
    assert_unsupported(result, "DecidableEq");
}

// ---------------------------------------------------------------------------
// extract_constructor_info tests (integration with env)
// ---------------------------------------------------------------------------

#[test]
fn test_extract_ctor_info_enum() {
    let (env, ind) = make_color_env();
    let ctors = extract_constructor_info(&ind, &env).expect("should extract ctors");

    assert_eq!(ctors.len(), 2);
    assert_eq!(ctors[0].name.to_string(), "Color.Red");
    assert_eq!(ctors[1].name.to_string(), "Color.Blue");
    assert!(ctors[0].fields.is_empty());
    assert!(ctors[1].fields.is_empty());
    assert!(!ctors[0].is_recursive);
    assert!(!ctors[1].is_recursive);
}

#[test]
fn test_extract_ctor_info_struct_with_fields() {
    let (env, ind) = make_point_env();
    let ctors = extract_constructor_info(&ind, &env).expect("should extract ctors");

    assert_eq!(ctors.len(), 1);
    assert_eq!(ctors[0].name.to_string(), "Point.mk");
    assert_eq!(ctors[0].fields.len(), 2);
    assert!(!ctors[0].is_recursive);
}

#[test]
fn test_extract_ctor_info_empty_type() {
    let (env, ind) = make_empty_env();
    let ctors = extract_constructor_info(&ind, &env).expect("should extract ctors");

    assert!(ctors.is_empty());
}

#[test]
fn test_extract_ctor_info_three_ctors() {
    let (env, ind) = make_traffic_env();
    let ctors = extract_constructor_info(&ind, &env).expect("should extract ctors");

    assert_eq!(ctors.len(), 3);
    assert_eq!(ctors[0].name.to_string(), "Traffic.Red");
    assert_eq!(ctors[1].name.to_string(), "Traffic.Yellow");
    assert_eq!(ctors[2].name.to_string(), "Traffic.Green");
}

#[test]
fn test_extract_ctor_info_single_field() {
    let (env, ind) = make_wrapper_env();
    let ctors = extract_constructor_info(&ind, &env).expect("should extract ctors");

    assert_eq!(ctors.len(), 1);
    assert_eq!(ctors[0].fields.len(), 1);
}

// ---------------------------------------------------------------------------
// derive_all integration with extract_constructor_info
// ---------------------------------------------------------------------------

#[test]
fn test_derive_all_via_extraction_enum_supported_subset() {
    let (env, ind) = make_color_env();
    let ctors = extract_constructor_info(&ind, &env).unwrap();
    let reg = DeriveHandlerRegistry::default_registry();

    let classes = vec![Name::from_string("Inhabited")];

    let decls = reg
        .derive_all(&ind.name, &ind.type_, &ctors, &classes, 0, &[])
        .expect("Inhabited should derive for a nullary enum");

    assert_eq!(decls.len(), 1);
    assert!(decls.iter().all(|d| d.is_instance));
}

#[test]
fn test_derive_all_via_extraction_struct_fails_closed() {
    let (env, ind) = make_point_env();
    let ctors = extract_constructor_info(&ind, &env).unwrap();
    let reg = DeriveHandlerRegistry::default_registry();

    let classes = vec![Name::from_string("BEq")];
    let result = reg.derive_all(&ind.name, &ind.type_, &ctors, &classes, 0, &[]);
    assert_unsupported(result, "BEq");
}

#[test]
fn test_derive_all_stops_on_first_error() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Empty");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    // Inhabited will fail (no constructors), but BEq should pass.
    // Since Inhabited comes after BEq, we check that BEq results are not returned
    // when Inhabited fails.
    let classes = vec![Name::from_string("BEq"), Name::from_string("Inhabited")];

    let result = reg.derive_all(&type_name, &type_expr, &empty_ctors(), &classes, 0, &[]);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// DerivedDecl structure tests
// ---------------------------------------------------------------------------

#[test]
fn test_derived_decl_is_instance_flag() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("Unit");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let classes = vec![Name::from_string("BEq")];
    let decls = reg
        .derive_all(
            &type_name,
            &type_expr,
            &single_nullary_ctor(),
            &classes,
            0,
            &[],
        )
        .unwrap();

    assert!(decls[0].is_instance);
}

#[test]
fn test_derived_decl_name_follows_convention() {
    let reg = DeriveHandlerRegistry::default_registry();
    let type_name = Name::from_string("MyType");
    let type_expr = Expr::sort(Level::succ(Level::zero()));

    let all_classes = vec![Name::from_string("BEq"), Name::from_string("Inhabited")];

    let decls = reg
        .derive_all(
            &type_name,
            &type_expr,
            &single_nullary_ctor(),
            &all_classes,
            0,
            &[],
        )
        .unwrap();

    let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
    assert!(names.contains(&"instBEqMyType".to_string()));
    assert!(names.contains(&"instInhabitedMyType".to_string()));
}

// ---------------------------------------------------------------------------
// Handler class_name tests
// ---------------------------------------------------------------------------

#[test]
fn test_handler_class_names() {
    assert_eq!(DeriveBEqExt.class_name(), "BEq");
    assert_eq!(DeriveHashableExt.class_name(), "Hashable");
    assert_eq!(DeriveReprExt.class_name(), "Repr");
    assert_eq!(DeriveOrdExt.class_name(), "Ord");
    assert_eq!(DeriveInhabitedExt.class_name(), "Inhabited");
    assert_eq!(DeriveDecidableEqExt.class_name(), "DecidableEq");
}
