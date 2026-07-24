// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended derive handler module (`derive_ext2`).

use clean_kernel::{Expr, Name};

use crate::derive::DeriveError;
use crate::derive_ext2::*;

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn mk_simple_input(name: &str, class: DeriveClass) -> DeriveExt2Input {
    DeriveExt2Input {
        type_name: Name::from_string(name),
        type_expr: Expr::const_str(name),
        constructors: vec![Ext2ConstructorInfo {
            name: Name::from_string(&format!("{name}.mk")),
            fields: vec![],
            is_recursive: false,
        }],
        num_params: 0,
        level_params: vec![],
        target_class: class,
    }
}

fn mk_input_with_fields(name: &str, class: DeriveClass, num_fields: usize) -> DeriveExt2Input {
    let fields: Vec<(Name, Expr)> = (0..num_fields)
        .map(|i| {
            (
                Name::from_string(&format!("field{i}")),
                Expr::const_str("Nat"),
            )
        })
        .collect();
    DeriveExt2Input {
        type_name: Name::from_string(name),
        type_expr: Expr::const_str(name),
        constructors: vec![Ext2ConstructorInfo {
            name: Name::from_string(&format!("{name}.mk")),
            fields,
            is_recursive: false,
        }],
        num_params: 0,
        level_params: vec![],
        target_class: class,
    }
}

fn mk_empty_input(name: &str, class: DeriveClass) -> DeriveExt2Input {
    DeriveExt2Input {
        type_name: Name::from_string(name),
        type_expr: Expr::const_str(name),
        constructors: vec![],
        num_params: 0,
        level_params: vec![],
        target_class: class,
    }
}

fn mk_multi_ctor_input(name: &str, class: DeriveClass) -> DeriveExt2Input {
    DeriveExt2Input {
        type_name: Name::from_string(name),
        type_expr: Expr::const_str(name),
        constructors: vec![
            Ext2ConstructorInfo {
                name: Name::from_string(&format!("{name}.A")),
                fields: vec![],
                is_recursive: false,
            },
            Ext2ConstructorInfo {
                name: Name::from_string(&format!("{name}.B")),
                fields: vec![(Name::from_string("val"), Expr::const_str("Nat"))],
                is_recursive: false,
            },
        ],
        num_params: 0,
        level_params: vec![],
        target_class: class,
    }
}

fn mk_parametric_input(name: &str, class: DeriveClass, num_params: u32) -> DeriveExt2Input {
    DeriveExt2Input {
        type_name: Name::from_string(name),
        type_expr: Expr::const_str(name),
        constructors: vec![Ext2ConstructorInfo {
            name: Name::from_string(&format!("{name}.mk")),
            fields: vec![(Name::from_string("val"), Expr::bvar(0))],
            is_recursive: false,
        }],
        num_params,
        level_params: vec![Name::from_string("u")],
        target_class: class,
    }
}

fn default_config() -> DeriveExt2Config {
    DeriveExt2Config::default()
}

fn assert_unsupported(result: Result<DeriveExt2Output, DeriveError>, class_name: &str) {
    match result {
        Err(DeriveError::Unsupported {
            class_name: got, ..
        }) => {
            assert_eq!(got, class_name);
        }
        other => panic!("expected Unsupported for {class_name}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Functor tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_functor_single_field_fails_closed() {
    let input = mk_input_with_fields("Box", DeriveClass::Functor, 1);
    let result = derive_functor(&input, &default_config());
    assert_unsupported(result, "Functor");
}

#[test]
fn test_derive_functor_multiple_fields_fails_closed() {
    let input = mk_input_with_fields("Pair", DeriveClass::Functor, 2);
    let result = derive_functor(&input, &default_config());
    assert_unsupported(result, "Functor");
}

#[test]
fn test_derive_functor_nested_parametric() {
    let input = mk_parametric_input("Tree", DeriveClass::Functor, 2);
    let result = derive_functor(&input, &default_config());
    assert_unsupported(result, "Functor");
}

#[test]
fn test_derive_functor_empty_type() {
    let input = mk_empty_input("Empty", DeriveClass::Functor);
    let result = derive_functor(&input, &default_config());
    assert_unsupported(result, "Functor");
}

// ---------------------------------------------------------------------------
// Traversable tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_traversable_basic() {
    let input = mk_simple_input("List", DeriveClass::Traversable);
    let result = derive_traversable(&input, &default_config());
    assert_unsupported(result, "Traversable");
}

#[test]
fn test_derive_traversable_parametric() {
    let input = mk_parametric_input("Container", DeriveClass::Traversable, 1);
    let result = derive_traversable(&input, &default_config());
    assert_unsupported(result, "Traversable");
}

// ---------------------------------------------------------------------------
// Foldable tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_foldable_basic() {
    let input = mk_simple_input("Seq", DeriveClass::Foldable);
    let result = derive_foldable(&input, &default_config());
    assert_unsupported(result, "Foldable");
}

#[test]
fn test_derive_foldable_with_params() {
    let input = mk_parametric_input("Vec", DeriveClass::Foldable, 1);
    let result = derive_foldable(&input, &default_config());
    assert_unsupported(result, "Foldable");
}

// ---------------------------------------------------------------------------
// Nonempty tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_nonempty_single_ctor_no_fields() {
    let input = mk_simple_input("Unit", DeriveClass::Nonempty);
    let result = derive_nonempty(&input, &default_config());
    assert!(result.is_ok());
    let output = result.unwrap();
    assert_eq!(output.decl_name.to_string(), "instNonemptyUnit");
}

#[test]
fn test_derive_nonempty_ctor_with_fields() {
    let input = mk_input_with_fields("Wrapper", DeriveClass::Nonempty, 3);
    let result = derive_nonempty(&input, &default_config());
    assert_unsupported(result, "Nonempty");
}

#[test]
fn test_derive_nonempty_empty_type_fails() {
    let input = mk_empty_input("Empty", DeriveClass::Nonempty);
    let result = derive_nonempty(&input, &default_config());
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::Unsupported {
            class_name, reason, ..
        } => {
            assert_eq!(class_name, "Nonempty");
            assert!(reason.contains("no constructors"));
        }
        other => panic!("unexpected error: {other}"),
    }
}

#[test]
fn test_derive_nonempty_multi_ctor() {
    let input = mk_multi_ctor_input("Either", DeriveClass::Nonempty);
    let result = derive_nonempty(&input, &default_config());
    assert!(result.is_ok());
}

// ---------------------------------------------------------------------------
// SizeOf tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_sizeof_basic_fails_closed() {
    let input = mk_simple_input("Color", DeriveClass::SizeOf);
    let result = derive_sizeof(&input, &default_config());
    assert_unsupported(result, "SizeOf");
}

#[test]
fn test_derive_sizeof_parametric() {
    let input = mk_parametric_input("Array", DeriveClass::SizeOf, 1);
    let result = derive_sizeof(&input, &default_config());
    assert_unsupported(result, "SizeOf");
}

// ---------------------------------------------------------------------------
// ToExpr tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_to_expr_basic_fails_closed() {
    let input = mk_simple_input("Bool", DeriveClass::ToExpr);
    let result = derive_to_expr(&input, &default_config());
    assert_unsupported(result, "ToExpr");
}

#[test]
fn test_derive_to_expr_with_fields() {
    let input = mk_input_with_fields("Point", DeriveClass::ToExpr, 2);
    let result = derive_to_expr(&input, &default_config());
    assert_unsupported(result, "ToExpr");
}

// ---------------------------------------------------------------------------
// FromExpr tests
// ---------------------------------------------------------------------------

#[test]
fn test_derive_from_expr_basic_fails_closed() {
    let input = mk_simple_input("Nat", DeriveClass::FromExpr);
    let result = derive_from_expr(&input, &default_config());
    assert_unsupported(result, "FromExpr");
}

#[test]
fn test_derive_from_expr_with_fields() {
    let input = mk_input_with_fields("Pair", DeriveClass::FromExpr, 2);
    let result = derive_from_expr(&input, &default_config());
    assert_unsupported(result, "FromExpr");
}

// ---------------------------------------------------------------------------
// Custom handler registration tests
// ---------------------------------------------------------------------------

fn custom_handler(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Ok(DeriveExt2Output {
        decl_name: Name::from_string(&format!("instCustom{}", input.type_name)),
        decl_type: Expr::const_str("CustomClass"),
        decl_value: Expr::const_str("CustomClass.mk"),
        auxiliary_decls: vec![],
    })
}

#[test]
fn test_register_custom_handler_and_derive() {
    let mut config = default_config();
    register_custom_handler(&mut config, "MyClass", custom_handler);
    let input = DeriveExt2Input {
        type_name: Name::from_string("Foo"),
        type_expr: Expr::const_str("Foo"),
        constructors: vec![],
        num_params: 0,
        level_params: vec![],
        target_class: DeriveClass::Custom("MyClass".to_owned()),
    };
    let mut cache = DeriveExt2Cache::new();
    let result = derive_ext2(&input, &config, &mut cache);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().decl_name.to_string(), "instCustomFoo");
}

#[test]
fn test_custom_handler_not_registered_returns_error() {
    let config = default_config();
    let input = DeriveExt2Input {
        type_name: Name::from_string("Bar"),
        type_expr: Expr::const_str("Bar"),
        constructors: vec![],
        num_params: 0,
        level_params: vec![],
        target_class: DeriveClass::Custom("Unknown".to_owned()),
    };
    let mut cache = DeriveExt2Cache::new();
    let result = derive_ext2(&input, &config, &mut cache);
    assert!(result.is_err());
    match result.unwrap_err() {
        DeriveError::NoHandler(name) => assert_eq!(name, "Unknown"),
        other => panic!("unexpected error: {other}"),
    }
}

// ---------------------------------------------------------------------------
// Caching tests
// ---------------------------------------------------------------------------

#[test]
fn test_cache_stores_result() {
    let config = default_config();
    let input = mk_simple_input("Cached", DeriveClass::Nonempty);
    let mut cache = DeriveExt2Cache::new();
    assert!(cache.is_empty());

    let _ = derive_ext2(&input, &config, &mut cache);
    assert_eq!(cache.len(), 1);
    let different_class = mk_simple_input("Cached", DeriveClass::SizeOf);
    assert!(cache.lookup(&different_class, &config).is_none());
    assert!(cache.lookup(&input, &config).is_some());
}

#[test]
fn test_cache_returns_same_result_on_second_call() {
    let config = default_config();
    let input = mk_simple_input("CachedTwo", DeriveClass::Nonempty);
    let mut cache = DeriveExt2Cache::new();

    let first = derive_ext2(&input, &config, &mut cache).unwrap();
    let second = derive_ext2(&input, &config, &mut cache).unwrap();
    assert_eq!(first.decl_name.to_string(), second.decl_name.to_string());
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_cache_disabled_does_not_store() {
    let mut config = default_config();
    config.enable_caching = false;
    let input = mk_simple_input("NoCacheType", DeriveClass::Nonempty);
    let mut cache = DeriveExt2Cache::new();

    let _ = derive_ext2(&input, &config, &mut cache);
    assert!(cache.is_empty());
}

#[test]
fn test_cache_different_classes_separate_entries() {
    let mut config = default_config();
    register_custom_handler(&mut config, "MyClass", custom_handler);
    let mut cache = DeriveExt2Cache::new();

    let input_nonempty = mk_simple_input("Multi", DeriveClass::Nonempty);
    let input_custom = mk_simple_input("Multi", DeriveClass::Custom("MyClass".to_owned()));

    derive_ext2(&input_nonempty, &config, &mut cache).expect("Nonempty should derive");
    derive_ext2(&input_custom, &config, &mut cache).expect("custom class should derive");
    assert_eq!(cache.len(), 2);
}

fn alternate_custom_handler(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Ok(DeriveExt2Output {
        decl_name: Name::from_string(&format!("instAlternate{}", input.type_name)),
        decl_type: Expr::const_str("AlternateClass"),
        decl_value: Expr::const_str("AlternateClass.mk"),
        auxiliary_decls: vec![],
    })
}

#[test]
fn test_cache_identity_includes_complete_input_shape() {
    let config = default_config();
    let first = mk_simple_input("Reused", DeriveClass::Nonempty);
    let mut changed = first.clone();
    changed.constructors.clear();
    let mut cache = DeriveExt2Cache::new();

    derive_ext2(&first, &config, &mut cache).expect("first shape should derive");
    assert!(
        derive_ext2(&changed, &config, &mut cache).is_err(),
        "a same-name cache entry must not mask a changed constructor shape"
    );
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_cache_identity_includes_custom_handler_registry() {
    let input = mk_simple_input("Configured", DeriveClass::Custom("Custom".to_owned()));
    let mut first_config = default_config();
    register_custom_handler(&mut first_config, "Custom", custom_handler);
    let mut second_config = default_config();
    register_custom_handler(&mut second_config, "Custom", alternate_custom_handler);
    let mut cache = DeriveExt2Cache::new();

    let first = derive_ext2(&input, &first_config, &mut cache).expect("first handler should run");
    let second =
        derive_ext2(&input, &second_config, &mut cache).expect("replacement handler should run");
    assert_eq!(first.decl_name.to_string(), "instCustomConfigured");
    assert_eq!(second.decl_name.to_string(), "instAlternateConfigured");
    assert_eq!(cache.len(), 2);
}

// ---------------------------------------------------------------------------
// Error case tests
// ---------------------------------------------------------------------------

#[test]
fn test_unsupported_shape_error_message() {
    let err = unsupported_shape_error(
        &DeriveClass::Functor,
        &Name::from_string("BadType"),
        "not a type constructor",
    );
    let msg = err.to_string();
    assert!(msg.contains("Functor"));
    assert!(msg.contains("BadType"));
    assert!(msg.contains("not a type constructor"));
}

// ---------------------------------------------------------------------------
// Edge case tests
// ---------------------------------------------------------------------------

#[test]
fn test_single_constructor_no_fields_all_classes() {
    let config = default_config();
    for class in supported_classes() {
        let input = mk_simple_input("SimpleEnum", class);
        let mut cache = DeriveExt2Cache::new();
        let result = derive_ext2(&input, &config, &mut cache);
        if matches!(&input.target_class, DeriveClass::Nonempty) {
            assert!(result.is_ok());
        } else {
            assert_unsupported(result, input.target_class.class_name());
        }
    }
}

#[test]
fn test_empty_type_all_builtin_classes_fail_closed() {
    let config = default_config();
    for class in supported_classes() {
        let input = mk_empty_input("EmptyType", class.clone());
        let mut cache = DeriveExt2Cache::new();
        let result = derive_ext2(&input, &config, &mut cache);
        assert_unsupported(result, class.class_name());
    }
}

#[test]
fn test_derive_class_class_name_correctness() {
    assert_eq!(DeriveClass::Functor.class_name(), "Functor");
    assert_eq!(DeriveClass::Traversable.class_name(), "Traversable");
    assert_eq!(DeriveClass::Foldable.class_name(), "Foldable");
    assert_eq!(DeriveClass::Nonempty.class_name(), "Nonempty");
    assert_eq!(DeriveClass::SizeOf.class_name(), "SizeOf");
    assert_eq!(DeriveClass::ToExpr.class_name(), "ToExpr");
    assert_eq!(DeriveClass::FromExpr.class_name(), "FromExpr");
    assert_eq!(
        DeriveClass::Custom("MyCustom".to_owned()).class_name(),
        "MyCustom"
    );
}

#[test]
fn test_supported_classes_returns_seven() {
    assert_eq!(supported_classes().len(), 7);
}

#[test]
fn test_derive_ext2_config_default() {
    let config = DeriveExt2Config::default();
    assert!(config.enable_caching);
    assert_eq!(config.max_derive_depth, 16);
    assert!(config.custom_handlers.is_empty());
}

#[test]
fn test_derive_ext2_cache_new_is_empty() {
    let cache = DeriveExt2Cache::new();
    assert!(cache.is_empty());
    assert_eq!(cache.len(), 0);
}

#[test]
fn test_derive_all_builtin_classes_dispatch() {
    let config = default_config();
    let mut cache = DeriveExt2Cache::new();
    for class in supported_classes() {
        let input = mk_simple_input("DispatchTest", class);
        let result = derive_ext2(&input, &config, &mut cache);
        if matches!(&input.target_class, DeriveClass::Nonempty) {
            assert!(result.is_ok());
        } else {
            assert_unsupported(result, input.target_class.class_name());
        }
    }
}

#[test]
fn test_mutual_type_multi_ctor_sizeof() {
    let input = mk_multi_ctor_input("MutualA", DeriveClass::SizeOf);
    let result = derive_sizeof(&input, &default_config());
    assert_unsupported(result, "SizeOf");
}

#[test]
fn test_parametric_type_foldable() {
    let input = mk_parametric_input("Stream", DeriveClass::Foldable, 3);
    let result = derive_foldable(&input, &default_config());
    assert_unsupported(result, "Foldable");
}

#[test]
fn test_ext2_instance_naming_convention() {
    let name = ext2_instance_name(&DeriveClass::Functor, &Name::from_string("List"));
    assert_eq!(name.to_string(), "instFunctorList");

    let name = ext2_instance_name(
        &DeriveClass::Custom("MyTC".to_owned()),
        &Name::from_string("Foo"),
    );
    assert_eq!(name.to_string(), "instMyTCFoo");
}
