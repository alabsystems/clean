// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for attribute handlers (`@[coe]`, `@[init]`, `@[default_instance]`,
//! `@[match_pattern]`).

use clean_kernel::{Declaration, Expr, Level, Name};

use super::*;

/// Create an environment with a single axiom declaration for testing.
fn env_with_decl(decl_name: &str) -> Environment {
    let mut env = Environment::new();
    let name = Name::from_string(decl_name);
    let prop = Expr::sort(Level::zero());
    env.add_decl(Declaration::Axiom {
        name,
        level_params: vec![],
        type_: prop,
    })
    .expect("add_decl should succeed");
    env
}

// ========================================================================
// handle_coe tests
// ========================================================================

#[test]
fn test_handle_coe_success() {
    let env = env_with_decl("my_coe");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("my_coe");

    handle_coe(&name, &env, &mut registry).expect("handle_coe should succeed");

    assert!(registry.is_coercion(&name));
    assert_eq!(registry.coercion_count(), 1);
}

#[test]
fn test_handle_coe_unknown_decl_returns_error() {
    let env = Environment::new();
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("nonexistent");

    let result = handle_coe(&name, &env, &mut registry);

    assert!(result.is_err());
    assert!(!registry.is_coercion(&name));
}

#[test]
fn test_handle_coe_duplicate_returns_error() {
    let env = env_with_decl("dup_coe");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("dup_coe");

    handle_coe(&name, &env, &mut registry).expect("first registration should succeed");
    let result = handle_coe(&name, &env, &mut registry);

    assert!(result.is_err());
    assert_eq!(registry.coercion_count(), 1);
}

// ========================================================================
// handle_init tests
// ========================================================================

#[test]
fn test_handle_init_success() {
    let env = env_with_decl("my_init");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("my_init");

    handle_init(&name, &env, &mut registry).expect("handle_init should succeed");

    assert!(registry.is_init_fn(&name));
    assert_eq!(registry.init_fn_count(), 1);
}

#[test]
fn test_handle_init_unknown_decl_returns_error() {
    let env = Environment::new();
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("nonexistent");

    let result = handle_init(&name, &env, &mut registry);

    assert!(result.is_err());
    assert!(!registry.is_init_fn(&name));
}

#[test]
fn test_handle_init_duplicate_returns_error() {
    let env = env_with_decl("dup_init");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("dup_init");

    handle_init(&name, &env, &mut registry).expect("first registration should succeed");
    let result = handle_init(&name, &env, &mut registry);

    assert!(result.is_err());
    assert_eq!(registry.init_fn_count(), 1);
}

// ========================================================================
// handle_default_instance tests
// ========================================================================

#[test]
fn test_handle_default_instance_with_default_priority() {
    let env = env_with_decl("my_default_inst");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("my_default_inst");

    handle_default_instance(&name, &env, &mut registry, None)
        .expect("handle_default_instance should succeed");

    assert!(registry.is_default_instance(&name));
    let info = registry
        .get_default_instance(&name)
        .expect("info should exist");
    assert_eq!(info.priority, DEFAULT_INSTANCE_PRIORITY);
    assert_eq!(info.name, name);
    assert_eq!(registry.default_instance_count(), 1);
}

#[test]
fn test_handle_default_instance_with_custom_priority() {
    let env = env_with_decl("custom_prio_inst");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("custom_prio_inst");

    handle_default_instance(&name, &env, &mut registry, Some(500))
        .expect("handle_default_instance should succeed");

    let info = registry
        .get_default_instance(&name)
        .expect("info should exist");
    assert_eq!(info.priority, 500);
}

#[test]
fn test_handle_default_instance_unknown_decl_returns_error() {
    let env = Environment::new();
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("nonexistent");

    let result = handle_default_instance(&name, &env, &mut registry, None);

    assert!(result.is_err());
    assert!(!registry.is_default_instance(&name));
}

#[test]
fn test_handle_default_instance_duplicate_returns_error() {
    let env = env_with_decl("dup_default_inst");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("dup_default_inst");

    handle_default_instance(&name, &env, &mut registry, None)
        .expect("first registration should succeed");
    let result = handle_default_instance(&name, &env, &mut registry, Some(200));

    assert!(result.is_err());
    assert_eq!(registry.default_instance_count(), 1);
    // Priority should remain from first registration
    let info = registry
        .get_default_instance(&name)
        .expect("info should exist");
    assert_eq!(info.priority, DEFAULT_INSTANCE_PRIORITY);
}

// ========================================================================
// handle_match_pattern tests
// ========================================================================

#[test]
fn test_handle_match_pattern_success() {
    let env = env_with_decl("my_pat");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("my_pat");

    handle_match_pattern(&name, &env, &mut registry).expect("handle_match_pattern should succeed");

    assert!(registry.is_match_pattern(&name));
    assert_eq!(registry.match_pattern_count(), 1);
}

#[test]
fn test_handle_match_pattern_unknown_decl_returns_error() {
    let env = Environment::new();
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("nonexistent");

    let result = handle_match_pattern(&name, &env, &mut registry);

    assert!(result.is_err());
    assert!(!registry.is_match_pattern(&name));
}

#[test]
fn test_handle_match_pattern_duplicate_returns_error() {
    let env = env_with_decl("dup_pat");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("dup_pat");

    handle_match_pattern(&name, &env, &mut registry).expect("first registration should succeed");
    let result = handle_match_pattern(&name, &env, &mut registry);

    assert!(result.is_err());
    assert_eq!(registry.match_pattern_count(), 1);
}

// ========================================================================
// Registry isolation tests
// ========================================================================

#[test]
fn test_registry_categories_are_independent() {
    let env = env_with_decl("multi_attr");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("multi_attr");

    handle_coe(&name, &env, &mut registry).expect("coe should succeed");
    handle_init(&name, &env, &mut registry).expect("init should succeed");
    handle_default_instance(&name, &env, &mut registry, Some(42))
        .expect("default_instance should succeed");
    handle_match_pattern(&name, &env, &mut registry).expect("match_pattern should succeed");

    assert!(registry.is_coercion(&name));
    assert!(registry.is_init_fn(&name));
    assert!(registry.is_default_instance(&name));
    assert!(registry.is_match_pattern(&name));

    assert_eq!(registry.coercion_count(), 1);
    assert_eq!(registry.init_fn_count(), 1);
    assert_eq!(registry.default_instance_count(), 1);
    assert_eq!(registry.match_pattern_count(), 1);
}

#[test]
fn test_registry_multiple_distinct_declarations() {
    let mut env = Environment::new();
    let prop = Expr::sort(Level::zero());
    for name_str in &["decl_a", "decl_b", "decl_c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name_str),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add_decl should succeed");
    }

    let mut registry = AttributeHandlerRegistry::new();
    let a = Name::from_string("decl_a");
    let b = Name::from_string("decl_b");
    let c = Name::from_string("decl_c");

    handle_coe(&a, &env, &mut registry).expect("coe a should succeed");
    handle_coe(&b, &env, &mut registry).expect("coe b should succeed");
    handle_init(&c, &env, &mut registry).expect("init c should succeed");

    assert_eq!(registry.coercion_count(), 2);
    assert_eq!(registry.init_fn_count(), 1);
    assert!(registry.is_coercion(&a));
    assert!(registry.is_coercion(&b));
    assert!(!registry.is_coercion(&c));
    assert!(registry.is_init_fn(&c));
}

#[test]
fn test_empty_registry_returns_zero_counts() {
    let registry = AttributeHandlerRegistry::new();

    assert_eq!(registry.coercion_count(), 0);
    assert_eq!(registry.init_fn_count(), 0);
    assert_eq!(registry.default_instance_count(), 0);
    assert_eq!(registry.match_pattern_count(), 0);
}

#[test]
fn test_registry_iterators_yield_registered_names() {
    let env = env_with_decl("iter_test");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("iter_test");

    handle_coe(&name, &env, &mut registry).unwrap();
    handle_match_pattern(&name, &env, &mut registry).unwrap();

    let coe_names: Vec<_> = registry.coercions().collect();
    assert_eq!(coe_names.len(), 1);
    assert_eq!(coe_names[0], &name);

    let pat_names: Vec<_> = registry.match_patterns().collect();
    assert_eq!(pat_names.len(), 1);
    assert_eq!(pat_names[0], &name);
}

#[test]
fn test_default_instance_iterator() {
    let env = env_with_decl("di_iter");
    let mut registry = AttributeHandlerRegistry::new();
    let name = Name::from_string("di_iter");

    handle_default_instance(&name, &env, &mut registry, Some(777)).unwrap();

    let infos: Vec<_> = registry.default_instances().collect();
    assert_eq!(infos.len(), 1);
    assert_eq!(infos[0].name, name);
    assert_eq!(infos[0].priority, 777);
}

// ========================================================================
// UserAttributeRegistry tests (Phase 3 extensibility surface)
// ========================================================================

#[test]
fn test_user_attribute_registry_dispatches_to_registered_handler() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    let env = env_with_decl("my_decl");
    let calls = Arc::new(AtomicUsize::new(0));
    let calls_in = Arc::clone(&calls);
    let mut reg = UserAttributeRegistry::new();
    reg.register(
        "my_attr",
        Arc::new(move |target: &Name, env: &Environment| {
            // A realistic handler validates its target, then does its work.
            validate_decl_exists(target, env)?;
            calls_in.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }),
    );

    assert!(reg.is_registered("my_attr"));
    assert_eq!(reg.registered_count(), 1);
    assert_eq!(reg.attribute_names().collect::<Vec<_>>(), vec!["my_attr"]);

    reg.dispatch("my_attr", &Name::from_string("my_decl"), &env)
        .expect("handler should accept an existing target");
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "the registered handler should run exactly once"
    );
}

#[test]
fn test_user_attribute_registry_unknown_attribute_is_unsupported_error() {
    let env = env_with_decl("d");
    let reg = UserAttributeRegistry::new();
    let err = reg
        .dispatch("not_registered", &Name::from_string("d"), &env)
        .expect_err("an unregistered attribute must fail loudly, not silently");
    assert!(
        matches!(err, ElabError::Unsupported { .. }),
        "expected Unsupported, got {err:?}"
    );
}

#[test]
fn test_user_attribute_registry_handler_error_propagates() {
    use std::sync::Arc;

    let env = env_with_decl("present");
    let mut reg = UserAttributeRegistry::new();
    reg.register(
        "strict",
        Arc::new(|target: &Name, env: &Environment| validate_decl_exists(target, env)),
    );
    // Absent target → the handler's own error propagates (not swallowed).
    assert!(
        reg.dispatch("strict", &Name::from_string("absent"), &env)
            .is_err(),
        "handler should reject an absent target"
    );
    // Present target → Ok.
    reg.dispatch("strict", &Name::from_string("present"), &env)
        .expect("handler should accept a present target");
}

#[test]
fn test_user_attribute_registry_last_registration_wins() {
    use std::sync::Arc;

    let env = env_with_decl("d");
    let mut reg = UserAttributeRegistry::new();
    reg.register(
        "a",
        Arc::new(|_t: &Name, _e: &Environment| {
            Err(ElabError::Unsupported {
                feature: "first handler (should be replaced)".into(),
            })
        }),
    );
    reg.register("a", Arc::new(|_t: &Name, _e: &Environment| Ok(())));
    assert_eq!(
        reg.registered_count(),
        1,
        "re-registering the same name replaces, not appends"
    );
    reg.dispatch("a", &Name::from_string("d"), &env)
        .expect("the second (last) registered handler should win");
}
