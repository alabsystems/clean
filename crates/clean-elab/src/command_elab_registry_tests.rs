// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ============================================================================
// Registry construction tests
// ============================================================================

#[test]
fn test_registry_new_has_builtins() {
    let registry = CommandElabRegistry::new();
    for &kind in BUILTIN_COMMAND_KINDS {
        assert!(
            registry.is_registered(kind),
            "builtin command kind '{kind}' should be registered"
        );
    }
}

#[test]
fn test_registry_builtin_count() {
    let registry = CommandElabRegistry::new();
    assert_eq!(
        registry.kind_count(),
        BUILTIN_COMMAND_KINDS.len(),
        "registry should have one kind per BUILTIN_COMMAND_KINDS entry"
    );
    assert_eq!(
        registry.handler_count(),
        BUILTIN_COMMAND_KINDS.len(),
        "one handler per builtin kind"
    );
}

#[test]
fn test_registry_default_trait() {
    let registry = CommandElabRegistry::default();
    assert_eq!(registry.kind_count(), BUILTIN_COMMAND_KINDS.len());
}

// ============================================================================
// Registration tests
// ============================================================================

#[test]
fn test_register_custom_command() {
    let mut registry = CommandElabRegistry::new();
    let initial_kinds = registry.kind_count();

    registry.register(
        "myCustomAttr",
        CommandElabEntry {
            command_name: "myCustomAttr".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 2000,
        },
    );

    assert!(registry.is_registered("myCustomAttr"));
    assert_eq!(registry.kind_count(), initial_kinds + 1);
}

#[test]
fn test_not_registered_for_unknown() {
    let registry = CommandElabRegistry::new();
    assert!(!registry.is_registered("nonexistent"));
    assert!(registry.get_handlers("nonexistent").is_none());
}

#[test]
fn test_multiple_handlers_priority_order() {
    let mut registry = CommandElabRegistry::new();

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Err(ElabError::NotImplemented("low".into()))),
            priority: 100,
        },
    );

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Err(ElabError::NotImplemented("high".into()))),
            priority: 500,
        },
    );

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Err(ElabError::NotImplemented("medium".into()))),
            priority: 300,
        },
    );

    let handlers = registry.get_handlers("testCmd").unwrap();
    assert_eq!(handlers.len(), 3);
    assert_eq!(handlers[0].priority, 500, "highest priority first");
    assert_eq!(handlers[1].priority, 300, "medium priority second");
    assert_eq!(handlers[2].priority, 100, "lowest priority third");
}

// ============================================================================
// Elaboration dispatch tests
// ============================================================================

#[test]
fn test_elaborate_no_handlers_returns_none() {
    let registry = CommandElabRegistry::new();
    let mut env = Environment::new();
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("test"),
        env: &mut env,
    };
    let result = registry.elaborate("nonexistent", &mut ctx, &[]);
    assert!(result.is_none(), "no handlers should return None");
}

#[test]
fn test_elaborate_first_success_wins() {
    let mut registry = CommandElabRegistry::default();

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 2000,
        },
    );

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| {
                Err(ElabError::NotImplemented("should not be reached".into()))
            }),
            priority: 500,
        },
    );

    let mut env = Environment::new();
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("test"),
        env: &mut env,
    };
    let result = registry.elaborate("testCmd", &mut ctx, &[]);
    assert!(
        result.expect("should have handlers").is_ok(),
        "high-priority handler should succeed"
    );
}

#[test]
fn test_elaborate_fallthrough_on_error() {
    let mut registry = CommandElabRegistry::default();

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Err(ElabError::NotImplemented("skip".into()))),
            priority: 2000,
        },
    );

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: 500,
        },
    );

    let mut env = Environment::new();
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("test"),
        env: &mut env,
    };
    let result = registry.elaborate("testCmd", &mut ctx, &[]);
    assert!(
        result.expect("should have handlers").is_ok(),
        "should fall through to lower-priority handler"
    );
}

#[test]
fn test_elaborate_all_fail_returns_last_error() {
    let mut registry = CommandElabRegistry::default();

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| Err(ElabError::NotImplemented("first failure".into()))),
            priority: 2000,
        },
    );

    registry.register(
        "testCmd",
        CommandElabEntry {
            command_name: "testCmd".to_owned(),
            handler: Arc::new(|_ctx, _args| {
                Err(ElabError::NotImplemented("second failure".into()))
            }),
            priority: 500,
        },
    );

    let mut env = Environment::new();
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("test"),
        env: &mut env,
    };
    let result = registry.elaborate("testCmd", &mut ctx, &[]);
    let err = result.expect("should have handlers").unwrap_err();
    let msg = format!("{err}");
    assert!(
        msg.contains("second failure"),
        "should return last handler's error, got: {msg}"
    );
}

// ============================================================================
// Iterator and debug tests
// ============================================================================

#[test]
fn test_kinds_iterator() {
    let registry = CommandElabRegistry::new();
    let kinds: Vec<&str> = registry.kinds().collect();
    assert_eq!(kinds.len(), BUILTIN_COMMAND_KINDS.len());
    for &expected in BUILTIN_COMMAND_KINDS {
        assert!(
            kinds.contains(&expected),
            "iterator should include '{expected}'"
        );
    }
}

#[test]
fn test_entry_debug_format() {
    let entry = CommandElabEntry {
        command_name: "myCmd".to_owned(),
        handler: Arc::new(|_ctx, _args| Ok(())),
        priority: 500,
    };
    let debug = format!("{entry:?}");
    assert!(debug.contains("myCmd"));
    assert!(debug.contains("500"));
}

#[test]
fn test_entry_clone() {
    let entry = CommandElabEntry {
        command_name: "myCmd".to_owned(),
        handler: Arc::new(|_ctx, _args| Ok(())),
        priority: 500,
    };
    let cloned = entry.clone();
    assert_eq!(cloned.command_name, "myCmd");
    assert_eq!(cloned.priority, 500);
}

#[test]
fn test_registry_debug_format() {
    let registry = CommandElabRegistry::new();
    let debug = format!("{registry:?}");
    assert!(debug.contains("CommandElabRegistry"));
    assert!(debug.contains("kind_count"));
}

// ============================================================================
// Builtin handler integration tests
// ============================================================================

/// Helper to create an environment with a registered definition for testing.
fn env_with_test_def(name: &str) -> Environment {
    let mut env = Environment::new();
    let decl = clean_kernel::Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: clean_kernel::Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero())),
        value: clean_kernel::Expr::sort(clean_kernel::Level::zero()),
        is_reducible: true,
    };
    env.add_decl(decl).expect("should register test definition");
    env
}

/// Helper to create an environment with a generic derive handler declaration.
fn env_with_test_derive_handler(class_name: &str, handler_name: &str) -> Environment {
    let mut env = Environment::new();
    let class_name = Name::from_string(class_name);
    let handler_name = Name::from_string(handler_name);
    let type_sort =
        clean_kernel::Expr::sort(clean_kernel::Level::succ(clean_kernel::Level::zero()));

    env.add_decl(clean_kernel::Declaration::Axiom {
        name: class_name.clone(),
        level_params: vec![],
        type_: clean_kernel::Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            type_sort.clone(),
            type_sort.clone(),
        ),
    })
    .expect("should register test class");

    env.add_decl(clean_kernel::Declaration::Axiom {
        name: handler_name,
        level_params: vec![],
        type_: clean_kernel::Expr::pi(
            clean_kernel::BinderInfo::Implicit,
            type_sort,
            clean_kernel::Expr::app(
                clean_kernel::Expr::const_(class_name, vec![]),
                clean_kernel::Expr::bvar(0),
            ),
        ),
    })
    .expect("should register test derive handler");

    env
}

#[test]
fn test_builtin_reducible_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myDef");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myDef"),
        env: &mut env,
    };

    let result = registry.elaborate("reducible", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[reducible] handler should succeed"
    );
}

#[test]
fn test_builtin_irreducible_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myDef");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myDef"),
        env: &mut env,
    };

    let result = registry.elaborate("irreducible", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[irreducible] handler should succeed"
    );
}

#[test]
fn test_builtin_semireducible_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myDef");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myDef"),
        env: &mut env,
    };

    let result = registry.elaborate("semireducible", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[semireducible] handler should succeed"
    );
}

#[test]
fn test_builtin_simp_handler_default_priority() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myLemma");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myLemma"),
        env: &mut env,
    };

    let result = registry.elaborate("simp", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[simp] handler should succeed"
    );

    assert!(
        env.is_simp_lemma(&Name::from_string("myLemma")),
        "myLemma should be registered as a simp lemma"
    );
}

#[test]
fn test_builtin_simp_handler_custom_priority() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myLemma");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myLemma"),
        env: &mut env,
    };

    let args = vec!["200".to_owned()];
    let result = registry.elaborate("simp", &mut ctx, &args);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[simp 200] handler should succeed"
    );

    assert!(env.is_simp_lemma(&Name::from_string("myLemma")));
}

#[test]
fn test_builtin_simp_handler_invalid_priority() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myLemma");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myLemma"),
        env: &mut env,
    };

    let args = vec!["notanumber".to_owned()];
    let result = registry.elaborate("simp", &mut ctx, &args);
    assert!(
        result.expect("should have handler").is_err(),
        "@[simp notanumber] should fail with invalid priority"
    );
}

#[test]
fn test_builtin_inline_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myFn");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myFn"),
        env: &mut env,
    };

    let result = registry.elaborate("inline", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[inline] handler should succeed"
    );

    assert!(
        env.is_inline(&Name::from_string("myFn")),
        "myFn should be registered as inline"
    );
}

#[test]
fn test_builtin_instance_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("instHAddNat");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("instHAddNat"),
        env: &mut env,
    };

    let result = registry.elaborate("instance", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[instance] handler should succeed"
    );
}

#[test]
fn test_builtin_instance_handler_with_priority() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("instHAddNat");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("instHAddNat"),
        env: &mut env,
    };

    let args = vec!["500".to_owned()];
    let result = registry.elaborate("instance", &mut ctx, &args);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[instance 500] handler should succeed"
    );
}

#[test]
fn test_builtin_extern_handler_with_name() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myExtern");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myExtern"),
        env: &mut env,
    };

    let args = vec!["lean_my_extern".to_owned()];
    let result = registry.elaborate("extern", &mut ctx, &args);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[extern \"lean_my_extern\"] handler should succeed"
    );

    assert!(
        env.is_extern(&Name::from_string("myExtern")),
        "myExtern should be registered as extern"
    );
    assert_eq!(
        env.get_extern(&Name::from_string("myExtern")),
        Some(&"lean_my_extern".to_owned()),
        "extern name should match"
    );
}

#[test]
fn test_builtin_extern_handler_default_name() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_def("myExtern");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("myExtern"),
        env: &mut env,
    };

    let result = registry.elaborate("extern", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[extern] with no args should use decl name"
    );

    assert!(env.is_extern(&Name::from_string("myExtern")));
}

#[test]
fn test_builtin_derive_handler_handler() {
    let registry = CommandElabRegistry::new();
    let mut env = env_with_test_derive_handler("MyClass", "deriveMyClass");
    let mut ctx = CommandElabCtx {
        decl_name: Name::from_string("deriveMyClass"),
        env: &mut env,
    };

    let result = registry.elaborate("derive_handler", &mut ctx, &[]);
    assert!(
        result.expect("should have handler").is_ok(),
        "@[derive_handler] handler should succeed"
    );

    let handlers = env
        .get_derive_handlers(&Name::from_string("MyClass"))
        .expect("MyClass should have a registered derive handler");
    assert_eq!(handlers, &[Name::from_string("deriveMyClass")]);
}

// ============================================================================
// User override tests
// ============================================================================

#[test]
fn test_user_overrides_builtin() {
    let mut registry = CommandElabRegistry::new();

    // Register a user handler at higher priority than builtin
    registry.register(
        "reducible",
        CommandElabEntry {
            command_name: "reducible".to_owned(),
            handler: Arc::new(|_ctx, _args| Ok(())),
            priority: DEFAULT_PRIORITY + 100,
        },
    );

    let handlers = registry.get_handlers("reducible").unwrap();
    assert_eq!(handlers.len(), 2, "builtin + user = 2 handlers");
    assert_eq!(
        handlers[0].priority,
        DEFAULT_PRIORITY + 100,
        "user handler should be first"
    );
    assert_eq!(
        handlers[1].priority, DEFAULT_PRIORITY,
        "builtin handler should be second"
    );
}
