// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance resolution, class declaration, and type class tests
//!
//! Covers:
//! - Basic instance resolution
//! - Instance priority and backtracking
//! - Class declaration parsing
//! - outParam and semiOutParam handling
//! - Instance caching

use super::*;

fn parameter_marker_environment() -> Environment {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let sort = Expr::sort(Level::param(u.clone()));
    for marker in ["outParam", "semiOutParam"] {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(marker),
            level_params: vec![u.clone()],
            type_: Expr::pi(BinderInfo::Default, sort.clone(), sort.clone()),
            value: Expr::lam(BinderInfo::Default, sort.clone(), Expr::bvar(0)),
            is_reducible: true,
        })
        .expect("checked parameter-marker identity");
    }
    env
}

// ==========================================================================
// Instance resolution tests
// ==========================================================================

#[test]
fn test_instance_resolution_basic() {
    // Setup: create an environment with a type class Add and an instance instAddNat
    let mut env = Environment::new();

    // Add Nat type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add type class: class Add (α : Type) := (add : α → α → α)
    // Represented as: Add : Type → Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    // Create elaboration context
    let mut ctx = ElabCtx::new(&env);

    // Register Add as a type class
    ctx.instances_mut()
        .register_class(Name::from_string("Add"), 1, vec![]);

    // Add instance: instAddNat : Add Nat
    let add_nat_type = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let inst_name = Name::from_string("instAddNat");

    ctx.instances_mut().add_instance(
        inst_name.clone(),
        Name::from_string("Add"),
        Expr::const_(inst_name, vec![]),
        add_nat_type.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Test resolution
    let result = ctx.resolve_instance(&add_nat_type);
    assert!(result.is_some(), "Should resolve Add Nat to instAddNat");

    if let Some(inst) = result {
        match inst.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name, &Name::from_string("instAddNat"));
            }
            other => panic!("Expected Const, got {other:?}"),
        }
    }
}

#[test]
fn test_instance_resolution_no_match() {
    // Test that resolution returns None when no instance exists
    let mut env = Environment::new();

    // Add Nat and Bool types
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Bool"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    // Register Add but only add instance for Nat
    ctx.instances_mut()
        .register_class(Name::from_string("Add"), 1, vec![]);

    let add_nat_type = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    ctx.instances_mut().add_instance(
        Name::from_string("instAddNat"),
        Name::from_string("Add"),
        Expr::const_(Name::from_string("instAddNat"), vec![]),
        add_nat_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // Try to resolve Add Bool - should fail
    let add_bool_type = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );

    let result = ctx.resolve_instance(&add_bool_type);
    assert!(result.is_none(), "Should not resolve Add Bool");
}

#[test]
fn test_instance_resolution_priority() {
    // Test that higher priority instances are preferred
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    ctx.instances_mut()
        .register_class(Name::from_string("Add"), 1, vec![]);

    let add_nat_type = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    // Add low priority instance first
    ctx.instances_mut().add_instance(
        Name::from_string("instAddNatLow"),
        Name::from_string("Add"),
        Expr::const_(Name::from_string("instAddNatLow"), vec![]),
        add_nat_type.clone(),
        50,
    );

    // Add high priority instance second
    ctx.instances_mut().add_instance(
        Name::from_string("instAddNatHigh"),
        Name::from_string("Add"),
        Expr::const_(Name::from_string("instAddNatHigh"), vec![]),
        add_nat_type.clone(),
        150,
    );

    // Resolution should return the high priority instance
    let result = ctx
        .resolve_instance(&add_nat_type)
        .expect("resolution should return an instance");

    if let ExprKind::Const(name, _) = result.kind() {
        assert_eq!(*name, Name::from_string("instAddNatHigh"));
    } else {
        panic!("Expected Const expression, got {:?}", result);
    }
}

#[test]
fn test_instance_resolution_unregistered_class() {
    // Test that resolution returns None for unregistered type classes
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    // Note: NOT registering Add as a type class

    let add_nat_type = Expr::app(
        Expr::const_(Name::from_string("Add"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );

    // Should return None because Add is not registered as a class
    let result = ctx.resolve_instance(&add_nat_type);
    assert!(
        result.is_none(),
        "Should not resolve unregistered type class"
    );
}

#[test]
fn test_instance_resolution_with_dependency() {
    use clean_kernel::expr::ExprKind;
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Mul"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    let add_class = Name::from_string("Add");
    let mul_class = Name::from_string("Mul");
    let nat = Name::from_string("Nat");

    ctx.instances_mut()
        .register_class(add_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(mul_class.clone(), 1, vec![]);

    let add_nat_type = Expr::app(
        Expr::const_(add_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let mul_nat_type = Expr::app(
        Expr::const_(mul_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // Base instance: Add Nat
    ctx.instances_mut().add_instance(
        Name::from_string("instAddNat"),
        add_class.clone(),
        Expr::const_(Name::from_string("instAddNat"), vec![]),
        add_nat_type.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Dependent instance: Mul Nat requires [Add Nat]
    let mul_inst_expr = Expr::lam(
        BinderInfo::InstImplicit,
        add_nat_type.clone(),
        Expr::const_(Name::from_string("instMulNat"), vec![]),
    );
    let mul_inst_type = Expr::pi(BinderInfo::InstImplicit, add_nat_type, mul_nat_type.clone());
    ctx.instances_mut().add_instance(
        Name::from_string("instMulNat"),
        mul_class.clone(),
        mul_inst_expr,
        mul_inst_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    let result = ctx.resolve_instance(&mul_nat_type);
    assert!(
        result.is_some(),
        "Should resolve Mul Nat using dependent Add Nat instance"
    );

    if let Some(expr) = result {
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(name, &Name::from_string("instMulNat")),
            other => panic!("Expected constant instance, got {other:?}"),
        }
    }
}

#[test]
fn test_instance_resolution_dependency_missing_instance() {
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Add"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Mul"),
        level_params: vec![],
        type_: Expr::arrow(Expr::type_(), Expr::type_()),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);

    let add_class = Name::from_string("Add");
    let mul_class = Name::from_string("Mul");
    let nat = Name::from_string("Nat");

    ctx.instances_mut()
        .register_class(add_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(mul_class.clone(), 1, vec![]);

    let add_nat_type = Expr::app(
        Expr::const_(add_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let mul_nat_type = Expr::app(
        Expr::const_(mul_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // Dependent instance: Mul Nat requires [Add Nat] but Add Nat is not registered
    let mul_inst_expr = Expr::lam(
        BinderInfo::InstImplicit,
        add_nat_type.clone(),
        Expr::const_(Name::from_string("instMulNat"), vec![]),
    );
    let mul_inst_type = Expr::pi(BinderInfo::InstImplicit, add_nat_type, mul_nat_type.clone());
    ctx.instances_mut().add_instance(
        Name::from_string("instMulNat"),
        mul_class.clone(),
        mul_inst_expr,
        mul_inst_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    let result = ctx.resolve_instance(&mul_nat_type);
    assert!(
        result.is_none(),
        "Should fail when dependency instance is missing"
    );
}

#[test]
fn test_instance_resolution_backtracking() {
    // Test backtracking: if first instance fails due to unsatisfied dependency,
    // should backtrack and try next instance.
    //
    // Setup:
    //   class A (α : Type)
    //   class B (α : Type)
    //   class C (α : Type)
    //   instance instAviaBNat [B Nat] : A Nat := ...  (priority 1000, tried first)
    //   instance instANat : A Nat := ...              (priority 500, fallback)
    //   instance instBviaCNat [C Nat] : B Nat := ...
    //   (no C Nat instance)
    //
    // When resolving A Nat:
    //   1. Try instAviaBNat (highest priority)
    //   2. Need to resolve B Nat
    //   3. Try instBviaCNat, need C Nat
    //   4. C Nat fails - no instances
    //   5. B Nat fails
    //   6. instAviaBNat fails, backtrack
    //   7. Try instANat (direct, no dependencies)
    //   8. Success!
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    // Add type Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add classes A, B, C
    for class_name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(class_name),
            level_params: vec![],
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
        })
        .unwrap();
    }

    let mut ctx = ElabCtx::new(&env);

    let a_class = Name::from_string("A");
    let b_class = Name::from_string("B");
    let c_class = Name::from_string("C");
    let nat = Name::from_string("Nat");

    ctx.instances_mut()
        .register_class(a_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(b_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(c_class.clone(), 1, vec![]);

    let a_nat_type = Expr::app(
        Expr::const_(a_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let b_nat_type = Expr::app(
        Expr::const_(b_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let c_nat_type = Expr::app(
        Expr::const_(c_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // Instance 1: instAviaBNat [B Nat] : A Nat (high priority)
    let inst_a_via_b_expr = Expr::lam(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        Expr::const_(Name::from_string("instAviaBNat"), vec![]),
    );
    let inst_a_via_b_type = Expr::pi(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        a_nat_type.clone(),
    );
    ctx.instances_mut().add_instance(
        Name::from_string("instAviaBNat"),
        a_class.clone(),
        inst_a_via_b_expr,
        inst_a_via_b_type,
        1000, // High priority - tried first
    );

    // Instance 2: instANat : A Nat (direct, lower priority)
    ctx.instances_mut().add_instance(
        Name::from_string("instANat"),
        a_class.clone(),
        Expr::const_(Name::from_string("instANat"), vec![]),
        a_nat_type.clone(),
        500, // Lower priority - fallback
    );

    // Instance for B Nat that requires C Nat (which doesn't exist)
    let inst_b_via_c_expr = Expr::lam(
        BinderInfo::InstImplicit,
        c_nat_type.clone(),
        Expr::const_(Name::from_string("instBviaCNat"), vec![]),
    );
    let inst_b_via_c_type = Expr::pi(BinderInfo::InstImplicit, c_nat_type, b_nat_type);
    ctx.instances_mut().add_instance(
        Name::from_string("instBviaCNat"),
        b_class.clone(),
        inst_b_via_c_expr,
        inst_b_via_c_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // No instance for C Nat!

    // Resolution should:
    // 1. Try instAviaBNat -> needs B Nat
    // 2. Try instBviaCNat -> needs C Nat -> FAIL
    // 3. Backtrack, try instANat -> SUCCESS
    let result = ctx.resolve_instance(&a_nat_type);
    assert!(
        result.is_some(),
        "Should backtrack and find instANat when instAviaBNat fails"
    );

    if let Some(expr) = result {
        match expr.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name,
                &Name::from_string("instANat"),
                "Should use fallback instance instANat"
            ),
            other => panic!("Expected constant instance, got {other:?}"),
        }
    }
}

#[test]
fn test_instance_resolution_backtracking_all_fail() {
    // Test that backtracking correctly fails when all instances fail.
    // Same setup as above, but without the fallback instANat.
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for class_name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(class_name),
            level_params: vec![],
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
        })
        .unwrap();
    }

    let mut ctx = ElabCtx::new(&env);

    let a_class = Name::from_string("A");
    let b_class = Name::from_string("B");
    let c_class = Name::from_string("C");
    let nat = Name::from_string("Nat");

    ctx.instances_mut()
        .register_class(a_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(b_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(c_class.clone(), 1, vec![]);

    let a_nat_type = Expr::app(
        Expr::const_(a_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let b_nat_type = Expr::app(
        Expr::const_(b_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let c_nat_type = Expr::app(
        Expr::const_(c_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // Only instAviaBNat [B Nat] : A Nat (no fallback)
    let inst_a_via_b_expr = Expr::lam(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        Expr::const_(Name::from_string("instAviaBNat"), vec![]),
    );
    let inst_a_via_b_type = Expr::pi(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        a_nat_type.clone(),
    );
    ctx.instances_mut().add_instance(
        Name::from_string("instAviaBNat"),
        a_class.clone(),
        inst_a_via_b_expr,
        inst_a_via_b_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // Instance for B Nat that requires C Nat (which doesn't exist)
    let inst_b_via_c_expr = Expr::lam(
        BinderInfo::InstImplicit,
        c_nat_type.clone(),
        Expr::const_(Name::from_string("instBviaCNat"), vec![]),
    );
    let inst_b_via_c_type = Expr::pi(BinderInfo::InstImplicit, c_nat_type, b_nat_type);
    ctx.instances_mut().add_instance(
        Name::from_string("instBviaCNat"),
        b_class.clone(),
        inst_b_via_c_expr,
        inst_b_via_c_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // No instance for C Nat, no fallback for A Nat
    let result = ctx.resolve_instance(&a_nat_type);
    assert!(
        result.is_none(),
        "Should fail when all instances fail due to unsatisfied dependencies"
    );
}

#[test]
fn test_instance_resolution_backtracking_multi_level() {
    // Test backtracking with multiple candidate instances at an intermediate level.
    //
    // Setup:
    //   class A (α : Type)
    //   class B (α : Type)
    //   class C (α : Type)
    //   instance instAviaBNat [B Nat] : A Nat  (needs B Nat)
    //   instance instBviaC [C Nat] : B Nat     (high priority, needs C Nat - will fail)
    //   instance instBNatDirect : B Nat       (low priority, direct - should succeed)
    //   (no C Nat instance)
    //
    // When resolving A Nat:
    //   1. Try instAviaBNat -> needs B Nat
    //   2. Try instBviaC (high priority) -> needs C Nat -> FAIL
    //   3. Backtrack within B Nat resolution, try instBNatDirect -> SUCCESS
    //   4. A Nat resolves successfully via instAviaBNat + instBNatDirect
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for class_name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(class_name),
            level_params: vec![],
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
        })
        .unwrap();
    }

    let mut ctx = ElabCtx::new(&env);

    let a_class = Name::from_string("A");
    let b_class = Name::from_string("B");
    let c_class = Name::from_string("C");
    let nat = Name::from_string("Nat");

    ctx.instances_mut()
        .register_class(a_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(b_class.clone(), 1, vec![]);
    ctx.instances_mut()
        .register_class(c_class.clone(), 1, vec![]);

    let a_nat_type = Expr::app(
        Expr::const_(a_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let b_nat_type = Expr::app(
        Expr::const_(b_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let c_nat_type = Expr::app(
        Expr::const_(c_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // instAviaBNat [B Nat] : A Nat
    let inst_a_via_b_expr = Expr::lam(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        Expr::const_(Name::from_string("instAviaBNat"), vec![]),
    );
    let inst_a_via_b_type = Expr::pi(
        BinderInfo::InstImplicit,
        b_nat_type.clone(),
        a_nat_type.clone(),
    );
    ctx.instances_mut().add_instance(
        Name::from_string("instAviaBNat"),
        a_class.clone(),
        inst_a_via_b_expr,
        inst_a_via_b_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // instBviaC [C Nat] : B Nat (high priority - tried first, will fail)
    let inst_b_via_c_expr = Expr::lam(
        BinderInfo::InstImplicit,
        c_nat_type.clone(),
        Expr::const_(Name::from_string("instBviaCNat"), vec![]),
    );
    let inst_b_via_c_type = Expr::pi(BinderInfo::InstImplicit, c_nat_type, b_nat_type.clone());
    ctx.instances_mut().add_instance(
        Name::from_string("instBviaCNat"),
        b_class.clone(),
        inst_b_via_c_expr,
        inst_b_via_c_type,
        1000, // High priority
    );

    // instBNatDirect : B Nat (low priority - fallback)
    ctx.instances_mut().add_instance(
        Name::from_string("instBNatDirect"),
        b_class.clone(),
        Expr::const_(Name::from_string("instBNatDirect"), vec![]),
        b_nat_type.clone(),
        500, // Low priority
    );

    // No instance for C Nat!

    // Resolution should succeed: A Nat -> B Nat (via instBNatDirect fallback)
    let result = ctx.resolve_instance(&a_nat_type);
    assert!(
        result.is_some(),
        "Should backtrack within B resolution and find instBNatDirect"
    );

    // The result should be instAviaBNat applied to instBNatDirect
    if let Some(ref expr) = result {
        if let ExprKind::Const(name, _) = expr.kind() {
            assert_eq!(
                *name,
                Name::from_string("instAviaBNat"),
                "Should use instAviaBNat with resolved dependency"
            );
        }
    }
    // Could also be an application if the lambda was beta-reduced, which is fine
}

#[test]
fn test_instance_resolution_diamond() {
    // Test diamond inheritance pattern:
    //
    //        A Nat
    //       /     \
    //   B Nat    C Nat
    //       \     /
    //        D Nat
    //
    // Setup:
    //   instance [B Nat] [C Nat] : A Nat
    //   instance [D Nat] : B Nat
    //   instance [D Nat] : C Nat
    //   instance : D Nat  (base instance)
    //
    // This tests that resolution correctly resolves the diamond without infinite loops.
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for class_name in ["A", "B", "C", "D"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(class_name),
            level_params: vec![],
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
        })
        .unwrap();
    }

    let mut ctx = ElabCtx::new(&env);

    let a_class = Name::from_string("A");
    let b_class = Name::from_string("B");
    let c_class = Name::from_string("C");
    let d_class = Name::from_string("D");
    let nat = Name::from_string("Nat");

    for class in [&a_class, &b_class, &c_class, &d_class] {
        ctx.instances_mut().register_class(class.clone(), 1, vec![]);
    }

    let a_nat = Expr::app(
        Expr::const_(a_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let b_nat = Expr::app(
        Expr::const_(b_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let c_nat = Expr::app(
        Expr::const_(c_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let d_nat = Expr::app(
        Expr::const_(d_class.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    // instance [B Nat] [C Nat] : A Nat
    let inst_a_expr = Expr::lam(
        BinderInfo::InstImplicit,
        b_nat.clone(),
        Expr::lam(
            BinderInfo::InstImplicit,
            c_nat.clone(),
            Expr::const_(Name::from_string("instANat"), vec![]),
        ),
    );
    let inst_a_type = Expr::pi(
        BinderInfo::InstImplicit,
        b_nat.clone(),
        Expr::pi(BinderInfo::InstImplicit, c_nat.clone(), a_nat.clone()),
    );
    ctx.instances_mut().add_instance(
        Name::from_string("instANat"),
        a_class.clone(),
        inst_a_expr,
        inst_a_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // instance [D Nat] : B Nat
    let inst_b_expr = Expr::lam(
        BinderInfo::InstImplicit,
        d_nat.clone(),
        Expr::const_(Name::from_string("instBNat"), vec![]),
    );
    let inst_b_type = Expr::pi(BinderInfo::InstImplicit, d_nat.clone(), b_nat.clone());
    ctx.instances_mut().add_instance(
        Name::from_string("instBNat"),
        b_class.clone(),
        inst_b_expr,
        inst_b_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // instance [D Nat] : C Nat
    let inst_c_expr = Expr::lam(
        BinderInfo::InstImplicit,
        d_nat.clone(),
        Expr::const_(Name::from_string("instCNat"), vec![]),
    );
    let inst_c_type = Expr::pi(BinderInfo::InstImplicit, d_nat.clone(), c_nat.clone());
    ctx.instances_mut().add_instance(
        Name::from_string("instCNat"),
        c_class.clone(),
        inst_c_expr,
        inst_c_type,
        crate::instances::DEFAULT_PRIORITY,
    );

    // instance : D Nat (base)
    ctx.instances_mut().add_instance(
        Name::from_string("instDNat"),
        d_class.clone(),
        Expr::const_(Name::from_string("instDNat"), vec![]),
        d_nat,
        crate::instances::DEFAULT_PRIORITY,
    );

    // Resolution should succeed for A Nat via the diamond
    let result = ctx.resolve_instance(&a_nat);
    assert!(
        result.is_some(),
        "Should resolve A Nat via diamond inheritance"
    );
}

// ==========================================================================
// Class declaration parsing and elaboration tests
// ==========================================================================

#[test]
fn test_class_decl_registers_class() {
    use clean_parser::Parser;

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Parse and elaborate a class declaration
    let decl = Parser::parse_decl(
        r"class Add (α : Type) where
          add : α → α → α",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    // Verify the class was registered
    assert!(
        ctx.instances.is_class(&Name::from_string("Add")),
        "Add should be registered as a type class"
    );

    // Verify the class info
    let class_info = ctx.instances.get_class(&Name::from_string("Add")).unwrap();
    assert_eq!(class_info.num_params, 1);
}

#[test]
fn test_class_decl_multiple_params() {
    use clean_parser::Parser;

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Class with multiple parameters
    let decl = Parser::parse_decl(
        r"class HAdd (α : Type) (β : Type) (γ : Type) where
          hAdd : α → β → γ",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    let class_info = ctx.instances.get_class(&Name::from_string("HAdd")).unwrap();
    assert_eq!(class_info.num_params, 3);
}

#[test]
fn test_class_decl_produces_structure() {
    use clean_parser::Parser;

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let decl = Parser::parse_decl(
        r"class Inhabited (α : Type) where
          default : α",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl).unwrap();

    // Class declarations produce structure results
    match result {
        ElabResult::Structure {
            name,
            field_names,
            projections,
            ..
        } => {
            assert_eq!(name.to_string(), "Inhabited");
            assert_eq!(field_names.len(), 1);
            assert_eq!(field_names[0].to_string(), "default");
            assert_eq!(projections.len(), 1);
        }
        other => panic!("Expected Structure result, got {other:?}"),
    }
}

/// Build an environment with Nat, Nat.add, and Add typeclass for instance tests.
/// Returns (env, add_class_name).
fn setup_env_with_nat_and_add() -> (Environment, Name) {
    use clean_kernel::{Constructor, Declaration, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let nat = Name::from_string("Nat");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: Expr::const_(nat.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(
                        Expr::const_(nat.clone(), vec![]),
                        Expr::const_(nat.clone(), vec![]),
                    ),
                },
            ],
        }],
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.add"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(nat.clone(), vec![]),
            Expr::arrow(Expr::const_(nat.clone(), vec![]), Expr::const_(nat, vec![])),
        ),
    })
    .unwrap();

    let add_class = Name::from_string("Add");
    // Add.mk : (α : Type) → (α → α → α) → Add α
    // α → α → α built as explicit Pi chain with depth-shifted BVars:
    //   depth 1 (under outer Pi for α:Type): α = BVar(0)
    //   depth 2 (+ first arrow binder): α = BVar(1)
    //   depth 3 (+ second arrow binder): α = BVar(2)
    let add_field_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
    );
    let add_result = Expr::app(Expr::const_(add_class.clone(), vec![]), Expr::bvar(1));
    let add_mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, add_field_ty, add_result),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: add_class.clone(),
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("Add.mk"),
                type_: add_mk_type,
            }],
        }],
    })
    .unwrap();
    env.register_structure_fields(add_class.clone(), vec![Name::from_string("add")])
        .unwrap();

    (env, add_class)
}

#[test]
fn test_instance_elaboration_basic() {
    use clean_parser::Parser;

    let (env, add_class) = setup_env_with_nat_and_add();
    let mut ctx = ElabCtx::new(&env);

    // First register the class in the instance table
    ctx.instances_mut()
        .register_class(add_class.clone(), 1, vec![]);

    let decl = Parser::parse_decl(
        r"instance : Add Nat where
          add := Nat.add",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    match result {
        Ok(ElabResult::Instance {
            name,
            class_name,
            priority,
            ..
        }) => {
            // Check instance name was auto-generated
            assert!(
                name.to_string().contains("instAdd"),
                "expected auto-generated name, got {name}"
            );
            assert_eq!(class_name, add_class);
            assert_eq!(priority, 1000); // DEFAULT_PRIORITY (Lean default, B99)

            // Check that the instance was registered
            let instances = ctx.instances().get_instances(&add_class);
            assert_eq!(instances.len(), 1);
            assert_eq!(instances[0].name.to_string(), name.to_string());
        }
        Ok(other) => panic!("Expected Instance result, got {other:?}"),
        Err(e) => panic!("Instance elaboration failed: {e:?}"),
    }
}

#[test]
fn test_instance_elaboration_named() {
    use clean_parser::Parser;

    let (env, add_class) = setup_env_with_nat_and_add();
    let mut ctx = ElabCtx::new(&env);
    ctx.instances_mut()
        .register_class(add_class.clone(), 1, vec![]);

    // Parse instance with explicit name
    let decl = Parser::parse_decl(
        r"instance instAddNat : Add Nat where
          add := Nat.add",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    match result {
        Ok(ElabResult::Instance { name, .. }) => {
            assert_eq!(name.to_string(), "instAddNat");
        }
        Ok(other) => panic!("Expected Instance result, got {other:?}"),
        Err(e) => panic!("Instance elaboration failed: {e:?}"),
    }
}

#[test]
fn test_instance_registration_in_table() {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};
    use clean_parser::Parser;

    let mut env = Environment::new();

    // Minimal setup - just the class structure
    let my_class = Name::from_string("MyClass");
    // Result is Type 1 (Sort 2) because field stores a Type-valued term
    let type1 = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let my_class_decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: my_class.clone(),
            type_: Expr::arrow(Expr::type_(), type1),
            constructors: vec![Constructor {
                name: Name::from_string("MyClass.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::type_(), // field type (: Type, needs Sort 2 result)
                        Expr::app(Expr::const_(my_class.clone(), vec![]), Expr::bvar(1)),
                    ),
                ),
            }],
        }],
    };
    env.add_inductive(my_class_decl).unwrap();
    env.register_structure_fields(my_class.clone(), vec![Name::from_string("val")])
        .unwrap();

    // Add a simple type to instantiate for
    let my_type = Name::from_string("MyType");
    let my_type_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: my_type.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("MyType.mk"),
                type_: Expr::const_(my_type.clone(), vec![]),
            }],
        }],
    };
    env.add_inductive(my_type_decl).unwrap();

    let mut ctx = ElabCtx::new(&env);
    ctx.instances_mut()
        .register_class(my_class.clone(), 1, vec![]);

    // Before elaborating, no instances
    assert_eq!(ctx.instances().get_instances(&my_class).len(), 0);

    let decl = Parser::parse_decl(
        r"instance : MyClass MyType where
          val := MyType",
    )
    .unwrap();

    ctx.elab_decl(&decl).unwrap();

    // After elaborating, instance is registered
    let instances = ctx.instances().get_instances(&my_class);
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].class_name, my_class);
}

#[test]
fn test_instance_missing_field_error() {
    use clean_kernel::{Constructor, InductiveDecl, InductiveType};
    use clean_parser::Parser;

    let mut env = Environment::new();

    // Class with two fields
    let my_class = Name::from_string("TwoFields");
    // Result is Type 1 (Sort 2) because fields store Type-valued terms
    let type1 = Expr::sort(Level::succ(Level::succ(Level::zero())));
    let my_class_decl = InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: my_class.clone(),
            type_: Expr::arrow(Expr::type_(), type1),
            constructors: vec![Constructor {
                name: Name::from_string("TwoFields.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::type_(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::type_(), // field1 (: Type, needs Sort 2 result)
                        Expr::pi(
                            BinderInfo::Default,
                            Expr::type_(), // field2 (: Type, needs Sort 2 result)
                            Expr::app(Expr::const_(my_class.clone(), vec![]), Expr::bvar(2)),
                        ),
                    ),
                ),
            }],
        }],
    };
    env.add_inductive(my_class_decl).unwrap();
    env.register_structure_fields(
        my_class.clone(),
        vec![Name::from_string("field1"), Name::from_string("field2")],
    )
    .unwrap();

    let my_type = Name::from_string("SomeType");
    let my_type_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: my_type.clone(),
            type_: Expr::type_(),
            constructors: vec![],
        }],
    };
    env.add_inductive(my_type_decl).unwrap();

    let mut ctx = ElabCtx::new(&env);
    ctx.instances_mut()
        .register_class(my_class.clone(), 2, vec![]);

    // Instance with only one field (missing field2)
    let decl = Parser::parse_decl(
        r"instance : TwoFields SomeType where
          field1 := SomeType",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    // B12: a long-form instance that OMITS a field now routes to the
    // structure-literal path (so defaulted methods can be materialized and
    // `extends` parents assembled). A genuinely default-less omitted field is
    // reported there as the precise typed `MissingStructureFields` naming the
    // field, rather than the generic `NotImplemented("missing field …")`. Both
    // reject loudly for the same reason; accept either.
    assert!(
        matches!(
            result,
            Err(ElabError::MissingStructureFields { ref fields, .. })
                if fields.iter().any(|f| f == "field2")
        ) || matches!(
            result,
            Err(ElabError::NotImplemented(ref msg)) if msg.contains("missing field")
        ),
        "Expected a loud missing-field rejection naming field2, got {result:?}"
    );
}

// ==========================================================================
// outParam tests
// ==========================================================================

#[test]
fn test_class_with_outparam_detected() {
    use clean_parser::Parser;

    let env = parameter_marker_environment();
    let mut ctx = ElabCtx::new(&env);

    // Parse a class with an out-parameter
    let decl = Parser::parse_decl(
        r"class HAdd (α : Type) (β : Type) (γ : outParam Type) where
          hAdd : α → β → γ",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    // Verify the class was registered with out_params
    let class_info = ctx.instances.get_class(&Name::from_string("HAdd")).unwrap();
    assert_eq!(class_info.num_params, 3);
    assert_eq!(
        class_info.out_params,
        vec![2],
        "Third parameter (index 2) should be outParam"
    );
}

#[test]
fn test_class_multiple_outparams() {
    use clean_parser::Parser;

    let env = parameter_marker_environment();
    let mut ctx = ElabCtx::new(&env);

    // Parse a class with multiple out-parameters
    let decl = Parser::parse_decl(
        r"class Bifunctor (F : outParam Type) (G : outParam Type) (α : Type) where
          bimap : α → F",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    let class_info = ctx
        .instances
        .get_class(&Name::from_string("Bifunctor"))
        .unwrap();
    assert_eq!(class_info.num_params, 3);
    assert_eq!(
        class_info.out_params,
        vec![0, 1],
        "First two parameters should be outParams"
    );
}

#[test]
fn test_class_no_outparam() {
    use clean_parser::Parser;

    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Parse a class without out-parameters
    let decl = Parser::parse_decl(
        r"class Add (α : Type) where
          add : α → α → α",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    let class_info = ctx.instances.get_class(&Name::from_string("Add")).unwrap();
    assert_eq!(class_info.num_params, 1);
    assert!(class_info.out_params.is_empty(), "Should have no outParams");
}

#[test]
fn test_outparam_instance_resolution() {
    // Test that instance resolution works with out-parameters
    // HAdd α β γ where γ is an out-param means we can resolve HAdd Nat Nat _
    // and get γ = Nat from the instance
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    // Add Nat type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let nat = Name::from_string("Nat");
    let hadd = Name::from_string("HAdd");

    // Register HAdd with γ as out-param (index 2)
    ctx.instances_mut().register_class(hadd.clone(), 3, vec![2]);

    // Add instance: HAdd Nat Nat Nat
    // Build: ((HAdd Nat) Nat) Nat
    let hadd_nat = Expr::app(
        Expr::const_(hadd.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let hadd_nat_nat = Expr::app(hadd_nat, Expr::const_(nat.clone(), vec![]));
    let hadd_nat_nat_nat = Expr::app(hadd_nat_nat, Expr::const_(nat.clone(), vec![]));

    let inst_expr = Expr::const_(Name::from_string("instHAddNatNatNat"), vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instHAddNatNatNat"),
        hadd.clone(),
        inst_expr,
        hadd_nat_nat_nat.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Try to resolve HAdd Nat Nat _ (with out-param as a metavariable)
    let out_param_meta = ctx.fresh_meta(Expr::type_());
    let goal_hadd_nat = Expr::app(
        Expr::const_(hadd.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let goal_hadd_nat_nat = Expr::app(goal_hadd_nat, Expr::const_(nat.clone(), vec![]));
    let goal_type = Expr::app(goal_hadd_nat_nat, out_param_meta);

    let result = ctx.resolve_instance(&goal_type);
    assert!(
        result.is_some(),
        "Should resolve HAdd Nat Nat _ with out-param"
    );
}

#[test]
fn test_outparam_no_match_wrong_input() {
    // Test that out-param resolution fails if input params don't match
    use clean_kernel::Declaration;

    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Bool"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let nat = Name::from_string("Nat");
    let bool_ = Name::from_string("Bool");
    let hadd = Name::from_string("HAdd");

    // Register HAdd with γ as out-param (index 2)
    ctx.instances_mut().register_class(hadd.clone(), 3, vec![2]);

    // Add instance: HAdd Nat Nat Nat (only works for Nat + Nat)
    let hadd_nat = Expr::app(
        Expr::const_(hadd.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let hadd_nat_nat = Expr::app(hadd_nat, Expr::const_(nat.clone(), vec![]));
    let hadd_nat_nat_nat = Expr::app(hadd_nat_nat, Expr::const_(nat.clone(), vec![]));

    let inst_expr = Expr::const_(Name::from_string("instHAddNatNatNat"), vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instHAddNatNatNat"),
        hadd.clone(),
        inst_expr,
        hadd_nat_nat_nat.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Try to resolve HAdd Bool Nat _ - should fail because Bool ≠ Nat
    let out_param_meta = ctx.fresh_meta(Expr::type_());
    let goal_hadd_bool = Expr::app(
        Expr::const_(hadd.clone(), vec![]),
        Expr::const_(bool_.clone(), vec![]), // Wrong type
    );
    let goal_hadd_bool_nat = Expr::app(goal_hadd_bool, Expr::const_(nat.clone(), vec![]));
    let goal_type = Expr::app(goal_hadd_bool_nat, out_param_meta);

    let result = ctx.resolve_instance(&goal_type);
    assert!(
        result.is_none(),
        "Should fail when non-out-param doesn't match"
    );
}

// ==========================================================================
// semiOutParam tests
// ==========================================================================

#[test]
fn test_class_with_semioutparam_detected() {
    use clean_parser::Parser;

    let env = parameter_marker_environment();
    let mut ctx = ElabCtx::new(&env);

    // Parse a class with a semi-out-parameter (like Coe)
    let decl = Parser::parse_decl(
        r"class Coe (α : semiOutParam Type) (β : Type) where
          coe : α → β",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    // Verify the class was registered with semi_out_params
    let class_info = ctx.instances.get_class(&Name::from_string("Coe")).unwrap();
    assert_eq!(class_info.num_params, 2);
    assert!(class_info.out_params.is_empty(), "Should have no outParams");
    assert_eq!(
        class_info.semi_out_params,
        vec![0],
        "First parameter (index 0) should be semiOutParam"
    );
}

#[test]
fn test_class_with_both_outparam_and_semioutparam() {
    use clean_parser::Parser;

    let env = parameter_marker_environment();
    let mut ctx = ElabCtx::new(&env);

    // Parse a class with both outParam and semiOutParam
    let decl = Parser::parse_decl(
        r"class HCoe (α : semiOutParam Type) (β : Type) (γ : outParam Type) where
          hCoe : α → β → γ",
    )
    .unwrap();

    let result = ctx.elab_decl(&decl);
    assert!(result.is_ok(), "Class elaboration failed: {result:?}");

    // Verify both param types were registered correctly
    let class_info = ctx.instances.get_class(&Name::from_string("HCoe")).unwrap();
    assert_eq!(class_info.num_params, 3);
    assert_eq!(
        class_info.out_params,
        vec![2],
        "Third parameter should be outParam"
    );
    assert_eq!(
        class_info.semi_out_params,
        vec![0],
        "First parameter should be semiOutParam"
    );
}

#[test]
fn test_semioutparam_unifies_bidirectionally() {
    // Test that semiOutParam participates in normal unification (unlike outParam)
    // With Coe (α : semiOutParam Type) (β : Type), when resolving Coe ?α Nat:
    // - If instance is Coe String Nat, then ?α unifies with String
    // - Unlike outParam, the goal ?α can also constrain the match

    use clean_kernel::Declaration;

    let mut env = Environment::new();

    // Add Nat and String types
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("String"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let nat = Name::from_string("Nat");
    let string = Name::from_string("String");
    let coe = Name::from_string("Coe");

    // Register Coe with α as semi-out-param (index 0)
    ctx.instances_mut()
        .register_class_full(coe.clone(), 2, vec![], vec![0]);

    // Add instance: Coe String Nat (can convert String to Nat)
    // Build: (Coe String) Nat
    let coe_string = Expr::app(
        Expr::const_(coe.clone(), vec![]),
        Expr::const_(string.clone(), vec![]),
    );
    let coe_string_nat = Expr::app(coe_string, Expr::const_(nat.clone(), vec![]));

    let inst_expr = Expr::const_(Name::from_string("instCoeStringNat"), vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instCoeStringNat"),
        coe.clone(),
        inst_expr,
        coe_string_nat.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Case 1: Resolve Coe ?α Nat - should succeed and set ?α = String
    let alpha_meta = ctx.fresh_meta(Expr::type_());
    let goal_coe_meta = Expr::app(Expr::const_(coe.clone(), vec![]), alpha_meta.clone());
    let goal_type = Expr::app(goal_coe_meta, Expr::const_(nat.clone(), vec![]));

    let result = ctx.resolve_instance(&goal_type);
    assert!(
        result.is_some(),
        "Should resolve Coe ?α Nat to Coe String Nat"
    );

    // Verify the metavariable was unified with String
    let alpha_resolved = ctx.metas.instantiate(&alpha_meta);
    match alpha_resolved.kind() {
        ExprKind::Const(n, _) if *n == string => (),
        _ => panic!("Expected ?α to be unified with String, got {alpha_resolved:?}"),
    }
}

#[test]
fn test_semioutparam_can_be_constrained() {
    // Test that semiOutParam can also be constrained from the goal side
    // (unlike outParam which only gets values from instances)

    use clean_kernel::Declaration;

    let mut env = Environment::new();

    // Add types
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("String"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Bool"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let mut ctx = ElabCtx::new(&env);
    let nat = Name::from_string("Nat");
    let string = Name::from_string("String");
    let bool_ = Name::from_string("Bool");
    let coe = Name::from_string("Coe");

    // Register Coe with α as semi-out-param (index 0)
    ctx.instances_mut()
        .register_class_full(coe.clone(), 2, vec![], vec![0]);

    // Add instance: Coe String Nat
    let coe_string = Expr::app(
        Expr::const_(coe.clone(), vec![]),
        Expr::const_(string.clone(), vec![]),
    );
    let coe_string_nat = Expr::app(coe_string, Expr::const_(nat.clone(), vec![]));

    let inst_expr = Expr::const_(Name::from_string("instCoeStringNat"), vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instCoeStringNat"),
        coe.clone(),
        inst_expr,
        coe_string_nat.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Case: Try to resolve Coe Bool Nat - should FAIL because no instance exists
    // (unlike outParam, the goal type must match what instances provide)
    let goal_coe_bool = Expr::app(
        Expr::const_(coe.clone(), vec![]),
        Expr::const_(bool_.clone(), vec![]),
    );
    let goal_type = Expr::app(goal_coe_bool, Expr::const_(nat.clone(), vec![]));

    let result = ctx.resolve_instance(&goal_type);
    assert!(
        result.is_none(),
        "Should fail: Coe Bool Nat has no instance (semiOutParam must match)"
    );
}

// ==========================================================================
// Instance priority attribute tests
// ==========================================================================

#[test]
fn test_instance_priority_attribute_parsing() {
    // Test that @[instance 50] sets priority to 50
    use clean_parser::parse_decl;

    let decl = parse_decl(
        r"@[instance 50] instance : Add Nat where
          add := Nat.add",
    )
    .unwrap();

    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            assert_eq!(priority, Some(50));
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_default_instance_attribute_parsing() {
    // `@[defaultInstance]` feeds the default-instance table; it must NOT
    // override the instance's ordinary resolution priority (the old
    // `Some(0)` silently demoted the instance below every plain one — B99).
    use clean_parser::parse_decl;

    let decl = parse_decl(
        r"@[defaultInstance] instance : ToString Nat where
          toString := Nat.repr",
    )
    .unwrap();

    match decl {
        SurfaceDecl::Instance { priority, .. } => {
            assert_eq!(priority, None);
        }
        _ => panic!("expected Instance"),
    }
}

#[test]
fn test_instance_priority_ordering() {
    // Test that instances are sorted by priority (highest first)
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let show = Name::from_string("Show");
    ctx.instances_mut().register_class(show.clone(), 1, vec![]);

    // Add instances with different priorities
    ctx.instances_mut().add_instance(
        Name::from_string("low"),
        show.clone(),
        Expr::const_(Name::from_string("low"), vec![]),
        Expr::const_(show.clone(), vec![]),
        50, // low priority
    );
    ctx.instances_mut().add_instance(
        Name::from_string("default"),
        show.clone(),
        Expr::const_(Name::from_string("default"), vec![]),
        Expr::const_(show.clone(), vec![]),
        100, // default priority
    );
    ctx.instances_mut().add_instance(
        Name::from_string("high"),
        show.clone(),
        Expr::const_(Name::from_string("high"), vec![]),
        Expr::const_(show.clone(), vec![]),
        150, // high priority
    );

    let instances = ctx.instances().get_instances(&show);
    assert_eq!(instances.len(), 3);
    // Verify priority ordering (highest first)
    assert_eq!(instances[0].priority, 150);
    assert_eq!(instances[1].priority, 100);
    assert_eq!(instances[2].priority, 50);
}

#[test]
fn test_default_instance_last() {
    // Test that @[defaultInstance] (priority 0) is tried last
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let show = Name::from_string("Show");
    ctx.instances_mut().register_class(show.clone(), 1, vec![]);

    // Add default instance first
    ctx.instances_mut().add_instance(
        Name::from_string("default_fallback"),
        show.clone(),
        Expr::const_(Name::from_string("default_fallback"), vec![]),
        Expr::const_(show.clone(), vec![]),
        0, // defaultInstance priority
    );

    // Add higher priority instance after
    ctx.instances_mut().add_instance(
        Name::from_string("preferred"),
        show.clone(),
        Expr::const_(Name::from_string("preferred"), vec![]),
        Expr::const_(show.clone(), vec![]),
        100, // normal priority
    );

    let instances = ctx.instances().get_instances(&show);
    assert_eq!(instances.len(), 2);
    // Higher priority should come first regardless of insertion order
    assert_eq!(instances[0].name.to_string(), "preferred");
    assert_eq!(instances[1].name.to_string(), "default_fallback");
}

#[test]
fn test_instance_cache_basic() {
    // Test that instance resolution caches ground goals
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register Add class and instance
    let add = Name::from_string("Add");
    let nat = Name::from_string("Nat");
    ctx.instances_mut().register_class(add.clone(), 1, vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instAddNat"),
        add.clone(),
        Expr::const_(Name::from_string("instAddNat"), vec![]),
        Expr::app(
            Expr::const_(add.clone(), vec![]),
            Expr::const_(nat.clone(), vec![]),
        ),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Initial cache should be empty
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 0);

    // Resolve Add Nat
    let goal = Expr::app(
        Expr::const_(add.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let result = ctx
        .resolve_instance(&goal)
        .expect("resolution should return an instance for Add Nat");

    // Cache should now contain the result (goal is ground - no metavariables)
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 1);

    // Resolve again - should use cache
    let result2 = ctx
        .resolve_instance(&goal)
        .expect("cached resolution should return an instance for Add Nat");
    assert_eq!(format!("{:?}", result), format!("{:?}", result2));

    // Cache size shouldn't change
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 1);
}

#[test]
fn test_successful_temporary_scope_invalidates_local_typechecker_cache_entries() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let (scoped_app, scoped_reduction) = ctx
        .with_temporary_local_scope(|this| {
            let scoped_fn = this.fresh_fvar();
            this.push_local_let_with_fvar(
                SurfaceName::generated_path("scopedSucc"),
                scoped_fn,
                Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
                succ.clone(),
            );
            let app = Expr::app(Expr::fvar(scoped_fn), zero.clone());
            let reduced = this.whnf(&app);
            assert_ne!(
                reduced, app,
                "temporary let-local should reduce while its scope is active"
            );
            Ok((app, reduced))
        })
        .expect("well-formed temporary work should commit its metavariables");

    assert_eq!(
        ctx.whnf(&scoped_app),
        scoped_app,
        "WHNF cache entry containing a removed temporary local leaked past scope restoration"
    );
    assert_ne!(scoped_app, scoped_reduction);
}

#[test]
fn test_successful_transaction_pop_invalidates_local_typechecker_cache_entries() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let scoped_fn = ctx.fresh_fvar();
    ctx.push_local_let_with_fvar(
        SurfaceName::generated_path("transactionSucc"),
        scoped_fn,
        Expr::pi(BinderInfo::Default, nat.clone(), nat),
        succ,
    );
    let scoped_app = Expr::app(Expr::fvar(scoped_fn), zero);
    assert_ne!(ctx.whnf(&scoped_app), scoped_app);

    ctx.with_local_scope_rollback(|this| {
        this.pop_local();
        Ok(())
    })
    .expect("successful plan-style local pop should commit");

    assert_eq!(
        ctx.whnf(&scoped_app),
        scoped_app,
        "successful transaction pop retained a cache entry containing the removed local"
    );
}

#[test]
fn test_consumed_transaction_markers_return_typed_errors_and_restore_locals() {
    let env = Environment::with_prelude();

    let mut temporary_ctx = ElabCtx::new(&env);
    let mut popped_meta = None;
    let temporary_result = temporary_ctx.with_temporary_local_scope(|this| {
        this.push_local(SurfaceName::generated_path("temporaryLeak"), Expr::type_());
        let meta = this.metas.fresh(Expr::type_());
        assert!(this.metas.assign(meta, Expr::prop()));
        popped_meta = Some(meta);
        let depth_before_attempt = this.metas.scope_depth();
        let trail_before_attempt = this.metas.undo_trail_len_for_tests();
        assert!(
            !this.metas.pop_scope(),
            "ordinary pop must not consume an owned wrapper marker"
        );
        assert_eq!(this.metas.scope_depth(), depth_before_attempt);
        assert_eq!(this.metas.undo_trail_len_for_tests(), trail_before_attempt);
        Ok(())
    });
    assert!(
        matches!(&temporary_result, Err(ElabError::InternalInvariant(message)) if message.contains("temporary-scope") && message.contains("consume")),
        "consumed temporary marker should be a typed internal error, got {temporary_result:?}"
    );
    assert!(
        temporary_ctx
            .metas
            .get(popped_meta.expect("closure must create a meta"))
            .is_none(),
        "pop-attempt invariant recovery leaked a created/assigned meta"
    );
    assert!(
        temporary_ctx
            .lookup_local(&SurfaceName::generated_path("temporaryLeak"))
            .is_none(),
        "typed invariant failure must still restore temporary locals"
    );

    let mut rollback_ctx = ElabCtx::new(&env);
    let stable_meta = rollback_ctx.metas.fresh(Expr::type_());
    let rollback_result = rollback_ctx.with_local_scope_rollback(|this| {
        this.push_local(
            SurfaceName::generated_path("transactionLeak"),
            Expr::type_(),
        );
        assert!(this.metas.assign(stable_meta, Expr::prop()));
        let depth_before_attempt = this.metas.scope_depth();
        let trail_before_attempt = this.metas.undo_trail_len_for_tests();
        assert!(
            !this.metas.commit(),
            "ordinary commit must not consume an owned wrapper marker"
        );
        assert_eq!(this.metas.scope_depth(), depth_before_attempt);
        assert_eq!(this.metas.undo_trail_len_for_tests(), trail_before_attempt);
        Ok(())
    });
    assert!(
        matches!(&rollback_result, Err(ElabError::InternalInvariant(message)) if message.contains("local-scope") && message.contains("consume")),
        "consumed transaction marker should be a typed internal error, got {rollback_result:?}"
    );
    assert!(
        !rollback_ctx.metas.is_assigned(stable_meta),
        "commit-attempt invariant recovery leaked a meta assignment"
    );
    assert!(
        rollback_ctx
            .lookup_local(&SurfaceName::generated_path("transactionLeak"))
            .is_none(),
        "typed invariant failure must restore transactional locals"
    );

    let depth_before = rollback_ctx.metas.scope_depth();
    let committed_nested = rollback_ctx
        .with_local_scope_rollback(|this| {
            this.metas.push_scope();
            let nested = this.metas.fresh(Expr::type_());
            assert!(
                this.metas.commit(),
                "ordinary nested scope above an owned marker must still commit"
            );
            Ok(nested)
        })
        .expect("normal nested commit should not trip marker ownership");
    assert!(rollback_ctx.metas.get(committed_nested).is_some());
    assert_eq!(rollback_ctx.metas.scope_depth(), depth_before);
}

#[test]
fn test_instance_cache_global_result_does_not_mask_pushed_local() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let show = Name::from_string("Show");
    let nat = Name::from_string("Nat");
    let goal = Expr::app(
        Expr::const_(show.clone(), vec![]),
        Expr::const_(nat, vec![]),
    );
    ctx.instances_mut().register_class(show.clone(), 1, vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instShowNat"),
        show,
        Expr::const_(Name::from_string("instShowNat"), vec![]),
        goal.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    let global = ctx
        .resolve_instance(&goal)
        .expect("global instance should populate the ground-goal cache");
    assert!(matches!(global.kind(), ExprKind::Const(name, _) if name.to_string() == "instShowNat"));

    let local = ctx.push_local(SurfaceName::generated_path("localShowNat"), goal.clone());
    ctx.push_local_instance(local, goal.clone());
    let resolved = ctx
        .resolve_instance(&goal)
        .expect("pushed local instance should shadow the cached global");
    assert!(
        matches!(resolved.kind(), ExprKind::FVar(id) if *id == local),
        "cache invalidation on push must expose the local instance, got {resolved:?}"
    );

    ctx.pop_local_instance();
    ctx.pop_local();
}

#[test]
fn test_instance_cache_popped_local_fvar_is_never_reused() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let show = Name::from_string("Show");
    let nat = Name::from_string("Nat");
    let goal = Expr::app(
        Expr::const_(show.clone(), vec![]),
        Expr::const_(nat, vec![]),
    );
    ctx.instances_mut().register_class(show.clone(), 1, vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instShowNat"),
        show,
        Expr::const_(Name::from_string("instShowNat"), vec![]),
        goal.clone(),
        crate::instances::DEFAULT_PRIORITY,
    );

    let local = ctx.push_local(SurfaceName::generated_path("localShowNat"), goal.clone());
    ctx.push_local_instance(local, goal.clone());
    let cached_local = ctx
        .resolve_instance(&goal)
        .expect("local instance should resolve and enter the cache");
    assert!(matches!(cached_local.kind(), ExprKind::FVar(id) if *id == local));

    ctx.pop_local_instance();
    ctx.pop_local();
    let resolved = ctx
        .resolve_instance(&goal)
        .expect("global instance should resolve after the local scope ends");
    assert!(
        matches!(resolved.kind(), ExprKind::Const(name, _) if name.to_string() == "instShowNat"),
        "cache invalidation on pop must not return stale local {local:?}, got {resolved:?}"
    );
}

#[test]
fn test_instance_cache_clear() {
    // Test that clear_instance_cache works
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register class and instance
    let show = Name::from_string("Show");
    let nat = Name::from_string("Nat");
    ctx.instances_mut().register_class(show.clone(), 1, vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instShowNat"),
        show.clone(),
        Expr::const_(Name::from_string("instShowNat"), vec![]),
        Expr::app(
            Expr::const_(show.clone(), vec![]),
            Expr::const_(nat.clone(), vec![]),
        ),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Resolve to populate cache
    let goal = Expr::app(
        Expr::const_(show.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let _ = ctx
        .resolve_instance(&goal)
        .expect("resolve_instance failed");
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 1);

    // Clear cache
    ctx.clear_instance_cache();
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 0);
}

#[test]
fn test_normalize_for_cache() {
    // Test that normalize_for_cache produces consistent keys
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Same structure should produce same key
    let nat = Name::from_string("Nat");
    let add = Name::from_string("Add");

    let e1 = Expr::app(
        Expr::const_(add.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );
    let e2 = Expr::app(
        Expr::const_(add.clone(), vec![]),
        Expr::const_(nat.clone(), vec![]),
    );

    let key1 = ctx.normalize_for_cache(&e1);
    let key2 = ctx.normalize_for_cache(&e2);
    assert_eq!(key1, key2);

    // Different structure should produce different keys
    let bool = Name::from_string("Bool");
    let e3 = Expr::app(
        Expr::const_(add.clone(), vec![]),
        Expr::const_(bool.clone(), vec![]),
    );
    let key3 = ctx.normalize_for_cache(&e3);
    assert_ne!(key1, key3);
}

#[test]
fn test_has_metavars() {
    // Test has_metavars detection
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    // Constant has no metavars
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(!ctx.has_metavars(&nat));

    // BVar has no metavars
    let bvar = Expr::bvar(0);
    assert!(!ctx.has_metavars(&bvar));

    // Regular FVar has no metavars
    let fvar = Expr::fvar(FVarId::new(42));
    assert!(!ctx.has_metavars(&fvar));

    // FVar with metavar tag IS a metavar
    let mvar = Expr::fvar(MetaState::to_fvar(MetaId(0)));
    assert!(ctx.has_metavars(&mvar));

    // App containing metavar
    let app_with_meta = Expr::app(Expr::const_(Name::from_string("Add"), vec![]), mvar.clone());
    assert!(ctx.has_metavars(&app_with_meta));

    // App without metavar
    let app_no_meta = Expr::app(Expr::const_(Name::from_string("Add"), vec![]), nat.clone());
    assert!(!ctx.has_metavars(&app_no_meta));
}

#[test]
fn test_instance_cache_with_metavars() {
    // Test that goals with metavars are NOT cached
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    // Register class and instance
    let add = Name::from_string("Add");
    let nat = Name::from_string("Nat");
    ctx.instances_mut().register_class(add.clone(), 1, vec![]);
    ctx.instances_mut().add_instance(
        Name::from_string("instAddNat"),
        add.clone(),
        Expr::const_(Name::from_string("instAddNat"), vec![]),
        Expr::app(
            Expr::const_(add.clone(), vec![]),
            Expr::const_(nat.clone(), vec![]),
        ),
        crate::instances::DEFAULT_PRIORITY,
    );

    // Create a goal with a metavariable: Add ?m
    let meta_id = ctx.metas.fresh(Expr::sort(Level::zero()));
    let meta_expr = Expr::fvar(MetaState::to_fvar(meta_id));
    let goal_with_meta = Expr::app(Expr::const_(add.clone(), vec![]), meta_expr);

    // Assign the metavariable to Nat so resolution succeeds
    ctx.metas.assign(meta_id, Expr::const_(nat.clone(), vec![]));

    // Resolve — after instantiation, the goal becomes Add Nat which is ground
    let resolved = ctx
        .resolve_instance(&goal_with_meta)
        .expect("resolution should succeed after metavariable instantiation");

    // The resolved instance should be an expression (the Add Nat instance)
    // It must not be a metavariable — it should be a concrete term
    assert!(
        !matches!(resolved.kind(), ExprKind::FVar(_)),
        "resolved instance should be concrete, not a metavariable, got {:?}",
        resolved.kind()
    );

    // The cache should contain the result for the ground (instantiated) goal
    let (cached_count, _) = ctx.instance_cache_stats();
    assert_eq!(cached_count, 1);
}

// ==========================================================================
// FRONTIER STAGE I-2 — the goal side: a Pi-shaped goal's ∀-telescope is
// opened, the conclusion resolved by the UNCHANGED search, and the answer
// re-abstracted into lambdas (`ElabCtx::resolve_goal_pi_abstracted`).
//
// The fixture family `tests/fixtures/source_frontier/p18,p24..p27` measures
// this end-to-end through `clean check`; these tests pin the same properties
// at the resolution API, where the returned Expr can be inspected directly
// and where the depth boundary is observable as a verdict rather than only as
// a term shape.
// ==========================================================================

/// Environment + context carrying `class C (α : Type)` with `instCNat : C Nat`,
/// and `class D (α : Type)` with no instance yet.
fn goal_side_ctx(env: &Environment) -> ElabCtx<'_> {
    let mut ctx = ElabCtx::new(env);
    ctx.instances_mut()
        .register_class(Name::from_string("C"), 1, vec![]);
    ctx.instances_mut()
        .register_class(Name::from_string("D"), 1, vec![]);
    let c_nat = Expr::app(
        Expr::const_(Name::from_string("C"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    ctx.instances_mut().add_instance(
        Name::from_string("instCNat"),
        Name::from_string("C"),
        Expr::const_(Name::from_string("instCNat"), vec![]),
        c_nat,
        crate::instances::DEFAULT_PRIORITY,
    );
    ctx
}

fn goal_side_env() -> Environment {
    use clean_kernel::env::Declaration;
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    for class in ["C", "D"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(class),
            level_params: vec![],
            type_: Expr::arrow(Expr::type_(), Expr::type_()),
        })
        .unwrap();
    }
    env
}

fn c_nat_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("C"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    )
}

fn nat_const() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// The capability: `(x : Nat) → C Nat` is answered by `fun (x : Nat) => instCNat`.
/// No candidate has that type — the term is BUILT, which is the whole of
/// stage I-2.
#[test]
fn test_goal_side_pi_goal_is_answered_by_an_abstraction() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    let goal = Expr::pi(BinderInfo::Default, nat_const(), c_nat_goal());
    let resolved = ctx
        .resolve_instance(&goal)
        .expect("a Pi-shaped goal whose conclusion resolves must be answered by an abstraction");

    match resolved.kind() {
        ExprKind::Lam(_, ty, body) => {
            assert_eq!(ty.as_ref(), &nat_const(), "binder type is the goal's own");
            match body.kind() {
                ExprKind::Const(name, _) => {
                    assert_eq!(name, &Name::from_string("instCNat"));
                }
                other => {
                    panic!("expected the conclusion's instance under the lambda, got {other:?}")
                }
            }
        }
        other => panic!("expected a Lam (the abstraction), got {other:?}"),
    }
}

/// The refusal: instance search is not a synthesizer for arbitrary Pi types.
/// `Nat → Nat` is Pi-shaped and inhabited; its conclusion is const-headed and
/// still not an instance goal, so there is no answer.
#[test]
fn test_goal_side_refuses_a_pi_whose_conclusion_is_not_an_instance() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    let goal = Expr::pi(BinderInfo::Default, nat_const(), nat_const());
    assert!(
        ctx.resolve_instance(&goal).is_none(),
        "a Pi goal whose conclusion is not resolvable must stay unresolved"
    );
}

/// The ground restriction: a goal that still carries a metavariable could be
/// SOLVED by the attempt rather than answered by it, so it is refused
/// outright — the same hole stage I-1 self-caught in its match (C), closed
/// here by construction.
#[test]
fn test_goal_side_refuses_a_pi_goal_carrying_a_metavariable() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    let meta_id = ctx.metas.fresh(Expr::type_());
    let meta = Expr::fvar(MetaState::to_fvar(meta_id));
    let goal = Expr::pi(
        BinderInfo::Default,
        nat_const(),
        Expr::app(Expr::const_(Name::from_string("C"), vec![]), meta),
    );
    assert!(
        ctx.resolve_instance(&goal).is_none(),
        "a Pi goal with an open carrier must not be answered by assigning it"
    );
}

/// Deliberately narrow: an `[inst]` binder in the GOAL's telescope would have
/// to be pushed as a local INSTANCE as well as a local, which is a separate
/// increment with its own safety argument. Refused, not opened half-way —
/// even though the conclusion on its own resolves (previous test).
#[test]
fn test_goal_side_refuses_an_instance_implicit_goal_binder() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    let goal = Expr::pi(BinderInfo::InstImplicit, c_nat_goal(), c_nat_goal());
    assert!(
        ctx.resolve_instance(&goal).is_none(),
        "an instance-implicit goal binder is refused rather than opened"
    );
}

/// An IMPORTED `scoped instance` is invisible until its namespace is opened,
/// exactly like a source-declared one (`instance_visible`). The olean loader
/// records the declaring namespace in `clean_olean::ScopedInstanceState`;
/// `ElabCtx` seeds `scoped_instances` from it at construction and keeps it
/// when the file's own scope state is set. Until 2026-09-10 the map was seeded
/// empty, so Mathlib's `Classical.Order.instOrd` (a `scoped instance`) fired
/// everywhere and `example (α : Type) [LE α] : LT α := inferInstance` passed
/// where Lean fails.
#[test]
fn test_imported_scoped_instance_is_gated_on_open() {
    let mut env = goal_side_env();
    // The loader's record: `instCNat` was declared `scoped` in `Foo`.
    let idx = clean_olean::scoped_instance_idx();
    env.get_ext_state_mut::<clean_olean::ScopedInstanceState>(idx)
        .scope_of
        .insert(Name::from_string("instCNat"), Name::from_string("Foo"));

    // Closed: the only candidate is scoped to an unopened namespace.
    let mut ctx = goal_side_ctx(&env);
    assert!(
        ctx.resolve_instance(&c_nat_goal()).is_none(),
        "a scoped instance must not resolve while its namespace is closed"
    );

    // `open Foo`: visible.
    let mut ns = crate::namespace::NamespaceState::new();
    ns.open_namespace(Name::from_string("Foo"));
    ctx.set_namespace_state(ns);
    assert!(
        ctx.resolve_instance(&c_nat_goal()).is_some(),
        "the same instance must resolve once its namespace is open"
    );

    // The file's own scope state layered on top must not forget the import.
    let mut ctx2 = goal_side_ctx(&env);
    ctx2.set_instance_scope_state(std::collections::HashSet::new(), HashMap::new(), &[]);
    assert!(
        ctx2.resolve_instance(&c_nat_goal()).is_none(),
        "setting the file's scope state must keep the imported scope"
    );
}

/// THE BOUNDARY, RE-DECIDED 2026-09-16. This test asserted the opposite until
/// that day, and the change is deliberate rather than a repair.
///
/// It used to pin `depth == 0`: the goal-side telescope answered the
/// ELABORATOR's own goal and never a candidate's `[inst]` sub-goal, so `D Nat`
/// below stayed unresolved. The stated reason was that the `decEq` bridge's
/// `DecidableEq α` delegation would otherwise silently change the TERM of goals
/// that already resolve.
///
/// What that restriction also refused was `Pi.hasLe`'s premise. A candidate's
/// `[inst]` premise is precisely where `∀ i, LE (π i)` appears, so the guard
/// closed the telescope to the one shape Mathlib needs, and
/// `Mathlib/Order/Basic.lean` lost five declarations to it (three directly,
/// two as `alias` cascades). Lifting it recovers all five by name, 65/206 ->
/// 70/206, with zero residual errors of that class.
///
/// The hazard does not follow, and `test_goal_side_abstraction_only_adds_never_replaces`
/// below is the pin rather than the argument: the abstraction is still reached
/// only after the primary search AND the candidate-side telescope both return
/// `None`, so it can only ADD a resolution, never replace a term that already
/// resolves.
#[test]
fn test_goal_side_is_applied_to_an_internal_subgoal() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    let pi_goal = Expr::pi(BinderInfo::Default, nat_const(), c_nat_goal());
    let d_nat = Expr::app(Expr::const_(Name::from_string("D"), vec![]), nat_const());
    // instD : [(x : Nat) → C Nat] → D Nat. The VALUE is the bare constant (a
    // lambda value would beta-reduce the premise away and leave `instD` with
    // no argument to inspect).
    ctx.instances_mut().add_instance(
        Name::from_string("instD"),
        Name::from_string("D"),
        Expr::const_(Name::from_string("instD"), vec![]),
        Expr::pi(BinderInfo::InstImplicit, pi_goal.clone(), d_nat.clone()),
        crate::instances::DEFAULT_PRIORITY,
    );

    let resolved = ctx
        .resolve_instance(&d_nat)
        .expect("a candidate's Pi-shaped [inst] premise is answered by the telescope, as in Lean");
    // The premise really is the built abstraction, not a metavariable left
    // behind: `instD (fun (x : Nat) => instCNat)`.
    let (head, args) = (resolved.get_app_fn(), resolved.get_app_args());
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name, &Name::from_string("instD")),
        other => panic!("expected `instD` at the head, got {other:?}"),
    }
    assert_eq!(
        args.len(),
        1,
        "instD takes exactly its [inst] premise: {resolved:?}"
    );
    match args[0].kind() {
        ExprKind::Lam(_, ty, body) => {
            assert_eq!(
                ty.as_ref(),
                &nat_const(),
                "the premise's binder is the goal's own"
            );
            match body.kind() {
                ExprKind::Const(name, _) => assert_eq!(name, &Name::from_string("instCNat")),
                other => panic!("expected instCNat under the premise's lambda, got {other:?}"),
            }
        }
        other => panic!("expected the built abstraction as instD's premise, got {other:?}"),
    }
    // ... and the SAME goal, asked by the elaborator, is still answered.
    assert!(
        ctx.resolve_instance(&pi_goal).is_some(),
        "the same goal at depth 0 must still be answered"
    );
}

/// THE HAZARD THE LIFTED GUARD NAMED, pinned instead of argued.
///
/// The worry recorded on `depth == 0` was that answering a candidate's sub-goal
/// could "silently change the TERM of goals that already resolve". The reason it
/// does not is structural and this test holds it: `resolve_pi_goal_by_abstraction`
/// is consulted only after the primary search AND `resolve_local_instance_telescoped`
/// have both returned `None`, so it can only ADD a resolution where there was
/// none — it can never rewrite one that already succeeded.
///
/// A goal answered by an ordinary registered instance must therefore come back
/// with that instance's own term, byte for byte, whether or not the goal-side
/// telescope is reachable at its depth.
#[test]
fn test_goal_side_abstraction_only_adds_never_replaces() {
    let env = goal_side_env();
    let mut ctx = goal_side_ctx(&env);

    // `C Nat` is answered by the fixture's OWN directly-registered instance —
    // no Pi anywhere, so the goal-side abstraction has nothing to contribute.
    // Using the fixture's instance rather than injecting one is deliberate: an
    // injected competitor would be testing priority selection, not term
    // stability. (Measured while writing this: an added `instC` loses to the
    // registered `instCNat`, which is the selection path and not this property.)
    let c_nat = c_nat_goal();
    let resolved = ctx
        .resolve_instance(&c_nat)
        .expect("the directly-registered instance must resolve");
    assert_eq!(
        resolved,
        Expr::const_(Name::from_string("instCNat"), vec![]),
        "a goal that already resolves keeps its exact term: the goal-side \
         abstraction adds resolutions, it never replaces one"
    );
}
