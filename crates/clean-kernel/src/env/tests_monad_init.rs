// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — IO/monad initialization functions.
//!
//! Covers 5 functions in `env/data.rs` with ZERO previous test coverage:
//! - `init_io` (line 2435): IO monad type + pure + bind
//! - `init_state_t` (line 2523): StateT monad transformer
//! - `init_state_m` (line 2614): StateM type alias
//! - `init_id` (line 2692): Id identity monad
//! - `init_monad_classes` (line 2780): Pure.pure + Bind.bind type classes
//!
//! These are the type definitions needed for `do`-notation support and
//! effectful programs. If any produce incorrect types, do-notation
//! elaboration would silently fail or produce wrong results.

use super::*;
use crate::tc::TypeChecker;

// =============================================================================
// init_io: IO monad (IO, IO.pure, IO.bind)
// =============================================================================

#[test]
fn test_init_io_creates_io_constant() {
    let mut env = Environment::new();
    env.init_io().expect("init_io should succeed");

    // IO should be defined
    let io_decl = env.get_const(&Name::from_string("IO"));
    assert!(io_decl.is_some(), "IO should be defined after init_io");
}

#[test]
fn test_init_io_creates_pure_and_bind() {
    let mut env = Environment::new();
    env.init_io().expect("init_io should succeed");

    // IO.pure should be defined
    let pure_decl = env.get_const(&Name::from_string("IO.pure"));
    assert!(
        pure_decl.is_some(),
        "IO.pure should be defined after init_io"
    );

    // IO.bind should be defined
    let bind_decl = env.get_const(&Name::from_string("IO.bind"));
    assert!(
        bind_decl.is_some(),
        "IO.bind should be defined after init_io"
    );
}

#[test]
fn test_init_io_type_checks() {
    let mut env = Environment::new();
    env.init_io().expect("init_io should succeed");

    let tc = TypeChecker::new(&env);

    // IO constant should be well-typed: IO : Type → Type
    let io_const = Expr::const_(Name::from_string("IO"), vec![]);
    let io_ty = tc.infer_type(&io_const).expect("IO should be well-typed");

    // IO : Type → Type means it's a Pi type
    assert!(
        matches!(&io_ty.kind, ExprKind::Pi(..)),
        "IO should have Pi type (Type → Type), got {:?}",
        io_ty.kind
    );
}

#[test]
fn test_init_io_idempotent() {
    let mut env = Environment::new();
    env.init_io().expect("first init_io");
    env.init_io().expect("second init_io should be idempotent");
}

// =============================================================================
// init_state_t: StateT monad transformer
// =============================================================================

#[test]
fn test_init_state_t_creates_constants() {
    let mut env = Environment::new();
    env.init_state_t().expect("init_state_t should succeed");

    assert!(
        env.get_const(&Name::from_string("StateT")).is_some(),
        "StateT should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.pure")).is_some(),
        "StateT.pure should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.set")).is_some(),
        "StateT.set should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.get")).is_some(),
        "StateT.get should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.modify")).is_some(),
        "StateT.modify should be defined (#3418)"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.modifyGet"))
            .is_some(),
        "StateT.modifyGet should be defined (#3418)"
    );
    assert!(
        env.get_const(&Name::from_string("StateT.run")).is_some(),
        "StateT.run should be defined"
    );
}

#[test]
fn test_init_state_t_type_checks() {
    let mut env = Environment::new();
    env.init_state_t().expect("init_state_t should succeed");

    let tc = TypeChecker::new(&env);

    let state_t_const = Expr::const_(
        Name::from_string("StateT"),
        vec![Level::zero(), Level::zero()],
    );
    let state_t_ty = tc
        .infer_type(&state_t_const)
        .expect("StateT should be well-typed");

    // StateT.{u,v} : Type (u+1) → (Type (u+1) → Type (v+1)) → Type (u+1) → Type (v+1)
    // which is a Pi type
    assert!(
        matches!(&state_t_ty.kind, ExprKind::Pi(..)),
        "StateT should have Pi type, got {:?}",
        state_t_ty.kind
    );
}

#[test]
fn test_init_state_t_idempotent() {
    let mut env = Environment::new();
    env.init_state_t().expect("first");
    env.init_state_t().expect("second should be idempotent");
}

// =============================================================================
// init_state_m: StateM type alias
// =============================================================================

#[test]
fn test_init_state_m_creates_constants() {
    let mut env = Environment::new();
    env.init_state_m().expect("init_state_m should succeed");

    assert!(
        env.get_const(&Name::from_string("StateM")).is_some(),
        "StateM should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("StateM.pure")).is_some(),
        "StateM.pure should be defined"
    );
}

#[test]
fn test_init_state_m_type_checks() {
    let mut env = Environment::new();
    env.init_state_m().expect("init_state_m should succeed");

    let tc = TypeChecker::new(&env);

    let state_m_const = Expr::const_(Name::from_string("StateM"), vec![Level::zero()]);
    let state_m_ty = tc
        .infer_type(&state_m_const)
        .expect("StateM should be well-typed");

    // StateM.{u} : Type (u+1) → Type (u+1) → Type (u+1)
    assert!(
        matches!(&state_m_ty.kind, ExprKind::Pi(..)),
        "StateM should have Pi type, got {:?}",
        state_m_ty.kind
    );
}

#[test]
fn test_init_state_m_idempotent() {
    let mut env = Environment::new();
    env.init_state_m().expect("first");
    env.init_state_m().expect("second should be idempotent");
}

// =============================================================================
// init_id: Id identity monad
// =============================================================================

#[test]
fn test_init_id_creates_constants() {
    let mut env = Environment::new();
    env.init_id().expect("init_id should succeed");

    assert!(
        env.get_const(&Name::from_string("Id")).is_some(),
        "Id should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("Id.mk")).is_some(),
        "Id.mk should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("Id.run")).is_some(),
        "Id.run should be defined"
    );
}

#[test]
fn test_init_id_type_checks() {
    let mut env = Environment::new();
    env.init_id().expect("init_id should succeed");

    let tc = TypeChecker::new(&env);

    // Id : Type u → Type u
    let id_const = Expr::const_(Name::from_string("Id"), vec![Level::zero()]);
    let id_ty = tc.infer_type(&id_const).expect("Id should be well-typed");
    assert!(
        matches!(&id_ty.kind, ExprKind::Pi(..)),
        "Id should have Pi type (Type u → Type u), got {:?}",
        id_ty.kind
    );
}

#[test]
fn test_init_id_idempotent() {
    let mut env = Environment::new();
    env.init_id().expect("first");
    env.init_id().expect("second should be idempotent");
}

// =============================================================================
// init_monad_classes: Pure.pure + Bind.bind
// =============================================================================

#[test]
fn test_init_monad_classes_creates_constants() {
    let mut env = Environment::new();
    env.init_monad_classes()
        .expect("init_monad_classes should succeed");

    assert!(
        env.get_const(&Name::from_string("Pure.pure")).is_some(),
        "Pure.pure should be defined"
    );
    assert!(
        env.get_const(&Name::from_string("Bind.bind")).is_some(),
        "Bind.bind should be defined"
    );
}

#[test]
fn test_init_monad_classes_type_checks() {
    let mut env = Environment::new();
    env.init_monad_classes()
        .expect("init_monad_classes should succeed");

    let tc = TypeChecker::new(&env);

    // Pure.pure should be well-typed
    let pure_const = Expr::const_(
        Name::from_string("Pure.pure"),
        vec![Level::zero(), Level::zero()],
    );
    let pure_ty = tc
        .infer_type(&pure_const)
        .expect("Pure.pure should be well-typed");
    assert!(
        matches!(&pure_ty.kind, ExprKind::Pi(..)),
        "Pure.pure should have Pi type, got {:?}",
        pure_ty.kind
    );

    // Bind.bind should be well-typed
    let bind_const = Expr::const_(
        Name::from_string("Bind.bind"),
        vec![Level::zero(), Level::zero()],
    );
    let bind_ty = tc
        .infer_type(&bind_const)
        .expect("Bind.bind should be well-typed");
    assert!(
        matches!(&bind_ty.kind, ExprKind::Pi(..)),
        "Bind.bind should have Pi type, got {:?}",
        bind_ty.kind
    );
}

#[test]
fn test_init_monad_classes_idempotent() {
    let mut env = Environment::new();
    env.init_monad_classes().expect("first");
    env.init_monad_classes()
        .expect("second should be idempotent");
}

// =============================================================================
// Integration: full monad stack for do-notation
// =============================================================================

#[test]
fn test_full_monad_stack_for_do_notation() {
    let mut env = Environment::new();

    // Initialize the full stack needed for do-notation
    env.init_io().expect("init_io");
    env.init_id().expect("init_id");
    env.init_state_t().expect("init_state_t");
    env.init_state_m().expect("init_state_m");
    env.init_monad_classes().expect("init_monad_classes");

    // All constants should coexist without conflicts
    let tc = TypeChecker::new(&env);

    // Verify all 11 constants are well-typed simultaneously
    let constants = [
        ("IO", vec![]),
        ("IO.pure", vec![]),
        ("IO.bind", vec![]),
        ("Id", vec![Level::zero()]),
        ("Id.mk", vec![Level::zero()]),
        ("Id.run", vec![Level::zero()]),
        ("StateT", vec![Level::zero(), Level::zero()]),
        ("StateT.pure", vec![Level::zero(), Level::zero()]),
        ("StateM", vec![Level::zero()]),
        ("StateM.pure", vec![Level::zero()]),
        ("Pure.pure", vec![Level::zero(), Level::zero()]),
    ];

    for (name, levels) in &constants {
        let c = Expr::const_(Name::from_string(name), levels.clone());
        let _ = tc
            .infer_type(&c)
            .unwrap_or_else(|e| panic!("{name} should be well-typed, got error: {e:?}"));
    }
}
