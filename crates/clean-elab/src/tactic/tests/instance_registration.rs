// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for instance tactic registration semantics (#2072).
//!
//! Verifies that letI, haveI, and inferI register resolved instances
//! in the ProofState's InstanceTable for subsequent typeclass resolution.

use super::*;
use crate::instances::InstanceTable;
use crate::tactic::instance::{have_i, infer_i, let_i};

/// Build a ProofState with an instance table containing a registered class.
///
/// Declares the class name as an axiom in the kernel environment so that
/// `close_goal_checked` (which invokes the type checker) can resolve the
/// constant. Without this, proofs referencing the class fail with
/// `UnknownConst`.
fn state_with_class(class: &str) -> ProofState {
    let mut env = setup_env();
    // Declare the class as a Prop-valued axiom so the type checker accepts it.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(class),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("classical_dec"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string(class), vec![]),
    })
    .unwrap();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut instances = InstanceTable::new();
    instances.register_class(Name::from_string(class), 0, vec![]);
    ProofState::with_instances(env, target, instances)
}

#[test]
fn test_let_i_registers_instance_in_table() {
    let mut state = state_with_class("Decidable");

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    let value = Expr::const_(Name::from_string("classical_dec"), vec![]);
    let_i(&mut state, "inst", ty, value).unwrap();

    // The instance should be registered in the table
    let instances = state.instances().expect("should have instance table");
    let registered = instances.get_instances(&Name::from_string("Decidable"));
    assert!(
        !registered.is_empty(),
        "letI should register instance in table"
    );
}

#[test]
fn test_have_i_registers_instance_in_table() {
    let mut state = state_with_class("Decidable");

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    have_i(&mut state, "inst", ty).unwrap();

    // The instance should be registered in the table
    let instances = state.instances().expect("should have instance table");
    let registered = instances.get_instances(&Name::from_string("Decidable"));
    assert!(
        !registered.is_empty(),
        "haveI should register instance in table"
    );
}

#[test]
fn test_have_i_creates_subgoal() {
    let mut state = state_with_class("Decidable");
    let original_goal_count = state.goals.len();

    let ty = Expr::const_(Name::from_string("Decidable"), vec![]);
    have_i(&mut state, "inst", ty).unwrap();

    // have_i should create a subgoal for proving the instance type
    assert_eq!(
        state.goals.len(),
        original_goal_count + 1,
        "haveI should add a subgoal for the instance proof"
    );
}

#[test]
fn test_infer_i_registers_resolved_instance() {
    let mut env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);

    let mut instances = InstanceTable::new();
    let dec_class = Name::from_string("Decidable");
    instances.register_class(dec_class.clone(), 0, vec![]);
    let inst_expr = Expr::const_(Name::from_string("instDecidable"), vec![]);
    let dec_ty = Expr::const_(dec_class.clone(), vec![]);
    env.add_decl(Declaration::Axiom {
        name: dec_class.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("instDecidable"),
        level_params: vec![],
        type_: dec_ty.clone(),
    })
    .unwrap();
    instances.add_instance(
        Name::from_string("instDecidable"),
        dec_class.clone(),
        inst_expr,
        dec_ty.clone(),
        100,
    );

    let mut state = ProofState::with_instances(env, target, instances);

    infer_i(&mut state, "inst", dec_ty).unwrap();

    // After inferI, the resolved instance should also be registered as a local instance
    let instances = state.instances().expect("should have instance table");
    let registered = instances.get_instances(&dec_class);
    // Should have at least 2: the original + the local one registered by infer_i
    assert!(
        registered.len() >= 2,
        "inferI should register resolved instance as local instance, got {} instances",
        registered.len()
    );
}

#[test]
fn test_let_i_without_instance_table_still_adds_to_context() {
    // When there's no instance table, letI should still add to local context
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let value = Expr::const_(Name::from_string("a"), vec![]);
    let_i(&mut state, "inst", ty, value).unwrap();

    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx.iter().any(|d| d.name == "inst"),
        "letI should add to local context even without instance table"
    );
}
