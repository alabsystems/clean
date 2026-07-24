// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for BCP loop refinement formalization.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_bcp_loop_refinement()
        .expect("init_bcp_loop_refinement");
    env
}

#[test]
fn test_all_types_registered() {
    let env = make_env();
    for name in [
        "BCPLoop.Literal",
        "BCPLoop.Literal.index",
        "BCPLoop.WatchEntry",
        "BCPLoop.WatchEntry.blocker",
        "BCPLoop.WatchEntry.clause_idx",
        "BCPLoop.WatchEntry.lit0",
        "BCPLoop.WatchEntry.lit1",
        "BCPLoop.WatchList",
        "BCPLoop.ImperativeState",
        "BCPLoop.ImperativeState.watches",
        "BCPLoop.ImperativeState.assignment",
        "BCPLoop.ImperativeState.trail",
        "BCPLoop.ImperativeState.i_ptr",
        "BCPLoop.ImperativeState.j_ptr",
        "BCPLoop.AbstractBCPState",
        "BCPLoop.BCPResult",
        "BCPLoop.BCPResult.ok",
        "BCPLoop.BCPResult.conflict",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_operations_registered() {
    let env = make_env();
    for name in [
        "BCPLoop.propagate_abstract",
        "BCPLoop.propagate_imperative",
        "BCPLoop.xor_other_watched",
        "BCPLoop.blocker_check",
        "BCPLoop.is_binary_clause",
        "BCPLoop.compaction_step",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "BCPLoop.two_pointer_compaction_invariant",
        "BCPLoop.xor_identity",
        "BCPLoop.watch_consistency_preserved",
        "BCPLoop.bcp_refinement",
        "BCPLoop.blocker_soundness",
        "BCPLoop.binary_clause_propagation",
        "BCPLoop.replacement_search_complete",
        "BCPLoop.compaction_preserves_watches",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "BCPLoop.two_pointer_compaction_invariant_helper",
        "BCPLoop.xor_identity_helper",
        "BCPLoop.watch_consistency_preserved_helper",
        "BCPLoop.bcp_refinement_helper",
        "BCPLoop.blocker_soundness_helper",
        "BCPLoop.binary_clause_propagation_helper",
        "BCPLoop.replacement_search_complete_helper",
        "BCPLoop.compaction_preserves_watches_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_bcp_result_type_checks() {
    let env = make_env();
    let result = crate::expr::Expr::const_(Name::from_string("BCPLoop.BCPResult"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&result)
        .expect("infer BCPLoop.BCPResult type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_propagate_imperative_type_checks() {
    let env = make_env();
    let op = crate::expr::Expr::const_(Name::from_string("BCPLoop.propagate_imperative"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&op)
        .expect("infer BCPLoop.propagate_imperative type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_blocker_check_type_checks() {
    let env = make_env();
    let op = crate::expr::Expr::const_(Name::from_string("BCPLoop.blocker_check"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&op)
        .expect("infer BCPLoop.blocker_check type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_bcp_refinement_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(Name::from_string("BCPLoop.bcp_refinement"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer BCPLoop.bcp_refinement type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent_init() {
    let mut env = Environment::new();
    env.init_bcp_loop_refinement()
        .expect("first init_bcp_loop_refinement");
    env.init_bcp_loop_refinement()
        .expect("second init_bcp_loop_refinement should be idempotent");
}
