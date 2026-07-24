// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof state serialization (`state_ser`).

use super::state_ser::{
    serialize_expr, serialize_goal, serialize_local_decl, serialize_proof_state, SerError,
    SerializedExpr, SerializedGoal, SerializedLocalDecl, SerializedProofState, TacticStep,
};
use super::{LocalDecl, ProofState};
use clean_kernel::{BinderInfo, Environment, Expr, FVarId};

/// Helper: create a minimal environment for test proof states.
fn test_env() -> Environment {
    Environment::new()
}

/// Helper: create a `Prop` sort expression.
fn prop() -> Expr {
    Expr::prop()
}

/// Helper: create a named constant expression (no universe levels).
fn const_expr(name: &str) -> Expr {
    Expr::const_str(name)
}

// =============================================================================
// Serialize empty proof state
// =============================================================================

#[test]
fn test_serialize_empty_proof_state() {
    let state = ProofState::new(test_env(), prop());
    let serialized = serialize_proof_state(&state);

    assert_eq!(serialized.version, 1);
    assert_eq!(serialized.goals.len(), 1);
    assert!(serialized.tactic_history.is_empty());
    // The main goal metavar should not yet have an assignment.
    assert!(serialized.meta_assignments.is_empty());
}

// =============================================================================
// Serialize single goal
// =============================================================================

#[test]
fn test_serialize_single_goal() {
    let state = ProofState::new(test_env(), prop());
    let goal = state.current_goal().expect("should have a goal");
    let sg = serialize_goal(goal);

    assert!(sg.id.starts_with("?m"));
    assert!(!sg.is_closed);
    assert!(sg.local_context.is_empty());
    // Target should be a Sort(Prop).
    match &sg.target_type {
        SerializedExpr::Sort(s) => assert!(!s.is_empty()),
        other => panic!("expected Sort, got {other:?}"),
    }
}

// =============================================================================
// Serialize local context
// =============================================================================

#[test]
fn test_serialize_local_context() {
    let decl = LocalDecl {
        fvar: FVarId::new(42),
        name: "h".to_owned(),
        ty: prop(),
        value: None,
    };
    let sd = serialize_local_decl(&decl);

    assert_eq!(sd.name, "h");
    assert_eq!(sd.binder_info, "default");
    assert!(sd.value.is_none());
    match &sd.ty {
        SerializedExpr::Sort(_) => {}
        other => panic!("expected Sort for ty, got {other:?}"),
    }
}

// =============================================================================
// Serialize various expr types
// =============================================================================

#[test]
fn test_serialize_expr_bvar() {
    let expr = Expr::bvar(3);
    let se = serialize_expr(&expr);
    assert_eq!(se, SerializedExpr::Var(3));
}

#[test]
fn test_serialize_expr_sort() {
    let se = serialize_expr(&prop());
    match &se {
        SerializedExpr::Sort(s) => assert!(!s.is_empty()),
        other => panic!("expected Sort, got {other:?}"),
    }
}

#[test]
fn test_serialize_expr_const() {
    let expr = const_expr("Nat.zero");
    let se = serialize_expr(&expr);
    match &se {
        SerializedExpr::Const(name, levels) => {
            assert_eq!(name, "Nat.zero");
            assert!(levels.is_empty());
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_serialize_expr_app() {
    let f = const_expr("Nat.succ");
    let a = const_expr("Nat.zero");
    let expr = Expr::app(f, a);
    let se = serialize_expr(&expr);
    match &se {
        SerializedExpr::App(func, arg) => {
            assert_eq!(**func, SerializedExpr::Const("Nat.succ".to_owned(), vec![]));
            assert_eq!(**arg, SerializedExpr::Const("Nat.zero".to_owned(), vec![]));
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_serialize_expr_lambda() {
    let ty = prop();
    let body = Expr::bvar(0);
    let expr = Expr::lam(BinderInfo::Default, ty, body);
    let se = serialize_expr(&expr);
    match &se {
        SerializedExpr::Lambda(bi, _, _) => {
            assert_eq!(bi, "default");
        }
        other => panic!("expected Lambda, got {other:?}"),
    }
}

#[test]
fn test_serialize_expr_pi() {
    let ty = prop();
    let body = prop();
    let expr = Expr::pi(BinderInfo::Default, ty, body);
    let se = serialize_expr(&expr);
    match &se {
        SerializedExpr::Pi(bi, _, _) => {
            assert_eq!(bi, "default");
        }
        other => panic!("expected Pi, got {other:?}"),
    }
}

#[test]
fn test_serialize_expr_fvar() {
    let expr = Expr::fvar(FVarId::new(99));
    let se = serialize_expr(&expr);
    assert_eq!(se, SerializedExpr::FVar("fvar_99".to_owned()));
}

// =============================================================================
// JSON round-trip
// =============================================================================

#[test]
fn test_json_round_trip() {
    let state = ProofState::new(test_env(), prop());
    let serialized = serialize_proof_state(&state);

    let json = serialized.to_json().expect("to_json should succeed");
    let deserialized = SerializedProofState::from_json(&json).expect("from_json should succeed");

    assert_eq!(serialized, deserialized);
}

#[test]
fn test_json_round_trip_with_context() {
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(0),
            name: "x".to_owned(),
            ty: const_expr("Nat"),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(1),
            name: "h".to_owned(),
            ty: prop(),
            value: None,
        },
    ];
    let state = ProofState::with_context(test_env(), prop(), ctx);
    let serialized = serialize_proof_state(&state);

    let json = serialized.to_json().expect("to_json should succeed");
    let deserialized = SerializedProofState::from_json(&json).expect("from_json should succeed");

    assert_eq!(serialized, deserialized);
    assert_eq!(deserialized.goals[0].local_context.len(), 2);
    assert_eq!(deserialized.goals[0].local_context[0].name, "x");
    assert_eq!(deserialized.goals[0].local_context[1].name, "h");
}

// =============================================================================
// Pretty print expressions
// =============================================================================

#[test]
fn test_pretty_print_var() {
    let se = SerializedExpr::Var(0);
    assert_eq!(se.pretty_print(), "#0");
}

#[test]
fn test_pretty_print_sort() {
    let se = SerializedExpr::Sort("Prop".to_owned());
    assert_eq!(se.pretty_print(), "Prop");
}

#[test]
fn test_pretty_print_const_no_levels() {
    let se = SerializedExpr::Const("Nat".to_owned(), vec![]);
    assert_eq!(se.pretty_print(), "Nat");
}

#[test]
fn test_pretty_print_const_with_levels() {
    let se = SerializedExpr::Const("List".to_owned(), vec!["u".to_owned()]);
    assert_eq!(se.pretty_print(), "List.{u}");
}

#[test]
fn test_pretty_print_app() {
    let se = SerializedExpr::App(
        Box::new(SerializedExpr::Const("f".to_owned(), vec![])),
        Box::new(SerializedExpr::Const("x".to_owned(), vec![])),
    );
    assert_eq!(se.pretty_print(), "(f x)");
}

#[test]
fn test_pretty_print_lambda() {
    let se = SerializedExpr::Lambda(
        "default".to_owned(),
        Box::new(SerializedExpr::Sort("Prop".to_owned())),
        Box::new(SerializedExpr::Var(0)),
    );
    assert_eq!(se.pretty_print(), "fun (default : Prop) => #0");
}

#[test]
fn test_pretty_print_pi() {
    let se = SerializedExpr::Pi(
        "implicit".to_owned(),
        Box::new(SerializedExpr::Sort("Type".to_owned())),
        Box::new(SerializedExpr::Var(0)),
    );
    assert_eq!(se.pretty_print(), "(implicit : Type) -> #0");
}

// =============================================================================
// Tactic step recording
// =============================================================================

#[test]
fn test_tactic_step_new() {
    let step = TacticStep::new("intro");
    assert_eq!(step.tactic_name, "intro");
    assert!(step.args.is_empty());
    assert_eq!(step.goals_before, 0);
    assert_eq!(step.goals_after, 0);
    assert!(!step.success);
}

#[test]
fn test_tactic_step_serialize() {
    let mut step = TacticStep::new("apply");
    step.args = vec!["Nat.succ".to_owned()];
    step.goals_before = 1;
    step.goals_after = 1;
    step.success = true;

    let json = serde_json::to_string(&step).expect("should serialize");
    let deser: TacticStep = serde_json::from_str(&json).expect("should deserialize");
    assert_eq!(step, deser);
}

// =============================================================================
// Version field
// =============================================================================

#[test]
fn test_version_field() {
    let state = ProofState::new(test_env(), prop());
    let serialized = serialize_proof_state(&state);
    assert_eq!(serialized.version, 1);
}

#[test]
fn test_version_mismatch() {
    let state_ser = SerializedProofState {
        goals: vec![],
        meta_assignments: vec![],
        tactic_history: vec![],
        version: 999,
    };
    let json = serde_json::to_string(&state_ser).expect("should serialize");
    let result = SerializedProofState::from_json(&json);
    match result {
        Err(SerError::VersionMismatch { expected, got }) => {
            assert_eq!(expected, 1);
            assert_eq!(got, 999);
        }
        other => panic!("expected VersionMismatch, got {other:?}"),
    }
}

// =============================================================================
// Goal count and is_solved
// =============================================================================

#[test]
fn test_goal_count() {
    let state = ProofState::new(test_env(), prop());
    let serialized = serialize_proof_state(&state);
    assert_eq!(serialized.goal_count(), 1);
}

#[test]
fn test_is_solved_empty() {
    let ser = SerializedProofState {
        goals: vec![],
        meta_assignments: vec![],
        tactic_history: vec![],
        version: 1,
    };
    assert!(ser.is_solved());
}

#[test]
fn test_is_solved_open_goal() {
    let ser = SerializedProofState {
        goals: vec![SerializedGoal {
            id: "?m0".to_owned(),
            target_type: SerializedExpr::Sort("Prop".to_owned()),
            local_context: vec![],
            is_closed: false,
        }],
        meta_assignments: vec![],
        tactic_history: vec![],
        version: 1,
    };
    assert!(!ser.is_solved());
}

#[test]
fn test_is_solved_all_closed() {
    let ser = SerializedProofState {
        goals: vec![SerializedGoal {
            id: "?m0".to_owned(),
            target_type: SerializedExpr::Sort("Prop".to_owned()),
            local_context: vec![],
            is_closed: true,
        }],
        meta_assignments: vec![],
        tactic_history: vec![],
        version: 1,
    };
    assert!(ser.is_solved());
}

// =============================================================================
// Serialize let-binding locals
// =============================================================================

#[test]
fn test_serialize_let_binding_local() {
    let decl = LocalDecl {
        fvar: FVarId::new(10),
        name: "x".to_owned(),
        ty: const_expr("Nat"),
        value: Some(const_expr("Nat.zero")),
    };
    let sd = serialize_local_decl(&decl);

    assert_eq!(sd.name, "x");
    assert!(sd.value.is_some());
    match sd.value.as_ref() {
        Some(SerializedExpr::Const(name, _)) => assert_eq!(name, "Nat.zero"),
        other => panic!("expected Const for let value, got {other:?}"),
    }
}

// =============================================================================
// Multiple goals
// =============================================================================

#[test]
fn test_multiple_goals() {
    let state = ProofState::new(test_env(), prop());
    let serialized = serialize_proof_state(&state);
    assert_eq!(serialized.goal_count(), 1);

    // Construct a serialized state with multiple goals manually.
    let ser = SerializedProofState {
        goals: vec![
            SerializedGoal {
                id: "?m0".to_owned(),
                target_type: SerializedExpr::Sort("Prop".to_owned()),
                local_context: vec![],
                is_closed: false,
            },
            SerializedGoal {
                id: "?m1".to_owned(),
                target_type: SerializedExpr::Const("Nat".to_owned(), vec![]),
                local_context: vec![SerializedLocalDecl {
                    name: "n".to_owned(),
                    ty: SerializedExpr::Const("Nat".to_owned(), vec![]),
                    value: None,
                    binder_info: "default".to_owned(),
                }],
                is_closed: false,
            },
        ],
        meta_assignments: vec![],
        tactic_history: vec![],
        version: 1,
    };
    assert_eq!(ser.goal_count(), 2);
    assert!(!ser.is_solved());
}

// =============================================================================
// Meta assignments
// =============================================================================

#[test]
fn test_meta_assignments_serialization() {
    let ser = SerializedProofState {
        goals: vec![],
        meta_assignments: vec![
            (
                "?m0".to_owned(),
                SerializedExpr::Const("True.intro".to_owned(), vec![]),
            ),
            ("?m1".to_owned(), SerializedExpr::Var(0)),
        ],
        tactic_history: vec![],
        version: 1,
    };

    let json = ser.to_json().expect("to_json should succeed");
    let deser = SerializedProofState::from_json(&json).expect("from_json should succeed");
    assert_eq!(ser, deser);
    assert_eq!(deser.meta_assignments.len(), 2);
    assert!(deser.is_solved()); // no open goals
}

// =============================================================================
// Pretty print: FVar, Meta, Other, Lit
// =============================================================================

#[test]
fn test_pretty_print_fvar() {
    let se = SerializedExpr::FVar("fvar_42".to_owned());
    assert_eq!(se.pretty_print(), "fvar_42");
}

#[test]
fn test_pretty_print_meta() {
    let se = SerializedExpr::Meta("?m0".to_owned());
    assert_eq!(se.pretty_print(), "?m0");
}

#[test]
fn test_pretty_print_other() {
    let se = SerializedExpr::Other("let x : ... := ... in ...".to_owned());
    assert_eq!(se.pretty_print(), "let x : ... := ... in ...");
}

#[test]
fn test_pretty_print_lit() {
    let se = SerializedExpr::Lit("Nat(42)".to_owned());
    assert_eq!(se.pretty_print(), "Nat(42)");
}
