// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for match expression compilation and evaluation.
//!
//! Part of #3084 - Match expression compilation for native execution.

use super::*;
use crate::match_eval::{eval_decision_tree, MatchEnv, MatchValue};
use crate::native_types::NativeType;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_var(name: &str) -> Var {
    Var {
        name: Name::from_string(name),
        type_: NativeType::UInt64,
    }
}

fn mk_ctor_tag(name: &str, arity: usize) -> ConstructorTag {
    ConstructorTag {
        name: Name::from_string(name),
        arity,
    }
}

fn mk_ctor_pat(name: &str, sub: Vec<Pattern>) -> Pattern {
    Pattern::Constructor(Name::from_string(name), sub)
}

fn mk_var_pat(name: &str) -> Pattern {
    Pattern::Variable(Name::from_string(name))
}

fn mk_arm(patterns: Vec<Pattern>, body_idx: usize) -> MatchArm {
    MatchArm {
        patterns,
        guard: None,
        body_idx,
    }
}

fn mk_ctor_val(name: &str, fields: Vec<MatchValue>) -> MatchValue {
    MatchValue::Constructor(mk_ctor_tag(name, fields.len()), fields)
}

// ---------------------------------------------------------------------------
// Compilation tests
// ---------------------------------------------------------------------------

#[test]
fn test_compile_match_single_wildcard_arm() {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![mk_arm(vec![Pattern::Wildcard], 0)];
    let tree = compile_match(&scrutinees, &arms);
    assert_eq!(tree, DecisionTree::Leaf(0));
}

#[test]
fn test_compile_match_single_variable_arm() {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![mk_arm(vec![mk_var_pat("y")], 0)];
    let tree = compile_match(&scrutinees, &arms);
    assert_eq!(tree, DecisionTree::Leaf(0));
}

#[test]
fn test_compile_match_empty_arms_produces_sentinel() {
    let scrutinees = vec![mk_var("x")];
    let arms: Vec<MatchArm> = vec![];
    let tree = compile_match(&scrutinees, &arms);
    assert_eq!(tree, DecisionTree::Leaf(usize::MAX));
}

#[test]
fn test_compile_match_single_constructor() {
    // match x with
    // | None => 0
    // | Some _ => 1
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // Should produce a Switch on x
    match &tree {
        DecisionTree::Switch(var, branches, default) => {
            assert_eq!(var.name, Name::from_string("x"));
            assert_eq!(branches.len(), 2);
            assert_eq!(branches[0].0.name, Name::from_string("None"));
            assert_eq!(branches[1].0.name, Name::from_string("Some"));
            assert!(default.is_none());
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_compile_match_constructor_with_default() {
    // match x with
    // | None => 0
    // | _ => 1
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);

    match &tree {
        DecisionTree::Switch(_, branches, default) => {
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, Name::from_string("None"));
            assert!(default.is_some());
            assert_eq!(**default.as_ref().unwrap(), DecisionTree::Leaf(1));
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_compile_match_nested_constructors() {
    // match x with
    // | Some(Some(_)) => 0
    // | Some(None) => 1
    // | None => 2
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(
            vec![mk_ctor_pat(
                "Some",
                vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])],
            )],
            0,
        ),
        mk_arm(
            vec![mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])])],
            1,
        ),
        mk_arm(vec![mk_ctor_pat("None", vec![])], 2),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // Top-level should be a Switch on x with None and Some branches
    match &tree {
        DecisionTree::Switch(var, branches, _) => {
            assert_eq!(var.name, Name::from_string("x"));
            assert_eq!(branches.len(), 2);
            // Some branch should have a nested switch on the field
            match &branches[0].1 {
                DecisionTree::Switch(_, inner_branches, _) => {
                    assert!(!inner_branches.is_empty());
                }
                DecisionTree::Leaf(_) => {
                    // Also acceptable if first-arm matching simplified
                }
                other => panic!("expected Switch or Leaf, got {other:?}"),
            }
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_compile_match_two_scrutinees() {
    // match x, y with
    // | True, True => 0
    // | True, False => 1
    // | False, _ => 2
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let arms = vec![
        mk_arm(
            vec![mk_ctor_pat("True", vec![]), mk_ctor_pat("True", vec![])],
            0,
        ),
        mk_arm(
            vec![mk_ctor_pat("True", vec![]), mk_ctor_pat("False", vec![])],
            1,
        ),
        mk_arm(vec![mk_ctor_pat("False", vec![]), Pattern::Wildcard], 2),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // Should produce a Switch (the column picked may be x or y depending on scoring)
    match &tree {
        DecisionTree::Switch(_, branches, _) => {
            assert!(!branches.is_empty());
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_compile_match_or_pattern() {
    // match x with
    // | A | B => 0
    // | C => 1
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(
            vec![Pattern::Or(vec![
                mk_ctor_pat("A", vec![]),
                mk_ctor_pat("B", vec![]),
            ])],
            0,
        ),
        mk_arm(vec![mk_ctor_pat("C", vec![])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);

    match &tree {
        DecisionTree::Switch(_, branches, _) => {
            // A, B, and C should all appear as branches
            let names: Vec<String> = branches.iter().map(|(t, _)| t.name.to_string()).collect();
            assert!(names.contains(&"A".to_string()));
            assert!(names.contains(&"B".to_string()));
            assert!(names.contains(&"C".to_string()));
        }
        other => panic!("expected Switch, got {other:?}"),
    }
}

#[test]
fn test_compile_match_no_scrutinees() {
    let scrutinees: Vec<Var> = vec![];
    let arms = vec![mk_arm(vec![], 42)];
    let tree = compile_match(&scrutinees, &arms);
    assert_eq!(tree, DecisionTree::Leaf(42));
}

// ---------------------------------------------------------------------------
// Column scoring tests
// ---------------------------------------------------------------------------

#[test]
fn test_score_column_prefers_constructors() {
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("A", vec![]), Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("B", vec![]), Pattern::Wildcard], 1),
    ];
    let score_0 = score_column(&arms, 0);
    let score_1 = score_column(&arms, 1);
    assert!(
        score_0 > score_1,
        "column 0 (constructors) should score higher than column 1 (wildcards)"
    );
}

#[test]
fn test_pick_column_selects_best() {
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("A", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard, mk_ctor_pat("B", vec![])], 1),
    ];
    let col = pick_column(&scrutinees, &arms);
    assert_eq!(col, 1, "should pick column 1 which has more constructors");
}

// ---------------------------------------------------------------------------
// Evaluation tests
// ---------------------------------------------------------------------------

#[test]
fn test_eval_leaf() {
    let tree = DecisionTree::Leaf(5);
    let env = MatchEnv::new(&[]);
    let result = eval_decision_tree(&tree, &env);
    assert_eq!(result.expect("should succeed"), 5);
}

#[test]
fn test_eval_sentinel_leaf_returns_nonexhaustive() {
    let tree = DecisionTree::Leaf(usize::MAX);
    let env = MatchEnv::new(&[]);
    let result = eval_decision_tree(&tree, &env);
    assert!(result.is_err());
}

#[test]
fn test_eval_simple_switch() {
    // Decision tree: switch x { None => 0, Some => 1 }
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![
            (mk_ctor_tag("None", 0), DecisionTree::Leaf(0)),
            (mk_ctor_tag("Some", 1), DecisionTree::Leaf(1)),
        ],
        None,
    );

    // Test with None
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("None", vec![]))]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 0);

    // Test with Some
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![MatchValue::Leaf]),
    )]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 1);
}

#[test]
fn test_eval_switch_with_default() {
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![(mk_ctor_tag("None", 0), DecisionTree::Leaf(0))],
        Some(Box::new(DecisionTree::Leaf(1))),
    );

    // Test with Some (falls through to default)
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![MatchValue::Leaf]),
    )]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 1);
}

#[test]
fn test_eval_unbound_variable_returns_error() {
    let scrutinee = mk_var("x");
    let tree = DecisionTree::Switch(
        scrutinee,
        vec![(mk_ctor_tag("A", 0), DecisionTree::Leaf(0))],
        None,
    );
    let env = MatchEnv::new(&[]);
    let result = eval_decision_tree(&tree, &env);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// Round-trip: compile then evaluate
// ---------------------------------------------------------------------------

#[test]
fn test_roundtrip_option_match() {
    // match x with
    // | None => 0
    // | Some _ => 1
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // Evaluate with None
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("None", vec![]))]);
    assert_eq!(
        eval_decision_tree(&tree, &env).expect("should match None"),
        0
    );

    // Evaluate with Some
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![MatchValue::Leaf]),
    )]);
    assert_eq!(
        eval_decision_tree(&tree, &env).expect("should match Some"),
        1
    );
}

#[test]
fn test_roundtrip_wildcard_default() {
    // match x with
    // | None => 0
    // | _ => 1
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![mk_ctor_pat("None", vec![])], 0),
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // None matches arm 0
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("None", vec![]))]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 0);

    // Some matches arm 1 (wildcard)
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![MatchValue::Leaf]),
    )]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 1);

    // Other constructors also match arm 1
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("Other", vec![]))]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 1);
}

#[test]
fn test_roundtrip_nested_option() {
    // match x with
    // | Some(Some(_)) => 0
    // | Some(None) => 1
    // | None => 2
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(
            vec![mk_ctor_pat(
                "Some",
                vec![mk_ctor_pat("Some", vec![Pattern::Wildcard])],
            )],
            0,
        ),
        mk_arm(
            vec![mk_ctor_pat("Some", vec![mk_ctor_pat("None", vec![])])],
            1,
        ),
        mk_arm(vec![mk_ctor_pat("None", vec![])], 2),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // None => 2
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("None", vec![]))]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 2);

    // Some(None) => 1
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![mk_ctor_val("None", vec![])]),
    )]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 1);

    // Some(Some(Leaf)) => 0
    let env = MatchEnv::new(&[(
        Name::from_string("x"),
        mk_ctor_val("Some", vec![mk_ctor_val("Some", vec![MatchValue::Leaf])]),
    )]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 0);
}

#[test]
fn test_roundtrip_two_scrutinees_bool_pair() {
    // match x, y with
    // | True, True => 0
    // | True, False => 1
    // | False, _ => 2
    let scrutinees = vec![mk_var("x"), mk_var("y")];
    let arms = vec![
        mk_arm(
            vec![mk_ctor_pat("True", vec![]), mk_ctor_pat("True", vec![])],
            0,
        ),
        mk_arm(
            vec![mk_ctor_pat("True", vec![]), mk_ctor_pat("False", vec![])],
            1,
        ),
        mk_arm(vec![mk_ctor_pat("False", vec![]), Pattern::Wildcard], 2),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // True, True => 0
    let env = MatchEnv::new(&[
        (Name::from_string("x"), mk_ctor_val("True", vec![])),
        (Name::from_string("y"), mk_ctor_val("True", vec![])),
    ]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 0);

    // True, False => 1
    let env = MatchEnv::new(&[
        (Name::from_string("x"), mk_ctor_val("True", vec![])),
        (Name::from_string("y"), mk_ctor_val("False", vec![])),
    ]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 1);

    // False, True => 2
    let env = MatchEnv::new(&[
        (Name::from_string("x"), mk_ctor_val("False", vec![])),
        (Name::from_string("y"), mk_ctor_val("True", vec![])),
    ]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 2);

    // False, False => 2
    let env = MatchEnv::new(&[
        (Name::from_string("x"), mk_ctor_val("False", vec![])),
        (Name::from_string("y"), mk_ctor_val("False", vec![])),
    ]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("match"), 2);
}

#[test]
fn test_roundtrip_first_match_wins() {
    // match x with
    // | _ => 0
    // | A => 1    (unreachable)
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        mk_arm(vec![Pattern::Wildcard], 0),
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    assert_eq!(tree, DecisionTree::Leaf(0), "wildcard arm should win");
}

// ---------------------------------------------------------------------------
// Guard tests
// ---------------------------------------------------------------------------

#[test]
fn test_compile_match_with_guard() {
    use crate::match_eval::eval_decision_tree_with_guards;

    // match x with
    // | A if guard => 0
    // | A => 1
    // | B => 2
    let guard_expr = clean_kernel::Expr::sort(clean_kernel::level::Level::zero());
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        MatchArm {
            patterns: vec![mk_ctor_pat("A", vec![])],
            guard: Some(guard_expr),
            body_idx: 0,
        },
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 2),
    ];
    let tree = compile_match(&scrutinees, &arms);

    // Evaluate with A and guard=true => arm 0
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("A", vec![]))]);
    let result = eval_decision_tree_with_guards(&tree, &env, &|_, _| Ok(true));
    assert_eq!(result.expect("should match"), 0);

    // Evaluate with A and guard=false => arm 1 (fallthrough)
    let result = eval_decision_tree_with_guards(&tree, &env, &|_, _| Ok(false));
    assert_eq!(result.expect("should match"), 1);
}

// ---------------------------------------------------------------------------
// Built-in const-guard evaluation tests
// ---------------------------------------------------------------------------

use clean_kernel::Expr;

/// Build the three-arm guarded tree shared by several tests:
/// `match x with | A if <guard> => 0 | A => 1 | B => 2`.
fn guarded_tree(guard: Expr) -> DecisionTree {
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        MatchArm {
            patterns: vec![mk_ctor_pat("A", vec![])],
            guard: Some(guard),
            body_idx: 0,
        },
        mk_arm(vec![mk_ctor_pat("A", vec![])], 1),
        mk_arm(vec![mk_ctor_pat("B", vec![])], 2),
    ];
    compile_match(&scrutinees, &arms)
}

fn env_x_a() -> MatchEnv {
    MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("A", vec![]))])
}

#[test]
fn test_try_eval_guard_const_bool_true_returns_true() {
    use crate::match_eval::try_eval_guard_const;
    assert_eq!(
        try_eval_guard_const(&Expr::const_str("Bool.true")),
        Some(true)
    );
    assert_eq!(try_eval_guard_const(&Expr::const_str("true")), Some(true));
}

#[test]
fn test_try_eval_guard_const_bool_false_returns_false() {
    use crate::match_eval::try_eval_guard_const;
    assert_eq!(
        try_eval_guard_const(&Expr::const_str("Bool.false")),
        Some(false)
    );
    assert_eq!(try_eval_guard_const(&Expr::const_str("false")), Some(false));
}

#[test]
fn test_try_eval_guard_const_unknown_const_returns_none() {
    use crate::match_eval::try_eval_guard_const;
    // A free reference we cannot reduce must stay unknown (not guessed).
    assert_eq!(try_eval_guard_const(&Expr::const_str("p")), None);
}

#[test]
fn test_try_eval_guard_const_not_negates() {
    use crate::match_eval::try_eval_guard_const;
    let not_true = Expr::app(Expr::const_str("Bool.not"), Expr::const_str("Bool.true"));
    assert_eq!(try_eval_guard_const(&not_true), Some(false));
    let not_false = Expr::app(Expr::const_str("not"), Expr::const_str("false"));
    assert_eq!(try_eval_guard_const(&not_false), Some(true));
}

#[test]
fn test_try_eval_guard_const_not_of_unknown_returns_none() {
    use crate::match_eval::try_eval_guard_const;
    let not_unknown = Expr::app(Expr::const_str("Bool.not"), Expr::const_str("p"));
    assert_eq!(try_eval_guard_const(&not_unknown), None);
}

#[test]
fn test_try_eval_guard_const_and_or() {
    use crate::match_eval::try_eval_guard_const;
    let and_tf = Expr::apps(
        Expr::const_str("Bool.and"),
        [Expr::const_str("Bool.true"), Expr::const_str("Bool.false")],
    );
    assert_eq!(try_eval_guard_const(&and_tf), Some(false));
    let or_tf = Expr::apps(
        Expr::const_str("Bool.or"),
        [Expr::const_str("Bool.true"), Expr::const_str("Bool.false")],
    );
    assert_eq!(try_eval_guard_const(&or_tf), Some(true));
}

#[test]
fn test_try_eval_guard_const_and_with_unknown_operand_returns_none() {
    use crate::match_eval::try_eval_guard_const;
    // Strict: even though `false && _` is logically false, one unresolved
    // operand must keep the whole guard unknown (no guessing).
    let and_unknown = Expr::apps(
        Expr::const_str("Bool.and"),
        [Expr::const_str("Bool.false"), Expr::const_str("p")],
    );
    assert_eq!(try_eval_guard_const(&and_unknown), None);
}

#[test]
fn test_try_eval_guard_const_nat_comparisons() {
    use crate::match_eval::try_eval_guard_const;
    let beq = Expr::apps(
        Expr::const_str("Nat.beq"),
        [Expr::nat_lit(3), Expr::nat_lit(3)],
    );
    assert_eq!(try_eval_guard_const(&beq), Some(true));
    let ble = Expr::apps(
        Expr::const_str("Nat.ble"),
        [Expr::nat_lit(2), Expr::nat_lit(5)],
    );
    assert_eq!(try_eval_guard_const(&ble), Some(true));
    let blt = Expr::apps(
        Expr::const_str("Nat.blt"),
        [Expr::nat_lit(5), Expr::nat_lit(5)],
    );
    assert_eq!(try_eval_guard_const(&blt), Some(false));
}

#[test]
fn test_try_eval_guard_const_nat_comparison_nonliteral_returns_none() {
    use crate::match_eval::try_eval_guard_const;
    let beq = Expr::apps(
        Expr::const_str("Nat.beq"),
        [Expr::nat_lit(3), Expr::const_str("n")],
    );
    assert_eq!(try_eval_guard_const(&beq), None);
}

#[test]
fn test_try_eval_guard_const_decide_wraps_bool() {
    use clean_kernel::level::Level;

    use crate::match_eval::try_eval_guard_const;
    // decide is applied to an instance/proof spine; the recognizable boolean
    // is whichever argument already reduces.
    let decide = Expr::apps(
        Expr::const_str("Decidable.decide"),
        [Expr::sort(Level::zero()), Expr::const_str("Bool.true")],
    );
    assert_eq!(try_eval_guard_const(&decide), Some(true));
}

#[test]
fn test_eval_decision_tree_const_guard_true_selects_arm() {
    // Guard is `Bool.true` => guarded arm 0 is selected.
    let tree = guarded_tree(Expr::const_str("Bool.true"));
    let env = env_x_a();
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 0);
}

#[test]
fn test_eval_decision_tree_const_guard_false_falls_through() {
    // Guard is `Bool.false` => fall through to the next matching arm (1).
    let tree = guarded_tree(Expr::const_str("Bool.false"));
    let env = env_x_a();
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 1);
}

#[test]
fn test_eval_decision_tree_unknown_guard_falls_through_no_panic() {
    // A guard that cannot be statically evaluated must fall through
    // conservatively (arm not selected) without panicking.
    let tree = guarded_tree(Expr::const_str("p"));
    let env = env_x_a();
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 1);
}

#[test]
fn test_eval_decision_tree_const_guard_nat_comparison_selects_arm() {
    // Guard is `Nat.blt 1 2` (= true) => guarded arm 0 selected.
    let guard = Expr::apps(
        Expr::const_str("Nat.blt"),
        [Expr::nat_lit(1), Expr::nat_lit(2)],
    );
    let tree = guarded_tree(guard);
    let env = env_x_a();
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 0);
}

#[test]
fn test_eval_decision_tree_unknown_guard_then_default_no_panic() {
    // match x with | A if <unknown> => 0 | _ => 1
    // With x = B and an unresolved guard, evaluation must reach the wildcard
    // arm (1) without panicking — the unknown guard does not wrongly fire.
    let scrutinees = vec![mk_var("x")];
    let arms = vec![
        MatchArm {
            patterns: vec![mk_ctor_pat("A", vec![])],
            guard: Some(Expr::const_str("p")),
            body_idx: 0,
        },
        mk_arm(vec![Pattern::Wildcard], 1),
    ];
    let tree = compile_match(&scrutinees, &arms);
    let env = MatchEnv::new(&[(Name::from_string("x"), mk_ctor_val("B", vec![]))]);
    assert_eq!(eval_decision_tree(&tree, &env).expect("should match"), 1);
}
