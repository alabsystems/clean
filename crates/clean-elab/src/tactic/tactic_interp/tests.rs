// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the structured tactic script interpreter.

use super::*;
use clean_kernel::{BinderInfo, Environment, Expr, Level};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_env() -> Environment {
    Environment::new()
}

/// Create a proof state with a simple goal: `Prop`.
fn prop_goal_state() -> ProofState {
    let env = mk_env();
    ProofState::new(env, Expr::sort(Level::zero()))
}

/// Create a proof state with a Pi goal `(A : Prop) -> Prop` to test `intro`.
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
fn pi_goal_state() -> ProofState {
    let env = mk_env();
    let target = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::sort(Level::zero()),
    );
    ProofState::new(env, target)
}

/// Create a proof state with two goals for combinator testing.
fn two_goal_state() -> ProofState {
    let env = mk_env();
    let mut state = ProofState::new(env.clone(), Expr::sort(Level::zero()));
    // Add a second goal by splitting or manually inserting.
    let meta_id = state.metas_mut().fresh(Expr::sort(Level::zero()));
    state.goals.push_back(super::super::core::Goal {
        meta_id,
        target: Expr::sort(Level::zero()),
        local_ctx: Vec::new(),
        tag: None,
    });
    state
}

// ---------------------------------------------------------------------------
// Parsing: atoms
// ---------------------------------------------------------------------------

#[test]
fn test_parse_atom_simple_name() {
    let node = parse_tactic_script("rfl").expect("should parse");
    assert_eq!(
        node,
        TacticNode::Atom(TacticAtom {
            name: "rfl".into(),
            args: vec![],
        })
    );
}

#[test]
fn test_parse_atom_with_args() {
    let node = parse_tactic_script("intro x").expect("should parse");
    assert_eq!(
        node,
        TacticNode::Atom(TacticAtom {
            name: "intro".into(),
            args: vec!["x".into()],
        })
    );
}

#[test]
fn test_parse_atom_multi_args() {
    let node = parse_tactic_script("intros a b c").expect("should parse");
    assert_eq!(
        node,
        TacticNode::Atom(TacticAtom {
            name: "intros".into(),
            args: vec!["a".into(), "b".into(), "c".into()],
        })
    );
}

// ---------------------------------------------------------------------------
// Parsing: sequences
// ---------------------------------------------------------------------------

#[test]
fn test_parse_semicolon_sequence() {
    let node = parse_tactic_script("intro x; rfl").expect("should parse");
    match node {
        TacticNode::Seq(nodes) => {
            assert_eq!(nodes.len(), 2);
            assert_eq!(
                nodes[0],
                TacticNode::Atom(TacticAtom {
                    name: "intro".into(),
                    args: vec!["x".into()],
                })
            );
            assert_eq!(
                nodes[1],
                TacticNode::Atom(TacticAtom {
                    name: "rfl".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn test_parse_newline_sequence() {
    let node = parse_tactic_script("intro x\nrfl").expect("should parse");
    match node {
        TacticNode::Seq(nodes) => assert_eq!(nodes.len(), 2),
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn test_parse_mixed_semicolon_newline() {
    let script = "intro x; apply h\nassumption";
    let node = parse_tactic_script(script).expect("should parse");
    match node {
        TacticNode::Seq(nodes) => assert_eq!(nodes.len(), 3),
        other => panic!("expected Seq of 3, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Parsing: combinators
// ---------------------------------------------------------------------------

#[test]
fn test_parse_try_combinator() {
    let node = parse_tactic_script("try rfl").expect("should parse");
    match node {
        TacticNode::Try(inner) => {
            assert_eq!(
                *inner,
                TacticNode::Atom(TacticAtom {
                    name: "rfl".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected Try, got {other:?}"),
    }
}

#[test]
fn test_parse_repeat_combinator() {
    let node = parse_tactic_script("repeat intro h").expect("should parse");
    match node {
        TacticNode::Repeat(inner) => {
            assert_eq!(
                *inner,
                TacticNode::Atom(TacticAtom {
                    name: "intro".into(),
                    args: vec!["h".into()],
                })
            );
        }
        other => panic!("expected Repeat, got {other:?}"),
    }
}

#[test]
fn test_parse_first_combinator_pipes() {
    let node = parse_tactic_script("first | rfl | assumption").expect("should parse");
    match node {
        TacticNode::First(alts) => {
            assert_eq!(alts.len(), 2);
            assert_eq!(
                alts[0],
                TacticNode::Atom(TacticAtom {
                    name: "rfl".into(),
                    args: vec![],
                })
            );
            assert_eq!(
                alts[1],
                TacticNode::Atom(TacticAtom {
                    name: "assumption".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected First, got {other:?}"),
    }
}

#[test]
fn test_parse_all_goals_combinator() {
    let node = parse_tactic_script("all_goals trivial").expect("should parse");
    match node {
        TacticNode::AllGoals(inner) => {
            assert_eq!(
                *inner,
                TacticNode::Atom(TacticAtom {
                    name: "trivial".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected AllGoals, got {other:?}"),
    }
}

#[test]
fn test_parse_any_goals_combinator() {
    let node = parse_tactic_script("any_goals assumption").expect("should parse");
    match node {
        TacticNode::AnyGoals(inner) => {
            assert_eq!(
                *inner,
                TacticNode::Atom(TacticAtom {
                    name: "assumption".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected AnyGoals, got {other:?}"),
    }
}

#[test]
fn test_parse_focus_combinator() {
    let node = parse_tactic_script("focus rfl").expect("should parse");
    match node {
        TacticNode::Focus(inner) => {
            assert_eq!(
                *inner,
                TacticNode::Atom(TacticAtom {
                    name: "rfl".into(),
                    args: vec![],
                })
            );
        }
        other => panic!("expected Focus, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Parsing: skip / done
// ---------------------------------------------------------------------------

#[test]
fn test_parse_skip() {
    let node = parse_tactic_script("skip").expect("should parse");
    assert_eq!(node, TacticNode::Skip);
}

#[test]
fn test_parse_done() {
    let node = parse_tactic_script("done").expect("should parse");
    assert_eq!(node, TacticNode::Done);
}

#[test]
fn test_parse_empty_script() {
    let node = parse_tactic_script("").expect("should parse");
    assert_eq!(node, TacticNode::Skip);
}

#[test]
fn test_parse_only_comments() {
    let node = parse_tactic_script("-- just a comment").expect("should parse");
    assert_eq!(node, TacticNode::Skip);
}

// ---------------------------------------------------------------------------
// Parsing: error cases
// ---------------------------------------------------------------------------

#[test]
fn test_parse_repeat_no_arg() {
    let result = parse_tactic_script("repeat");
    assert!(result.is_err(), "repeat without arg should fail");
}

#[test]
fn test_parse_first_no_alternatives() {
    let result = parse_tactic_script("first");
    assert!(result.is_err(), "first without alternatives should fail");
}

// ---------------------------------------------------------------------------
// Execution: atom dispatch
// ---------------------------------------------------------------------------

#[test]
fn test_execute_sorry_closes_goal() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Atom(TacticAtom {
        name: "sorry".into(),
        args: vec![],
    });
    interp
        .execute(&node, &mut state)
        .expect("sorry should succeed");
    assert!(state.is_complete(), "sorry should close the goal");
}

#[test]
fn test_execute_unknown_tactic_fails() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Atom(TacticAtom {
        name: "nonexistent_tactic_xyz".into(),
        args: vec![],
    });
    let result = interp.execute(&node, &mut state);
    assert!(result.is_err(), "unknown tactic should fail");
}

#[test]
fn test_execute_skip_is_noop() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let goal_count = state.goals().len();
    let interp = TacticInterpreter::new(&env);

    interp
        .execute(&TacticNode::Skip, &mut state)
        .expect("skip should succeed");
    assert_eq!(state.goals().len(), goal_count);
}

// ---------------------------------------------------------------------------
// Execution: sequence
// ---------------------------------------------------------------------------

#[test]
fn test_execute_seq_sorry_closes() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Seq(vec![
        TacticNode::Skip,
        TacticNode::Atom(TacticAtom {
            name: "sorry".into(),
            args: vec![],
        }),
    ]);
    interp
        .execute(&node, &mut state)
        .expect("seq with sorry should succeed");
    assert!(state.is_complete());
}

#[test]
fn test_execute_seq_error_propagation() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Seq(vec![
        TacticNode::Atom(TacticAtom {
            name: "nonexistent".into(),
            args: vec![],
        }),
        TacticNode::Atom(TacticAtom {
            name: "sorry".into(),
            args: vec![],
        }),
    ]);
    let result = interp.execute(&node, &mut state);
    assert!(result.is_err(), "error in seq should propagate");
    assert!(!state.is_complete(), "sorry should not have run");
}

// ---------------------------------------------------------------------------
// Execution: try combinator
// ---------------------------------------------------------------------------

#[test]
fn test_execute_try_swallows_failure() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Try(Box::new(TacticNode::Atom(TacticAtom {
        name: "nonexistent".into(),
        args: vec![],
    })));
    interp
        .execute(&node, &mut state)
        .expect("try should always succeed");
    assert!(!state.is_complete(), "state should be unchanged");
}

#[test]
fn test_execute_try_passes_success() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Try(Box::new(TacticNode::Atom(TacticAtom {
        name: "sorry".into(),
        args: vec![],
    })));
    interp
        .execute(&node, &mut state)
        .expect("try should succeed");
    assert!(state.is_complete(), "sorry should have closed the goal");
}

// ---------------------------------------------------------------------------
// Execution: first combinator
// ---------------------------------------------------------------------------

#[test]
fn test_execute_first_picks_first_success() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    let node = TacticNode::First(vec![
        TacticNode::Atom(TacticAtom {
            name: "nonexistent".into(),
            args: vec![],
        }),
        TacticNode::Atom(TacticAtom {
            name: "sorry".into(),
            args: vec![],
        }),
    ]);
    interp
        .execute(&node, &mut state)
        .expect("first should succeed on second alt");
    assert!(state.is_complete());
}

#[test]
fn test_execute_first_all_fail() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    let node = TacticNode::First(vec![
        TacticNode::Atom(TacticAtom {
            name: "nonexistent1".into(),
            args: vec![],
        }),
        TacticNode::Atom(TacticAtom {
            name: "nonexistent2".into(),
            args: vec![],
        }),
    ]);
    let result = interp.execute(&node, &mut state);
    assert!(result.is_err(), "first should fail when all alts fail");
}

// ---------------------------------------------------------------------------
// Execution: repeat
// ---------------------------------------------------------------------------

#[test]
fn test_execute_repeat_terminates_on_failure() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    // `repeat nonexistent` should succeed (zero iterations).
    let node = TacticNode::Repeat(Box::new(TacticNode::Atom(TacticAtom {
        name: "nonexistent".into(),
        args: vec![],
    })));
    interp
        .execute(&node, &mut state)
        .expect("repeat should succeed even with 0 iterations");
    assert!(!state.is_complete());
}

#[test]
fn test_execute_repeat_sorry_once() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    let node = TacticNode::Repeat(Box::new(TacticNode::Atom(TacticAtom {
        name: "sorry".into(),
        args: vec![],
    })));
    interp
        .execute(&node, &mut state)
        .expect("repeat sorry should succeed");
    assert!(state.is_complete());
}

// ---------------------------------------------------------------------------
// Execution: done
// ---------------------------------------------------------------------------

#[test]
fn test_execute_done_succeeds_when_complete() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    // Close the goal first.
    interp
        .execute(
            &TacticNode::Atom(TacticAtom {
                name: "sorry".into(),
                args: vec![],
            }),
            &mut state,
        )
        .unwrap();
    assert!(state.is_complete());

    interp
        .execute(&TacticNode::Done, &mut state)
        .expect("done should succeed when complete");
}

#[test]
fn test_execute_done_fails_when_incomplete() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let interp = TacticInterpreter::new(&env);

    let result = interp.execute(&TacticNode::Done, &mut state);
    assert!(result.is_err(), "done should fail when goals remain");
}

// ---------------------------------------------------------------------------
// Execution: focus
// ---------------------------------------------------------------------------

#[test]
fn test_execute_focus_on_first_goal() {
    let env = mk_env();
    let mut state = two_goal_state();
    assert_eq!(state.goals().len(), 2);

    let interp = TacticInterpreter::new(&env);
    let node = TacticNode::Focus(Box::new(TacticNode::Atom(TacticAtom {
        name: "sorry".into(),
        args: vec![],
    })));
    interp
        .execute(&node, &mut state)
        .expect("focus sorry should succeed");
    // The first goal is closed; the second remains.
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_execute_focus_no_goals() {
    let env = mk_env();
    let mut state = prop_goal_state();
    // Close all goals first.
    let interp = TacticInterpreter::new(&env);
    interp
        .execute(
            &TacticNode::Atom(TacticAtom {
                name: "sorry".into(),
                args: vec![],
            }),
            &mut state,
        )
        .unwrap();
    assert!(state.is_complete());

    let result = interp.execute(&TacticNode::Focus(Box::new(TacticNode::Skip)), &mut state);
    assert!(result.is_err(), "focus with no goals should fail");
}

// ---------------------------------------------------------------------------
// run_tactic_script convenience
// ---------------------------------------------------------------------------

#[test]
fn test_run_tactic_script_sorry() {
    let env = mk_env();
    let mut state = prop_goal_state();
    run_tactic_script("sorry", &mut state, &env).expect("should succeed");
    assert!(state.is_complete());
}

#[test]
fn test_run_tactic_script_skip_then_sorry() {
    let env = mk_env();
    let mut state = prop_goal_state();
    run_tactic_script("skip; sorry", &mut state, &env).expect("should succeed");
    assert!(state.is_complete());
}

#[test]
fn test_run_tactic_script_comment_stripping() {
    let env = mk_env();
    let mut state = prop_goal_state();
    let script = "-- this is a comment\nsorry -- close it";
    run_tactic_script(script, &mut state, &env).expect("should succeed");
    assert!(state.is_complete());
}

// ---------------------------------------------------------------------------
// TacticAtom::to_tactic_string
// ---------------------------------------------------------------------------

#[test]
fn test_atom_to_tactic_string_no_args() {
    let atom = TacticAtom {
        name: "rfl".into(),
        args: vec![],
    };
    assert_eq!(atom.to_tactic_string(), "rfl");
}

#[test]
fn test_atom_to_tactic_string_with_args() {
    let atom = TacticAtom {
        name: "intro".into(),
        args: vec!["x".into()],
    };
    assert_eq!(atom.to_tactic_string(), "intro x");
}

#[test]
fn test_atom_to_tactic_string_multi_args() {
    let atom = TacticAtom {
        name: "intros".into(),
        args: vec!["a".into(), "b".into(), "c".into()],
    };
    assert_eq!(atom.to_tactic_string(), "intros a b c");
}
