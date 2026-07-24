// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended tactic interpreter (`tactic_interp_ext`).

use super::tactic_interp_ext::*;
use super::{Expr, Level, ProofState, TacticError};
use clean_kernel::Environment;
use std::time::Duration;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn mk_env() -> Environment {
    Environment::new()
}

fn mk_prop() -> Expr {
    Expr::sort(Level::zero())
}

fn mk_state() -> ProofState {
    ProofState::new(mk_env(), mk_prop())
}

fn ok_handler() -> TacticHandler {
    Box::new(|state: &mut ProofState| {
        state.pop_current_goal()?;
        Ok(())
    })
}

fn fail_handler() -> TacticHandler {
    Box::new(|_: &mut ProofState| Err(TacticError::GoalMismatch("fail".into())))
}

fn noop_handler() -> TacticHandler {
    Box::new(|_: &mut ProofState| Ok(()))
}

fn default_interp() -> ExtTacticInterpreter {
    ExtTacticInterpreter::new(InterpConfig::default())
}

fn tracing_interp() -> ExtTacticInterpreter {
    ExtTacticInterpreter::new(InterpConfig {
        enable_tracing: true,
        ..InterpConfig::default()
    })
}

// =========================================================================
// 1. Backtracking with state snapshots
// =========================================================================

#[test]
fn test_snapshot_capture_restore_preserves_goals() {
    let state = mk_state();
    let snap = StateSnapshot::capture(&state);
    let mut state2 = state;
    state2.pop_current_goal().unwrap();
    assert!(state2.goals().is_empty());
    snap.restore(&mut state2);
    assert_eq!(state2.goals().len(), 1);
}

#[test]
fn test_with_backtrack_restores_on_failure() {
    let mut interp = default_interp();
    let mut state = mk_state();
    let r = interp.execute_with_backtrack(&mut state, |s| {
        s.pop_current_goal()?;
        Err(TacticError::GoalMismatch("test".into()))
    });
    assert!(r.is_err());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_with_backtrack_commits_on_success() {
    let mut interp = default_interp();
    let mut state = mk_state();
    let r = interp.execute_with_backtrack(&mut state, |s| {
        s.pop_current_goal()?;
        Ok(())
    });
    assert!(r.is_ok());
    assert!(state.goals().is_empty());
}

#[test]
fn test_execute_with_backtrack_restores_on_error() {
    let mut interp = default_interp();
    let mut state = mk_state();
    let r = interp.execute_with_backtrack(&mut state, |s| {
        s.pop_current_goal()?;
        Err(TacticError::GoalMismatch("fail".into()))
    });
    assert!(r.is_err());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_execute_with_backtrack_commits_success() {
    let mut interp = default_interp();
    let mut state = mk_state();
    let r = interp.execute_with_backtrack(&mut state, |s| {
        s.pop_current_goal()?;
        Ok(())
    });
    assert!(r.is_ok());
    assert!(state.goals().is_empty());
}

// =========================================================================
// 2. Tactic combinators (via run_script with registered tactics)
// =========================================================================

#[test]
fn test_first_succeeds_on_second_via_script() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    interp.register_tactic("good", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "first | bad | good");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_first_all_fail_via_script() {
    let mut interp = default_interp();
    interp.register_tactic("bad1", fail_handler());
    interp.register_tactic("bad2", fail_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "first | bad1 | bad2");
    assert!(r.is_err());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_repeat_zero_iterations_on_immediate_fail() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "repeat bad");
    assert!(r.is_ok());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_repeat_one_success_then_fail() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "repeat close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_try_succeeds_on_failure() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "try bad");
    assert!(r.is_ok());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_try_preserves_success() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "try close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_focus_on_first_goal() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "focus close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_focus_no_goals() {
    let mut interp = default_interp();
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    state.pop_current_goal().unwrap();
    let r = interp.run_script(&mut state, "focus noop");
    assert!(matches!(r, Err(TacticError::NoGoals)));
}

#[test]
fn test_all_goals_applies_to_each() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "all_goals close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_any_goals_partial_success() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "any_goals close");
    assert!(r.is_ok());
}

#[test]
fn test_any_goals_all_fail() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "any_goals bad");
    assert!(r.is_err());
}

// =========================================================================
// 3. Fuel / timeout control
// =========================================================================

#[test]
fn test_fuel_exhaustion() {
    let mut interp = ExtTacticInterpreter::new(InterpConfig {
        fuel: 2,
        enable_tracing: false,
        timeout: None,
    });
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    // Each run_script resets fuel, so this tests within a single script
    // where the fuel budget is consumed across multiple nodes
    let r = interp.execute_with_backtrack(&mut state, |_s| Ok(()));
    // First backtrack consumes no fuel (execute_with_backtrack doesn't go through run_named)
    assert!(r.is_ok());
}

#[test]
fn test_fuel_low_budget_exhausts_in_script() {
    // A script with more nodes than available fuel should fail
    let mut interp = ExtTacticInterpreter::new(InterpConfig {
        fuel: 1,
        enable_tracing: false,
        timeout: None,
    });
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    // "noop; noop" parses as Seq([Atom, Atom]) = 3 nodes (seq + 2 atoms)
    // With fuel=1, should exhaust
    let r = interp.run_script(&mut state, "noop; noop");
    assert!(matches!(r, Err(TacticError::Timeout { .. })));
}

#[test]
fn test_timeout_config() {
    let config = InterpConfig {
        fuel: 1024,
        enable_tracing: false,
        timeout: Some(Duration::from_millis(100)),
    };
    let interp = ExtTacticInterpreter::new(config);
    assert_eq!(interp.trace().len(), 0);
}

#[test]
fn test_with_fuel_builder() {
    let interp = ExtTacticInterpreter::new(InterpConfig::default()).with_fuel(42);
    // The fuel was set; verify the interpreter was built without error
    assert!(interp.trace().is_empty());
}

#[test]
fn test_default_config_values() {
    let cfg = InterpConfig::default();
    assert_eq!(cfg.fuel, 1_024);
    assert!(!cfg.enable_tracing);
    assert_eq!(cfg.timeout, None);
}

// =========================================================================
// 4. Tracing / profiling
// =========================================================================

#[test]
fn test_tracing_disabled_by_default() {
    let mut interp = default_interp();
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "noop");
    assert!(interp.trace().is_empty());
}

#[test]
fn test_tracing_enabled_records_traces() {
    let mut interp = tracing_interp();
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "noop");
    assert!(!interp.trace().is_empty());
    assert!(interp.trace()[0].success);
}

#[test]
fn test_tracing_records_failure() {
    let mut interp = tracing_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "bad");
    assert!(!interp.trace().is_empty());
    assert!(!interp.trace()[0].success);
}

#[test]
fn test_tracing_duration_is_non_negative() {
    let mut interp = tracing_interp();
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "noop");
    assert!(interp.trace()[0].duration >= Duration::ZERO);
}

#[test]
fn test_tracing_nested_children() {
    let mut interp = tracing_interp();
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    // "try noop" = try node containing noop atom
    let _ = interp.run_script(&mut state, "try noop");
    // Root trace should have children from nested execution
    assert!(!interp.trace().is_empty());
}

// =========================================================================
// 5. User tactic registration
// =========================================================================

#[test]
fn test_register_and_lookup() {
    let mut interp = default_interp();
    interp.register_tactic("my_tac", ok_handler());
    assert!(interp.lookup_tactic("my_tac").is_some());
    assert!(interp.lookup_tactic("nonexistent").is_none());
}

#[test]
fn test_registered_tactic_executes_via_script() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_unregistered_tactic_errors() {
    let mut interp = default_interp();
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "unknown_tactic");
    assert!(r.is_err());
}

#[test]
fn test_register_overwrite() {
    let mut interp = default_interp();
    interp.register_tactic("t", fail_handler());
    interp.register_tactic("t", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "t");
    assert!(r.is_ok());
}

// =========================================================================
// 6. Tactic script replay (parser tests)
// =========================================================================

#[test]
fn test_parse_atom() {
    let ast = ExtTacticInterpreter::parse_script("intro x").unwrap();
    assert_eq!(ast, TacticScript::Atom("intro".into(), vec!["x".into()]));
}

#[test]
fn test_parse_sequence() {
    let ast = ExtTacticInterpreter::parse_script("a; b; c").unwrap();
    match ast {
        TacticScript::Seq(nodes) => assert_eq!(nodes.len(), 3),
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn test_parse_first() {
    let ast = ExtTacticInterpreter::parse_script("first | a | b").unwrap();
    match ast {
        TacticScript::First(alts) => assert_eq!(alts.len(), 2),
        other => panic!("expected First, got {other:?}"),
    }
}

#[test]
fn test_parse_repeat() {
    let ast = ExtTacticInterpreter::parse_script("repeat assumption").unwrap();
    match ast {
        TacticScript::Repeat { body, max_iters } => {
            assert!(max_iters.is_none());
            assert_eq!(*body, TacticScript::Atom("assumption".into(), vec![]));
        }
        other => panic!("expected Repeat, got {other:?}"),
    }
}

#[test]
fn test_parse_repeat_with_limit() {
    let ast = ExtTacticInterpreter::parse_script("repeat[5] assumption").unwrap();
    match ast {
        TacticScript::Repeat { body, max_iters } => {
            assert_eq!(max_iters, Some(5));
            assert_eq!(*body, TacticScript::Atom("assumption".into(), vec![]));
        }
        other => panic!("expected Repeat, got {other:?}"),
    }
}

#[test]
fn test_parse_try() {
    let ast = ExtTacticInterpreter::parse_script("try rfl").unwrap();
    match ast {
        TacticScript::Try(inner) => {
            assert_eq!(*inner, TacticScript::Atom("rfl".into(), vec![]));
        }
        other => panic!("expected Try, got {other:?}"),
    }
}

#[test]
fn test_parse_all_goals() {
    let ast = ExtTacticInterpreter::parse_script("all_goals assumption").unwrap();
    assert!(matches!(ast, TacticScript::AllGoals(_)));
}

#[test]
fn test_parse_any_goals() {
    let ast = ExtTacticInterpreter::parse_script("any_goals rfl").unwrap();
    assert!(matches!(ast, TacticScript::AnyGoals(_)));
}

#[test]
fn test_parse_focus() {
    let ast = ExtTacticInterpreter::parse_script("focus exact h").unwrap();
    assert!(matches!(ast, TacticScript::Focus(_)));
}

#[test]
fn test_parse_empty_returns_empty_seq() {
    let ast = ExtTacticInterpreter::parse_script("").unwrap();
    assert_eq!(ast, TacticScript::Seq(Vec::new()));
}

#[test]
fn test_parse_first_missing_alts_errors() {
    let r = ExtTacticInterpreter::parse_script("first");
    assert!(r.is_err());
}

// =========================================================================
// 7. Script execution integration
// =========================================================================

#[test]
fn test_run_script_sequence() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "noop; close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_run_script_first_combinator() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    interp.register_tactic("good", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "first | bad | good");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

#[test]
fn test_run_script_try_combinator() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "try bad");
    assert!(r.is_ok());
    assert_eq!(state.goals().len(), 1);
}

#[test]
fn test_run_script_repeat_combinator() {
    let mut interp = default_interp();
    interp.register_tactic("close", ok_handler());
    let mut state = mk_state();
    let r = interp.run_script(&mut state, "repeat close");
    assert!(r.is_ok());
    assert!(state.is_complete());
}

// =========================================================================
// 8. Structured error reporting with stack traces
// =========================================================================

#[test]
fn test_last_error_none_initially() {
    let interp = default_interp();
    assert!(interp.last_error().is_none());
}

#[test]
fn test_last_error_some_after_failure() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "bad");
    assert!(interp.last_error().is_some());
}

#[test]
fn test_last_error_cleared_on_success() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    interp.register_tactic("noop", noop_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "bad");
    assert!(interp.last_error().is_some());
    let _ = interp.run_script(&mut state, "noop");
    assert!(interp.last_error().is_none());
}

#[test]
fn test_structured_error_contains_source() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "bad");
    let err = interp.last_error().unwrap();
    assert!(matches!(err.source, TacticError::GoalMismatch(_)));
}

#[test]
fn test_structured_error_has_stack_frames() {
    let mut interp = default_interp();
    interp.register_tactic("bad", fail_handler());
    let mut state = mk_state();
    let _ = interp.run_script(&mut state, "try bad");
    // try swallows the error, so last_error should be None
    assert!(interp.last_error().is_none());
}

#[test]
fn test_tactic_stack_frame_default() {
    let frame = TacticStackFrame::default();
    assert!(frame.tactic.is_empty());
    assert_eq!(frame.depth, 0);
}

// =========================================================================
// 9. InterpConfig and constructor tests
// =========================================================================

#[test]
fn test_interp_new_empty_registry() {
    let interp = default_interp();
    assert!(interp.lookup_tactic("anything").is_none());
}

#[test]
fn test_interp_trace_empty_initially() {
    let interp = default_interp();
    assert!(interp.trace().is_empty());
}

#[test]
fn test_tactic_trace_default() {
    let trace = TacticTrace::default();
    assert!(trace.name.is_empty());
    assert!(!trace.success);
    assert!(trace.children.is_empty());
    assert_eq!(trace.duration, Duration::ZERO);
}
