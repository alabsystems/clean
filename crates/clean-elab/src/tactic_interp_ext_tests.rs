// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended tactic interpretation (`tactic_interp_ext`).

use crate::tactic::Goal;
use crate::tactic_interp_ext::*;
use crate::tactic_interp_profile::TacticHeartbeatProfile;
use crate::unify::{MetaId, MetaState};
use clean_kernel::{Expr, Level};

/// Helper: create a simple goal with the given target expression.
fn make_goal(target: Expr) -> Goal {
    let mut metas = MetaState::new();
    let meta_id = metas.fresh(target.clone());
    Goal {
        meta_id,
        target,
        local_ctx: Vec::new(),
        tag: None,
    }
}

/// Helper: create N goals with Prop targets.
fn make_goals(n: usize) -> Vec<Goal> {
    (0..n)
        .map(|i| {
            let target = Expr::sort(Level::zero());
            Goal {
                meta_id: MetaId(i as u64),
                target,
                local_ctx: Vec::new(),
                tag: None,
            }
        })
        .collect()
}

/// Helper: default config.
fn default_config() -> TacticInterpConfig {
    TacticInterpConfig::default()
}

/// Helper: config with sorry allowed.
fn sorry_config() -> TacticInterpConfig {
    TacticInterpConfig {
        allow_sorry: true,
        ..Default::default()
    }
}

/// Helper: config with tracing enabled.
fn trace_config() -> TacticInterpConfig {
    TacticInterpConfig {
        trace_enabled: true,
        ..Default::default()
    }
}

// =========================================================================
// TacticInterpConfig tests
// =========================================================================

#[test]
fn test_config_default_heartbeats() {
    let config = TacticInterpConfig::default();
    assert_eq!(config.max_heartbeats, 200_000);
}

#[test]
fn test_config_default_trace_disabled() {
    let config = TacticInterpConfig::default();
    assert!(!config.trace_enabled);
}

#[test]
fn test_config_default_timeout_none() {
    let config = TacticInterpConfig::default();
    assert!(config.timeout_ms.is_none());
}

#[test]
fn test_config_default_sorry_disallowed() {
    let config = TacticInterpConfig::default();
    assert!(!config.allow_sorry);
}

#[test]
fn test_config_custom_heartbeats() {
    let config = TacticInterpConfig {
        max_heartbeats: 500,
        ..Default::default()
    };
    assert_eq!(config.max_heartbeats, 500);
}

// =========================================================================
// TacticInterpState tests
// =========================================================================

#[test]
fn test_state_push_goal() {
    let goals = make_goals(1);
    let config = default_config();
    let mut state = TacticInterpState::new(goals, &config);
    assert_eq!(state.goal_count(), 1);

    let extra = make_goal(Expr::sort(Level::zero()));
    state.push_goal(extra);
    assert_eq!(state.goal_count(), 2);
}

#[test]
fn test_state_pop_goal() {
    let goals = make_goals(2);
    let config = default_config();
    let mut state = TacticInterpState::new(goals, &config);

    let popped = state.pop_goal();
    assert!(popped.is_some());
    assert_eq!(state.goal_count(), 1);
}

#[test]
fn test_state_pop_goal_empty() {
    let config = default_config();
    let mut state = TacticInterpState::new(Vec::new(), &config);
    assert!(state.pop_goal().is_none());
}

#[test]
fn test_state_tick_heartbeat_within_budget() {
    let config = TacticInterpConfig {
        max_heartbeats: 10,
        ..Default::default()
    };
    let mut state = TacticInterpState::new(Vec::new(), &config);

    for _ in 0..10 {
        state.tick_heartbeat().expect("should be within budget");
    }
    assert_eq!(state.heartbeats, 10);
}

#[test]
fn test_state_tick_heartbeat_exceeds_budget() {
    let config = TacticInterpConfig {
        max_heartbeats: 2,
        ..Default::default()
    };
    let mut state = TacticInterpState::new(Vec::new(), &config);

    state.tick_heartbeat().expect("tick 1");
    state.tick_heartbeat().expect("tick 2");
    let result = state.tick_heartbeat();
    assert!(result.is_err(), "should exceed budget on tick 3");
}

#[test]
fn test_state_trace_enabled() {
    let config = trace_config();
    let mut state = TacticInterpState::new(Vec::new(), &config);
    state.trace("hello");
    state.trace("world");
    assert_eq!(state.trace_log.len(), 2);
    assert_eq!(state.trace_log[0], "hello");
    assert_eq!(state.trace_log[1], "world");
}

#[test]
fn test_state_trace_disabled_noop() {
    let config = default_config();
    let mut state = TacticInterpState::new(Vec::new(), &config);
    state.trace("should not appear");
    assert!(state.trace_log.is_empty());
}

#[test]
fn test_state_is_complete_empty() {
    let config = default_config();
    let state = TacticInterpState::new(Vec::new(), &config);
    assert!(state.is_complete());
}

#[test]
fn test_state_is_complete_with_goals() {
    let config = default_config();
    let state = TacticInterpState::new(make_goals(1), &config);
    assert!(!state.is_complete());
}

// =========================================================================
// TacticCommand construction tests
// =========================================================================

#[test]
fn test_command_named_construction() {
    let cmd = TacticCommand::Named {
        name: "intro".to_string(),
        args: vec![],
    };
    assert!(matches!(cmd, TacticCommand::Named { .. }));
}

#[test]
fn test_command_sequence_construction() {
    let cmd = TacticCommand::Sequence(vec![
        TacticCommand::Named {
            name: "intro".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
    ]);
    if let TacticCommand::Sequence(cmds) = &cmd {
        assert_eq!(cmds.len(), 2);
    } else {
        panic!("expected Sequence");
    }
}

#[test]
fn test_command_sorry_construction() {
    let cmd = TacticCommand::Sorry;
    assert_eq!(cmd, TacticCommand::Sorry);
}

// =========================================================================
// interpret_tactic_block tests
// =========================================================================

#[test]
fn test_interpret_empty_tactics_with_goals() {
    let goals = make_goals(2);
    let config = default_config();
    let result = interpret_tactic_block(goals, &[], &config).expect("empty tactics should succeed");
    assert_eq!(result.remaining_goals.len(), 2);
    assert!(result.proof_term.is_none());
}

#[test]
fn test_interpret_empty_tactics_no_goals() {
    let config = default_config();
    let result = interpret_tactic_block(Vec::new(), &[], &config).expect("empty block, no goals");
    assert!(result.remaining_goals.is_empty());
    assert!(result.proof_term.is_some());
}

#[test]
fn test_interpret_named_tactic_closes_goal() {
    let goals = make_goals(1);
    let config = default_config();
    let tactics = vec![TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("should close goal");
    assert!(result.remaining_goals.is_empty());
    assert!(result.proof_term.is_some());
}

#[test]
fn test_interpret_skip_does_not_close_goal() {
    let goals = make_goals(1);
    let config = default_config();
    let tactics = vec![TacticCommand::Named {
        name: "skip".to_string(),
        args: vec![],
    }];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("skip should succeed");
    assert_eq!(result.remaining_goals.len(), 1);
}

#[test]
fn test_interpret_sequence_closes_multiple_goals() {
    let goals = make_goals(3);
    let config = default_config();
    let tactics = vec![TacticCommand::Sequence(vec![
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
    ])];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("should close all goals");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_sorry_disallowed() {
    let goals = make_goals(1);
    let config = default_config(); // sorry not allowed
    let tactics = vec![TacticCommand::Sorry];
    let result = interpret_tactic_block(goals, &tactics, &config);
    assert!(result.is_err(), "sorry should fail when disallowed");
}

#[test]
fn test_interpret_sorry_allowed() {
    let goals = make_goals(1);
    let config = sorry_config();
    let tactics = vec![TacticCommand::Sorry];
    let result = interpret_tactic_block(goals, &tactics, &config)
        .expect("sorry should succeed when allowed");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_try_swallows_failure() {
    let goals = make_goals(1);
    let config = default_config();
    // Try sorry (which fails since sorry is not allowed) should not propagate.
    let tactics = vec![TacticCommand::Try(Box::new(TacticCommand::Sorry))];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("try should swallow sorry failure");
    assert_eq!(result.remaining_goals.len(), 1, "goals should be restored");
}

#[test]
fn test_interpret_try_success_preserves_change() {
    let goals = make_goals(1);
    let config = default_config();
    let tactics = vec![TacticCommand::Try(Box::new(TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }))];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("try with success");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_repeat_closes_goals() {
    let goals = make_goals(3);
    let config = default_config();
    let tactics = vec![TacticCommand::Repeat(Box::new(TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }))];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("repeat should close goals");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_repeat_stops_on_failure() {
    let goals = make_goals(2);
    let config = default_config();
    let tactics = vec![
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Repeat(Box::new(TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        })),
    ];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("should succeed");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_focus_on_goal() {
    let goals = make_goals(2);
    let config = default_config();
    // Focus on goal 1 (second goal), close it.
    let tactics = vec![TacticCommand::Focus(
        1,
        Box::new(TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        }),
    )];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("focus should succeed");
    // One goal remains (the original goal 0).
    assert_eq!(result.remaining_goals.len(), 1);
}

#[test]
fn test_interpret_focus_out_of_bounds() {
    let goals = make_goals(1);
    let config = default_config();
    let tactics = vec![TacticCommand::Focus(
        5,
        Box::new(TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        }),
    )];
    let result = interpret_tactic_block(goals, &tactics, &config);
    assert!(result.is_err(), "focus on out-of-bounds index should fail");
}

#[test]
fn test_interpret_all_goals() {
    let goals = make_goals(3);
    let config = default_config();
    let tactics = vec![TacticCommand::AllGoals(Box::new(TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }))];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("all_goals should succeed");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_interpret_heartbeat_overflow() {
    let goals = make_goals(1);
    let config = TacticInterpConfig {
        max_heartbeats: 1,
        ..Default::default()
    };
    // Two commands, but only 1 heartbeat allowed.
    let tactics = vec![
        TacticCommand::Named {
            name: "skip".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "skip".to_string(),
            args: vec![],
        },
    ];
    let result = interpret_tactic_block(goals, &tactics, &config);
    assert!(result.is_err(), "should exceed heartbeat budget");
}

#[test]
fn test_interpret_trace_logging() {
    let goals = make_goals(1);
    let config = trace_config();
    let tactics = vec![TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("should succeed with tracing");
    assert!(
        !result.trace_log.is_empty(),
        "trace log should have entries"
    );
    assert!(
        result.trace_log.iter().any(|e| e.contains("begin")),
        "trace should contain 'begin'"
    );
}

#[test]
fn test_interpret_heartbeats_counted() {
    let goals = make_goals(2);
    let config = default_config();
    let tactics = vec![
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
    ];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("should succeed");
    assert!(
        result.heartbeats_used >= 2,
        "should use at least 2 heartbeats"
    );
}

// =========================================================================
// check_all_goals_closed tests
// =========================================================================

#[test]
fn test_check_all_goals_closed_success() {
    let result = TacticInterpResult {
        proof_term: Some(Expr::sort(Level::zero())),
        remaining_goals: Vec::new(),
        heartbeats_used: 5,
        trace_log: Vec::new(),
        heartbeat_profile: TacticHeartbeatProfile::default(),
    };
    let proof = check_all_goals_closed(&result).expect("should succeed");
    assert_eq!(proof, Expr::sort(Level::zero()));
}

#[test]
fn test_check_all_goals_closed_failure() {
    let result = TacticInterpResult {
        proof_term: None,
        remaining_goals: make_goals(1),
        heartbeats_used: 5,
        trace_log: Vec::new(),
        heartbeat_profile: TacticHeartbeatProfile::default(),
    };
    let err = check_all_goals_closed(&result);
    assert!(err.is_err(), "should fail with remaining goals");
}

#[test]
fn test_check_all_goals_closed_no_proof_term() {
    let result = TacticInterpResult {
        proof_term: None,
        remaining_goals: Vec::new(),
        heartbeats_used: 0,
        trace_log: Vec::new(),
        heartbeat_profile: TacticHeartbeatProfile::default(),
    };
    let err = check_all_goals_closed(&result);
    assert!(err.is_err(), "should fail without proof term");
}

// =========================================================================
// format_tactic_trace tests
// =========================================================================

#[test]
fn test_format_trace_empty() {
    let formatted = format_tactic_trace(&[]);
    assert_eq!(formatted, "[no trace]");
}

#[test]
fn test_format_trace_single_entry() {
    let trace = vec!["hello".to_string()];
    let formatted = format_tactic_trace(&trace);
    assert_eq!(formatted, "[0] hello");
}

#[test]
fn test_format_trace_multiple_entries() {
    let trace = vec!["alpha".to_string(), "beta".to_string(), "gamma".to_string()];
    let formatted = format_tactic_trace(&trace);
    assert!(formatted.contains("[0] alpha"));
    assert!(formatted.contains("[1] beta"));
    assert!(formatted.contains("[2] gamma"));
}

// =========================================================================
// Edge case tests
// =========================================================================

#[test]
fn test_nested_sequence_in_try() {
    let goals = make_goals(2);
    let config = default_config();
    let tactics = vec![TacticCommand::Try(Box::new(TacticCommand::Sequence(vec![
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
    ])))];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("nested try+seq");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_sorry_on_no_goals_is_noop() {
    let config = sorry_config();
    let tactics = vec![TacticCommand::Sorry];
    let result = interpret_tactic_block(Vec::new(), &tactics, &config)
        .expect("sorry on empty goals should no-op, not error");
    assert!(
        result.remaining_goals.is_empty(),
        "no goals were ever present, none should remain"
    );
}

#[test]
fn test_sorry_on_no_goals_no_allow_is_still_noop() {
    // Hardening: even without allow_sorry, an empty goal stack means the
    // early-exit short-circuits before dispatch_sorry runs, so this should
    // also no-op cleanly rather than tripping the "sorry not allowed" guard.
    let config = default_config();
    let tactics = vec![TacticCommand::Sorry];
    let result = interpret_tactic_block(Vec::new(), &tactics, &config)
        .expect("sorry on empty goals should no-op regardless of allow_sorry");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_sorry_on_nonempty_goals_without_allow_still_errors() {
    // Negative test: the new early-exit must NOT short-circuit when there
    // ARE goals — `sorry` on a real goal without `allow_sorry` must still
    // fail closed. Prevents the early-exit from masking the safety guard.
    let goals = make_goals(1);
    let config = default_config(); // allow_sorry == false
    let tactics = vec![TacticCommand::Sorry];
    let result = interpret_tactic_block(goals, &tactics, &config);
    assert!(
        result.is_err(),
        "sorry on a real goal without allow_sorry must still error, got {result:?}"
    );
}

#[test]
fn test_focus_zero_index_is_identity() {
    let goals = make_goals(2);
    let config = default_config();
    let tactics = vec![TacticCommand::Focus(
        0,
        Box::new(TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        }),
    )];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("focus 0");
    // Focus on goal 0 closes it; goal 1 remains.
    assert_eq!(result.remaining_goals.len(), 1);
}

#[test]
fn test_repeat_on_empty_goals_succeeds() {
    let config = default_config();
    let tactics = vec![TacticCommand::Repeat(Box::new(TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }))];
    let result = interpret_tactic_block(Vec::new(), &tactics, &config).expect("repeat on empty");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_all_goals_on_empty_succeeds() {
    let config = default_config();
    let tactics = vec![TacticCommand::AllGoals(Box::new(TacticCommand::Named {
        name: "exact".to_string(),
        args: vec![],
    }))];
    let result = interpret_tactic_block(Vec::new(), &tactics, &config).expect("all_goals on empty");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_multiple_sorry_closes_multiple_goals() {
    let goals = make_goals(3);
    let config = sorry_config();
    let tactics = vec![
        TacticCommand::Sorry,
        TacticCommand::Sorry,
        TacticCommand::Sorry,
    ];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("multiple sorry");
    assert!(result.remaining_goals.is_empty());
}

#[test]
fn test_early_stop_on_completion() {
    let goals = make_goals(1);
    let config = trace_config();
    // First tactic closes the goal; second should not be reached.
    let tactics = vec![
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "exact".to_string(),
            args: vec![],
        },
    ];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("early stop");
    assert!(result.remaining_goals.is_empty());
    // Only 1 dispatch + early stop trace, not 2 dispatches.
    assert!(
        result
            .trace_log
            .iter()
            .any(|e| e.contains("stopping early")),
        "should log early stop"
    );
}

#[test]
fn test_config_with_timeout() {
    let config = TacticInterpConfig {
        timeout_ms: Some(5000),
        ..Default::default()
    };
    assert_eq!(config.timeout_ms, Some(5000));
}

#[test]
fn test_named_tactic_with_args() {
    let goals = make_goals(1);
    let config = trace_config();
    let tactics = vec![TacticCommand::Named {
        name: "apply".to_string(),
        args: vec![Expr::sort(Level::zero())],
    }];
    let result = interpret_tactic_block(goals, &tactics, &config).expect("named with args");
    assert!(result.remaining_goals.is_empty());
    assert!(
        result.trace_log.iter().any(|e| e.contains("args: 1")),
        "trace should show arg count"
    );
}

// =========================================================================
// Heartbeat profiler tests (#3399)
// =========================================================================

/// Profiler off by default — the result carries an empty bucket map.
#[test]
fn test_profile_disabled_by_default_empty_buckets() {
    let goals = make_goals(1);
    let config = default_config();
    assert!(!config.profile_heartbeats);

    let tactics = vec![TacticCommand::Named {
        name: "simp".to_string(),
        args: vec![],
    }];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("simple interp should succeed");

    // With profiling disabled the bucket map is empty but totals are populated.
    assert!(
        result.heartbeat_profile.top_buckets.is_empty(),
        "top_buckets should be empty when profiling disabled, got {:?}",
        result.heartbeat_profile.top_buckets
    );
    assert!(
        result.heartbeat_profile.total >= 1,
        "total should still reflect heartbeats used"
    );
    assert_eq!(result.heartbeat_profile.limit, 200_000);
}

/// Profiler tracks per-tactic heartbeat attribution.
#[test]
fn test_profile_named_tactics_attributed_by_name() {
    let goals = make_goals(3);
    let config = TacticInterpConfig {
        profile_heartbeats: true,
        ..Default::default()
    };

    let tactics = vec![
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "cases".to_string(),
            args: vec![],
        },
    ];

    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("profiled interp should succeed");

    // Three ticks total, attributed 2 to simp and 1 to cases.
    assert_eq!(result.heartbeats_used, 3);
    assert_eq!(result.heartbeat_profile.total, 3);

    let map: std::collections::HashMap<_, _> = result
        .heartbeat_profile
        .top_buckets
        .iter()
        .cloned()
        .collect();
    assert_eq!(
        map.get("simp").copied(),
        Some(2),
        "simp should have 2 ticks"
    );
    assert_eq!(
        map.get("cases").copied(),
        Some(1),
        "cases should have 1 tick"
    );

    // Buckets are sorted descending by count, then by name.
    let first = &result.heartbeat_profile.top_buckets[0];
    assert_eq!(first.0, "simp", "hottest bucket should be first");
    assert_eq!(first.1, 2);
}

/// Profiler attributes structural combinators to stable label buckets.
#[test]
fn test_profile_structural_combinators_bucketed() {
    let goals = make_goals(1);
    let config = TacticInterpConfig {
        profile_heartbeats: true,
        allow_sorry: true,
        ..Default::default()
    };

    // try(sorry) dispatches two commands: the outer `try` and its inner `sorry`.
    let tactics = vec![TacticCommand::Try(Box::new(TacticCommand::Sorry))];
    let result =
        interpret_tactic_block(goals, &tactics, &config).expect("try(sorry) should succeed");

    let map: std::collections::HashMap<_, _> = result
        .heartbeat_profile
        .top_buckets
        .iter()
        .cloned()
        .collect();
    assert_eq!(
        map.get("try").copied(),
        Some(1),
        "try should have 1 tick, got {:?}",
        result.heartbeat_profile.top_buckets
    );
    assert_eq!(
        map.get("sorry").copied(),
        Some(1),
        "sorry should have 1 tick, got {:?}",
        result.heartbeat_profile.top_buckets
    );
}

/// Heartbeat overflow with profiling enabled includes a breakdown in the error.
///
/// This is the behavioral test required by the acceptance criteria in #3399:
/// synthesize a timeout and assert the breakdown of top consumers appears in
/// the error output.
#[test]
fn test_profile_overflow_error_includes_top_consumers_breakdown() {
    // Enough goals so a single dispatch of `simp` per goal exceeds the budget.
    let goals = make_goals(5);
    let config = TacticInterpConfig {
        max_heartbeats: 2,
        profile_heartbeats: true,
        ..Default::default()
    };

    // Sequence of three named tactics; the sequence wrapper plus the third
    // dispatch must push us over the 2-heartbeat budget so we hit the profiled
    // error path.
    let tactics = vec![TacticCommand::Sequence(vec![
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "cases".to_string(),
            args: vec![],
        },
    ])];

    let result = interpret_tactic_block(goals, &tactics, &config);
    let err = result.expect_err("overflow should produce ElabError");
    let msg = err.to_string();
    assert!(
        msg.contains("heartbeat limit exceeded"),
        "error should mention heartbeat: {msg}"
    );
    assert!(
        msg.contains("Tactic heartbeat profile"),
        "error should include profile breakdown: {msg}"
    );
    assert!(
        msg.contains("simp"),
        "error should name the hottest tactic ('simp'): {msg}"
    );
    // The percentage column and totals should be present in the breakdown.
    assert!(
        msg.contains("%)"),
        "breakdown should show percentage column: {msg}"
    );
}

/// Heartbeat overflow without profiling does NOT include a profile breakdown.
#[test]
fn test_profile_overflow_error_no_breakdown_when_disabled() {
    let goals = make_goals(5);
    let config = TacticInterpConfig {
        max_heartbeats: 1,
        profile_heartbeats: false,
        ..Default::default()
    };
    let tactics = vec![
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
        TacticCommand::Named {
            name: "simp".to_string(),
            args: vec![],
        },
    ];
    let err = interpret_tactic_block(goals, &tactics, &config).expect_err("should overflow");
    let msg = err.to_string();
    assert!(
        msg.contains("heartbeat limit exceeded"),
        "error should mention heartbeat: {msg}"
    );
    assert!(
        !msg.contains("Tactic heartbeat profile"),
        "profile should NOT be embedded when disabled: {msg}"
    );
}
