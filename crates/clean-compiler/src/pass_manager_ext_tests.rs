// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended pass manager.
//!
//! Part of #3083 — Extensibility.

use super::pass_manager_ext::*;
use crate::ir::{IRBody, IRDecl, IRType, VarId};
use clean_kernel::Name;
use std::time::Duration;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Create a trivial IRDecl for testing.
fn test_decl(name: &str) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(crate::ir::IRArg::Var(VarId(0))),
    }
}

/// Identity pass: returns input unchanged.
fn identity_pass(name: &str, phase: ExtPhase) -> ExtPass {
    ExtPass::new(name, phase, "identity", |decls| Ok(decls.to_vec()))
}

/// Pass that appends a new decl named `<original>_<suffix>`.
fn appending_pass(name: &str, phase: ExtPhase, suffix: &'static str) -> ExtPass {
    ExtPass::new(name, phase, "appending", move |decls| {
        let mut out = decls.to_vec();
        for d in decls {
            let mut new_d = d.clone();
            new_d.name = Name::from_string(&format!("{}_{}", d.name, suffix));
            out.push(new_d);
        }
        Ok(out)
    })
}

/// Pass that removes all decls (produces empty output).
fn removing_pass(name: &str, phase: ExtPhase) -> ExtPass {
    ExtPass::new(name, phase, "removing", |_decls| Ok(Vec::new()))
}

/// Pass that always fails.
fn failing_pass(name: &str, phase: ExtPhase) -> ExtPass {
    ExtPass::new(name, phase, "failing", |_decls| {
        Err("intentional failure".into())
    })
}

// ===========================================================================
// Registration tests
// ===========================================================================

#[test]
fn test_register_single_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("inline", ExtPhase::Main))
        .expect("registration should succeed");
    assert_eq!(mgr.pass_count(), 1);
}

#[test]
fn test_register_multiple_passes() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("a", ExtPhase::Early)).unwrap();
    mgr.register(identity_pass("b", ExtPhase::Main)).unwrap();
    mgr.register(identity_pass("c", ExtPhase::Late)).unwrap();
    assert_eq!(mgr.pass_count(), 3);
}

#[test]
fn test_register_duplicate_name_fails() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("dce", ExtPhase::Late)).unwrap();
    let err = mgr
        .register(identity_pass("dce", ExtPhase::Late))
        .unwrap_err();
    match err {
        PassManagerExtError::DuplicatePass(name) => assert_eq!(name, "dce"),
        other => panic!("expected DuplicatePass, got: {other:?}"),
    }
}

#[test]
fn test_has_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("cse", ExtPhase::Main)).unwrap();
    assert!(mgr.has_pass("cse"));
    assert!(!mgr.has_pass("nonexistent"));
}

#[test]
fn test_passes_in_phase() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("a", ExtPhase::Early)).unwrap();
    mgr.register(identity_pass("b", ExtPhase::Main)).unwrap();
    mgr.register(identity_pass("c", ExtPhase::Early)).unwrap();
    let early = mgr.passes_in_phase(ExtPhase::Early);
    assert_eq!(early.len(), 2);
    assert_eq!(early[0].name, "a");
    assert_eq!(early[1].name, "c");
}

// ===========================================================================
// Enable / disable tests
// ===========================================================================

#[test]
fn test_disable_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("dce", ExtPhase::Late)).unwrap();
    assert!(mgr.is_pass_enabled("dce"));
    mgr.disable_pass("dce");
    assert!(!mgr.is_pass_enabled("dce"));
}

#[test]
fn test_enable_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("dce", ExtPhase::Late)).unwrap();
    mgr.disable_pass("dce");
    mgr.enable_pass("dce");
    assert!(mgr.is_pass_enabled("dce"));
}

#[test]
fn test_is_pass_enabled_unknown_pass() {
    let mgr = ExtPassManager::new();
    // Unknown pass is not enabled (because it does not exist).
    assert!(!mgr.is_pass_enabled("ghost"));
}

#[test]
fn test_disabled_pass_skipped_in_stats() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("skip_me", ExtPhase::Early))
        .unwrap();
    mgr.disable_pass("skip_me");

    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 1);

    let ps = stats.per_pass.get("skip_me").unwrap();
    assert_eq!(ps.skips, 1);
    assert_eq!(ps.runs, 0);
}

// ===========================================================================
// Dependency & validation tests
// ===========================================================================

#[test]
fn test_validate_missing_dependency() {
    let mut mgr = ExtPassManager::new();
    let pass = identity_pass("opt", ExtPhase::Main).depends_on("nonexistent");
    mgr.register(pass).unwrap();
    let err = mgr.validate().unwrap_err();
    match err {
        PassManagerExtError::MissingDependency { pass, dependency } => {
            assert_eq!(pass, "opt");
            assert_eq!(dependency, "nonexistent");
        }
        other => panic!("expected MissingDependency, got: {other:?}"),
    }
}

#[test]
fn test_validate_conflict_detected() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("a", ExtPhase::Main)).unwrap();
    let b = identity_pass("b", ExtPhase::Main).conflicts_with("a");
    mgr.register(b).unwrap();
    let err = mgr.validate().unwrap_err();
    match err {
        PassManagerExtError::ConflictingRequirements { a, b, .. } => {
            assert_eq!(a, "b");
            assert_eq!(b, "a");
        }
        other => panic!("expected ConflictingRequirements, got: {other:?}"),
    }
}

#[test]
fn test_validate_no_conflict_when_other_not_registered() {
    let mut mgr = ExtPassManager::new();
    let a = identity_pass("a", ExtPhase::Main).conflicts_with("ghost");
    mgr.register(a).unwrap();
    mgr.validate()
        .expect("no conflict if the other pass is absent");
}

#[test]
fn test_validate_cycle_two_nodes() {
    let mut mgr = ExtPassManager::new();
    let a = identity_pass("a", ExtPhase::Main).depends_on("b");
    let b = identity_pass("b", ExtPhase::Main).depends_on("a");
    mgr.register(a).unwrap();
    mgr.register(b).unwrap();
    let err = mgr.validate().unwrap_err();
    match err {
        PassManagerExtError::CycleDetected { cycle } => {
            assert!(cycle.contains('a'));
            assert!(cycle.contains('b'));
        }
        other => panic!("expected CycleDetected, got: {other:?}"),
    }
}

#[test]
fn test_validate_cycle_three_nodes() {
    let mut mgr = ExtPassManager::new();
    let a = identity_pass("x", ExtPhase::Main).depends_on("z");
    let b = identity_pass("y", ExtPhase::Main).depends_on("x");
    let c = identity_pass("z", ExtPhase::Main).depends_on("y");
    mgr.register(a).unwrap();
    mgr.register(b).unwrap();
    mgr.register(c).unwrap();
    let err = mgr.validate().unwrap_err();
    match err {
        PassManagerExtError::CycleDetected { .. } => {}
        other => panic!("expected CycleDetected, got: {other:?}"),
    }
}

#[test]
fn test_validate_ok_for_valid_pipeline() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("a", ExtPhase::Early)).unwrap();
    let b = identity_pass("b", ExtPhase::Main).depends_on("a");
    mgr.register(b).unwrap();
    mgr.validate().expect("should be valid");
}

// ===========================================================================
// Topological ordering tests
// ===========================================================================

#[test]
fn test_topological_order_respects_phases() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("late_pass", ExtPhase::Late))
        .unwrap();
    mgr.register(identity_pass("early_pass", ExtPhase::Early))
        .unwrap();
    let order = mgr.topological_order().unwrap();
    let early_idx = order.iter().position(|n| n == "early_pass").unwrap();
    let late_idx = order.iter().position(|n| n == "late_pass").unwrap();
    assert!(early_idx < late_idx, "early must come before late");
}

#[test]
fn test_topological_order_respects_dependencies() {
    let mut mgr = ExtPassManager::new();
    let b = identity_pass("b", ExtPhase::Main).depends_on("a");
    mgr.register(identity_pass("a", ExtPhase::Main)).unwrap();
    mgr.register(b).unwrap();
    let order = mgr.topological_order().unwrap();
    let a_idx = order.iter().position(|n| n == "a").unwrap();
    let b_idx = order.iter().position(|n| n == "b").unwrap();
    assert!(a_idx < b_idx);
}

#[test]
fn test_topological_order_deterministic() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("c", ExtPhase::Main)).unwrap();
    mgr.register(identity_pass("a", ExtPhase::Main)).unwrap();
    mgr.register(identity_pass("b", ExtPhase::Main)).unwrap();
    let order1 = mgr.topological_order().unwrap();
    let order2 = mgr.topological_order().unwrap();
    assert_eq!(order1, order2, "topological order must be deterministic");
}

#[test]
fn test_topological_order_all_four_phases() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("codegen_p", ExtPhase::Codegen))
        .unwrap();
    mgr.register(identity_pass("early_p", ExtPhase::Early))
        .unwrap();
    mgr.register(identity_pass("late_p", ExtPhase::Late))
        .unwrap();
    mgr.register(identity_pass("main_p", ExtPhase::Main))
        .unwrap();
    let order = mgr.topological_order().unwrap();
    let positions: Vec<usize> = ["early_p", "main_p", "late_p", "codegen_p"]
        .iter()
        .map(|n| order.iter().position(|o| o == n).unwrap())
        .collect();
    assert!(positions.windows(2).all(|w| w[0] < w[1]));
}

// ===========================================================================
// Execution tests
// ===========================================================================

#[test]
fn test_run_empty_pipeline() {
    let mgr = ExtPassManager::new();
    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 1);
    assert_eq!(stats.per_pass.len(), 0);
}

#[test]
fn test_run_identity_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("id", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (out, _) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].name.to_string(), "f");
}

#[test]
fn test_run_appending_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(appending_pass("dup", ExtPhase::Main, "copy"))
        .unwrap();
    let input = vec![test_decl("f")];
    let (out, _) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 2);
}

#[test]
fn test_run_removing_pass() {
    let mut mgr = ExtPassManager::new();
    mgr.register(removing_pass("dce", ExtPhase::Late)).unwrap();
    let input = vec![test_decl("f"), test_decl("g")];
    let (out, _) = mgr.run(&input).unwrap();
    assert!(out.is_empty());
}

#[test]
fn test_run_failing_pass_returns_error() {
    let mut mgr = ExtPassManager::new();
    mgr.register(failing_pass("bad", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let err = mgr.run(&input).unwrap_err();
    match err {
        PassManagerExtError::PassFailed { pass, reason } => {
            assert_eq!(pass, "bad");
            assert_eq!(reason, "intentional failure");
        }
        other => panic!("expected PassFailed, got: {other:?}"),
    }
}

#[test]
fn test_run_multi_phase_pipeline() {
    let mut mgr = ExtPassManager::new();
    mgr.register(appending_pass("early_dup", ExtPhase::Early, "e"))
        .unwrap();
    mgr.register(identity_pass("main_id", ExtPhase::Main))
        .unwrap();
    mgr.register(identity_pass("late_id", ExtPhase::Late))
        .unwrap();
    let input = vec![test_decl("f")];
    let (out, _) = mgr.run(&input).unwrap();
    // early_dup doubles: [f, f_e]. The rest are identity.
    assert_eq!(out.len(), 2);
}

#[test]
fn test_run_with_dependencies() {
    // `b` depends on `a`. Both in Main phase. Execution order: a then b.
    let mut mgr = ExtPassManager::new();
    // a appends "_a"
    mgr.register(appending_pass("a", ExtPhase::Main, "a"))
        .unwrap();
    // b appends "_b"
    let b = appending_pass("b", ExtPhase::Main, "b").depends_on("a");
    mgr.register(b).unwrap();

    let input = vec![test_decl("f")];
    let (out, _) = mgr.run(&input).unwrap();
    // After a: [f, f_a]. After b: [f, f_a, f_b, f_a_b].
    assert_eq!(out.len(), 4);
    let names: Vec<String> = out.iter().map(|d| d.name.to_string()).collect();
    assert!(names.contains(&"f".to_string()));
    assert!(names.contains(&"f_a".to_string()));
}

// ===========================================================================
// Profiling / statistics tests
// ===========================================================================

#[test]
fn test_stats_runs_counted() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("p", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (_, stats) = mgr.run(&input).unwrap();
    let ps = stats.per_pass.get("p").unwrap();
    assert!(ps.runs >= 1);
    assert_eq!(ps.skips, 0);
}

#[test]
fn test_stats_total_time_nonzero() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("p", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (_, stats) = mgr.run(&input).unwrap();
    // total_time might be very small but should be non-panicking.
    assert!(stats.total_time >= Duration::ZERO);
}

#[test]
fn test_stats_decl_counts() {
    let mut mgr = ExtPassManager::new();
    mgr.register(appending_pass("dup", ExtPhase::Main, "x"))
        .unwrap();
    let input = vec![test_decl("f")];
    let (_, stats) = mgr.run(&input).unwrap();
    let ps = stats.per_pass.get("dup").unwrap();
    assert_eq!(ps.last_decl_count_in, 1);
    assert_eq!(ps.last_decl_count_out, 2);
}

#[test]
fn test_stats_total_iterations() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("id", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (_, stats) = mgr.run(&input).unwrap();
    assert!(stats.total_iterations >= 1);
}

#[test]
fn test_profiling_disabled() {
    let config = ExtPipelineConfig {
        profiling: false,
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    mgr.register(identity_pass("p", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (_, stats) = mgr.run(&input).unwrap();
    let ps = stats.per_pass.get("p").unwrap();
    // When profiling is off, time should be zero (no measurement taken).
    assert_eq!(ps.total_time, Duration::ZERO);
}

// ===========================================================================
// Iteration / fixpoint tests
// ===========================================================================

#[test]
fn test_fixpoint_converges_immediately_for_identity() {
    let config = ExtPipelineConfig {
        max_iterations: 5,
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    mgr.register(identity_pass("id", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 1);
    // Identity converges in 1 iteration + the check iteration that sees no change.
    assert!(stats.total_iterations <= 2);
}

#[test]
fn test_max_iterations_caps_execution() {
    let config = ExtPipelineConfig {
        max_iterations: 3,
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    // This pass keeps appending, never reaches fixpoint.
    mgr.register(appending_pass("grow", ExtPhase::Main, "x").fixed_point())
        .unwrap();
    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    // After 3 iterations of doubling: 1->2->4->8
    assert_eq!(out.len(), 8);
    assert_eq!(stats.total_iterations, 3);
}

#[test]
fn test_single_shot_mode() {
    let config = ExtPipelineConfig {
        max_iterations: 0, // single shot
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    mgr.register(appending_pass("grow", ExtPhase::Main, "x"))
        .unwrap();
    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 2); // one pass application only
    assert_eq!(stats.total_iterations, 1);
}

// ===========================================================================
// Diff callback tests
// ===========================================================================

#[test]
fn test_diff_callback_invoked() {
    use std::sync::{Arc, Mutex};

    let log: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let log_clone = Arc::clone(&log);

    let config = ExtPipelineConfig {
        diff_enabled: true,
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    mgr.set_diff_callback(Box::new(move |name, before, after| {
        log_clone
            .lock()
            .unwrap()
            .push(format!("{}: {} -> {}", name, before.len(), after.len()));
    }));
    mgr.register(appending_pass("dup", ExtPhase::Main, "x"))
        .unwrap();
    let input = vec![test_decl("f")];
    mgr.run(&input).unwrap();
    let entries = log.lock().unwrap();
    assert!(!entries.is_empty());
    assert!(entries[0].starts_with("dup:"));
}

#[test]
fn test_diff_callback_not_invoked_when_disabled() {
    use std::sync::{Arc, Mutex};

    let log: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let log_clone = Arc::clone(&log);

    let config = ExtPipelineConfig {
        diff_enabled: false,
        ..Default::default()
    };
    let mut mgr = ExtPassManager::with_config(config);
    mgr.set_diff_callback(Box::new(move |name, _, _| {
        log_clone.lock().unwrap().push(name.to_owned());
    }));
    mgr.register(identity_pass("id", ExtPhase::Main)).unwrap();
    let input = vec![test_decl("f")];
    mgr.run(&input).unwrap();
    let entries = log.lock().unwrap();
    assert!(entries.is_empty());
}

// ===========================================================================
// Builder / metadata tests
// ===========================================================================

#[test]
fn test_ext_pass_builder_depends_on() {
    let p = identity_pass("b", ExtPhase::Main).depends_on("a");
    assert_eq!(p.meta.dependencies, vec!["a"]);
}

#[test]
fn test_ext_pass_builder_conflicts_with() {
    let p = identity_pass("b", ExtPhase::Main).conflicts_with("a");
    assert_eq!(p.meta.conflicts, vec!["a"]);
}

#[test]
fn test_ext_pass_builder_chaining() {
    let p = identity_pass("c", ExtPhase::Late)
        .depends_on("a")
        .depends_on("b")
        .conflicts_with("z");
    assert_eq!(p.meta.dependencies, vec!["a", "b"]);
    assert_eq!(p.meta.conflicts, vec!["z"]);
}

#[test]
fn test_pass_meta_description() {
    let p = ExtPass::new("dce", ExtPhase::Late, "dead code elimination", |d| {
        Ok(d.to_vec())
    });
    assert_eq!(p.meta.description, "dead code elimination");
}

// ===========================================================================
// Phase enum tests
// ===========================================================================

#[test]
fn test_ext_phase_ordering() {
    assert!(ExtPhase::Early < ExtPhase::Main);
    assert!(ExtPhase::Main < ExtPhase::Late);
    assert!(ExtPhase::Late < ExtPhase::Codegen);
}

#[test]
fn test_ext_phase_names() {
    assert_eq!(ExtPhase::Early.name(), "early");
    assert_eq!(ExtPhase::Main.name(), "main");
    assert_eq!(ExtPhase::Late.name(), "late");
    assert_eq!(ExtPhase::Codegen.name(), "codegen");
}

#[test]
fn test_ext_phase_display() {
    assert_eq!(format!("{}", ExtPhase::Codegen), "codegen");
}

// ===========================================================================
// Error display tests
// ===========================================================================

#[test]
fn test_error_display_missing_dependency() {
    let err = PassManagerExtError::MissingDependency {
        pass: "b".into(),
        dependency: "a".into(),
    };
    let msg = err.to_string();
    assert!(msg.contains("depends on unregistered pass"));
}

#[test]
fn test_error_display_cycle() {
    let err = PassManagerExtError::CycleDetected {
        cycle: "a -> b -> a".into(),
    };
    assert!(err.to_string().contains("cycle detected"));
}

#[test]
fn test_error_display_duplicate() {
    let err = PassManagerExtError::DuplicatePass("foo".into());
    assert!(err.to_string().contains("duplicate pass name"));
}

#[test]
fn test_error_display_pass_failed() {
    let err = PassManagerExtError::PassFailed {
        pass: "dce".into(),
        reason: "boom".into(),
    };
    assert!(err.to_string().contains("boom"));
}

#[test]
fn test_error_display_conflicting() {
    let err = PassManagerExtError::ConflictingRequirements {
        a: "x".into(),
        b: "y".into(),
        detail: "reason".into(),
    };
    assert!(err.to_string().contains("conflicting requirements"));
}

// ===========================================================================
// Edge case / integration tests
// ===========================================================================

#[test]
fn test_run_empty_input() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("id", ExtPhase::Main)).unwrap();
    let (out, _) = mgr.run(&[]).unwrap();
    assert!(out.is_empty());
}

#[test]
fn test_large_pipeline_ten_passes() {
    let mut mgr = ExtPassManager::new();
    for i in 0..10 {
        mgr.register(identity_pass(&format!("p{i}"), ExtPhase::Main))
            .unwrap();
    }
    let input = vec![test_decl("f")];
    let (out, stats) = mgr.run(&input).unwrap();
    assert_eq!(out.len(), 1);
    assert_eq!(stats.per_pass.len(), 10);
}

#[test]
fn test_pipeline_with_all_phases_populated() {
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("e1", ExtPhase::Early)).unwrap();
    mgr.register(identity_pass("e2", ExtPhase::Early)).unwrap();
    mgr.register(identity_pass("m1", ExtPhase::Main)).unwrap();
    mgr.register(identity_pass("l1", ExtPhase::Late)).unwrap();
    mgr.register(identity_pass("c1", ExtPhase::Codegen))
        .unwrap();

    let order = mgr.topological_order().unwrap();
    // Early passes before Main, Main before Late, Late before Codegen.
    let e1 = order.iter().position(|n| n == "e1").unwrap();
    let m1 = order.iter().position(|n| n == "m1").unwrap();
    let l1 = order.iter().position(|n| n == "l1").unwrap();
    let c1 = order.iter().position(|n| n == "c1").unwrap();
    assert!(e1 < m1);
    assert!(m1 < l1);
    assert!(l1 < c1);
}

#[test]
fn test_debug_impls() {
    let mgr = ExtPassManager::new();
    let debug = format!("{mgr:?}");
    assert!(debug.contains("ExtPassManager"));

    let pass = identity_pass("test", ExtPhase::Main);
    let debug = format!("{pass:?}");
    assert!(debug.contains("ExtPass"));
}

#[test]
fn test_pipeline_stats_default() {
    let stats = PipelineStats::default();
    assert_eq!(stats.total_iterations, 0);
    assert_eq!(stats.total_time, Duration::ZERO);
    assert!(stats.per_pass.is_empty());
}

#[test]
fn test_pass_stats_default() {
    let ps = PassStats::default();
    assert_eq!(ps.runs, 0);
    assert_eq!(ps.skips, 0);
    assert_eq!(ps.total_time, Duration::ZERO);
}

#[test]
fn test_config_default_values() {
    let config = ExtPipelineConfig::default();
    assert!(config.disabled_passes.is_empty());
    assert_eq!(config.max_iterations, 10);
    assert!(config.profiling);
    assert!(!config.diff_enabled);
}

#[test]
fn test_cross_phase_dependency() {
    // A pass in Late can depend on a pass in Early (within same phase would
    // already be handled by phase ordering, but explicit dep is also fine).
    let mut mgr = ExtPassManager::new();
    mgr.register(identity_pass("setup", ExtPhase::Early))
        .unwrap();
    let late = identity_pass("cleanup", ExtPhase::Late).depends_on("setup");
    mgr.register(late).unwrap();
    mgr.validate().expect("cross-phase dependency is valid");
    let order = mgr.topological_order().unwrap();
    let s = order.iter().position(|n| n == "setup").unwrap();
    let c = order.iter().position(|n| n == "cleanup").unwrap();
    assert!(s < c);
}
