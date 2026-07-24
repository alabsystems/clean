// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended optimization analysis and orchestration.
//!
//! Part of #3082 - Compiler optimization extensions.

use std::time::Duration;

use clean_kernel::{BigNat, Expr, FVarId, Literal, Name};

use crate::lcnf::{
    Alt, Arg, Cases, Code, Decl, DeclValue, ExternAttr, FunDecl, LetDecl, LetValue, Param,
};
use crate::opt::OptConfig;
use crate::opt_ext::{
    batch_code_size, check_pass_order, count_code_nodes, decl_code_size, detect_fixpoint,
    detect_fixpoint_batch, generate_report, known_pass_dependencies, ExtOptConfig, IrSizeTracker,
    IterationResult, OptExtError, OptPassId, OptimizationStats, PassAggregateStats, PassConfig,
    PassDependency, PassProfile,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn fvar(n: u64) -> FVarId {
    FVarId::new(n)
}

fn nat_type() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn simple_return_code() -> Code {
    Code::Return(fvar(0))
}

fn let_return_code() -> Code {
    let decl = LetDecl::new(
        fvar(1),
        Name::from_string("x"),
        nat_type(),
        LetValue::nat(42),
    );
    Code::let_bind(decl, Code::Return(fvar(1)))
}

fn nested_let_code() -> Code {
    let d1 = LetDecl::new(
        fvar(1),
        Name::from_string("a"),
        nat_type(),
        LetValue::nat(1),
    );
    let d2 = LetDecl::new(
        fvar(2),
        Name::from_string("b"),
        nat_type(),
        LetValue::nat(2),
    );
    let d3 = LetDecl::new(
        fvar(3),
        Name::from_string("c"),
        nat_type(),
        LetValue::Const {
            name: Name::from_string("Nat.add"),
            levels: vec![],
            args: vec![Arg::FVar(fvar(1)), Arg::FVar(fvar(2))],
        },
    );
    Code::let_bind(
        d1,
        Code::let_bind(d2, Code::let_bind(d3, Code::Return(fvar(3)))),
    )
}

fn cases_code() -> Code {
    let alt1 = Alt::ctor(Name::from_string("Nat.zero"), vec![], Code::Return(fvar(0)));
    let alt2 = Alt::default(Code::Return(fvar(1)));
    Code::Cases(Cases::new(
        Name::from_string("Nat"),
        nat_type(),
        fvar(0),
        vec![alt1, alt2],
    ))
}

fn make_decl(name: &str, code: Code) -> Decl {
    Decl::new(
        Name::from_string(name),
        vec![],
        nat_type(),
        vec![],
        code,
        false,
    )
}

fn make_extern_decl(name: &str) -> Decl {
    Decl {
        name: Name::from_string(name),
        level_params: vec![],
        ty: nat_type(),
        params: vec![],
        body: DeclValue::Extern(ExternAttr { entries: vec![] }),
        recursive: false,
    }
}

// ---------------------------------------------------------------------------
// OptPassId tests
// ---------------------------------------------------------------------------

#[test]
fn test_opt_pass_id_name_roundtrip() {
    for &id in OptPassId::all() {
        assert!(!id.name().is_empty(), "pass {:?} has empty name", id);
    }
}

#[test]
fn test_opt_pass_id_all_contains_all_variants() {
    let all = OptPassId::all();
    assert_eq!(all.len(), 10);
}

#[test]
fn test_opt_pass_id_iterative_subset() {
    let iter = OptPassId::iterative_passes();
    assert_eq!(iter.len(), 5);
    for &id in iter {
        assert!(OptPassId::all().contains(&id));
    }
}

#[test]
fn test_opt_pass_id_batch_subset() {
    let batch = OptPassId::batch_passes();
    assert_eq!(batch.len(), 4);
    for &id in batch {
        assert!(OptPassId::all().contains(&id));
    }
}

#[test]
fn test_opt_pass_id_finalization_subset() {
    let fin = OptPassId::finalization_passes();
    assert_eq!(fin.len(), 1);
    assert_eq!(fin[0], OptPassId::JoinPoints);
}

#[test]
fn test_opt_pass_id_names_unique() {
    let names: Vec<&str> = OptPassId::all().iter().map(|id| id.name()).collect();
    let mut deduped = names.clone();
    deduped.sort();
    deduped.dedup();
    assert_eq!(names.len(), deduped.len(), "duplicate pass names");
}

// ---------------------------------------------------------------------------
// count_code_nodes tests
// ---------------------------------------------------------------------------

#[test]
fn test_count_code_nodes_return() {
    assert_eq!(count_code_nodes(&simple_return_code()), 1);
}

#[test]
fn test_count_code_nodes_unreachable() {
    let code = Code::Unreachable(nat_type());
    assert_eq!(count_code_nodes(&code), 1);
}

#[test]
fn test_count_code_nodes_let_return() {
    // let x = 42; return x  =>  1 (let) + 1 (lit value) + 1 (return) = 3
    let size = count_code_nodes(&let_return_code());
    assert_eq!(size, 3);
}

#[test]
fn test_count_code_nodes_nested_lets() {
    let size = count_code_nodes(&nested_let_code());
    // 3 lets + 3 values (1 + 1 + 3 [1 + 2 args]) + 1 return = 9
    assert_eq!(size, 9);
}

#[test]
fn test_count_code_nodes_jmp() {
    let code = Code::Jmp {
        jp: fvar(0),
        args: vec![Arg::FVar(fvar(1)), Arg::Erased],
    };
    // 1 + 2 args = 3
    assert_eq!(count_code_nodes(&code), 3);
}

#[test]
fn test_count_code_nodes_cases() {
    let size = count_code_nodes(&cases_code());
    // 1 (cases) + 1 (return in alt1) + 1 (return in alt2) = 3
    assert_eq!(size, 3);
}

#[test]
fn test_count_code_nodes_fun() {
    let fun_decl = FunDecl::new(
        fvar(10),
        Name::from_string("f"),
        vec![],
        nat_type(),
        Code::Return(fvar(0)),
    );
    let code = Code::fun(fun_decl, Code::Return(fvar(1)));
    // 1 (fun) + 1 (return in fun body) + 1 (return in rest) = 3
    assert_eq!(count_code_nodes(&code), 3);
}

#[test]
fn test_count_code_nodes_join_point() {
    let jp_decl = FunDecl::new(
        fvar(10),
        Name::from_string("jp"),
        vec![],
        nat_type(),
        Code::Return(fvar(0)),
    );
    let code = Code::JoinPoint(jp_decl, Box::new(Code::Return(fvar(1))));
    assert_eq!(count_code_nodes(&code), 3);
}

// ---------------------------------------------------------------------------
// decl_code_size / batch_code_size tests
// ---------------------------------------------------------------------------

#[test]
fn test_decl_code_size_code() {
    let decl = make_decl("f", let_return_code());
    assert_eq!(decl_code_size(&decl), 3);
}

#[test]
fn test_decl_code_size_extern() {
    let decl = make_extern_decl("ext");
    assert_eq!(decl_code_size(&decl), 0);
}

#[test]
fn test_batch_code_size_empty() {
    assert_eq!(batch_code_size(&[]), 0);
}

#[test]
fn test_batch_code_size_multiple() {
    let decls = vec![
        make_decl("a", simple_return_code()),
        make_decl("b", let_return_code()),
    ];
    // 1 + 3 = 4
    assert_eq!(batch_code_size(&decls), 4);
}

// ---------------------------------------------------------------------------
// Fixed-point detection tests
// ---------------------------------------------------------------------------

#[test]
fn test_detect_fixpoint_identical() {
    let code = let_return_code();
    assert!(detect_fixpoint(&code, &code));
}

#[test]
fn test_detect_fixpoint_different() {
    let before = let_return_code();
    let after = simple_return_code();
    assert!(!detect_fixpoint(&before, &after));
}

#[test]
fn test_detect_fixpoint_batch_identical() {
    let decls = vec![make_decl("f", let_return_code())];
    assert!(detect_fixpoint_batch(&decls, &decls));
}

#[test]
fn test_detect_fixpoint_batch_different_length() {
    let a = vec![make_decl("f", simple_return_code())];
    let b = vec![
        make_decl("f", simple_return_code()),
        make_decl("g", simple_return_code()),
    ];
    assert!(!detect_fixpoint_batch(&a, &b));
}

#[test]
fn test_detect_fixpoint_batch_different_content() {
    let a = vec![make_decl("f", simple_return_code())];
    let b = vec![make_decl("f", let_return_code())];
    assert!(!detect_fixpoint_batch(&a, &b));
}

#[test]
fn test_detect_fixpoint_batch_empty() {
    let empty: Vec<Decl> = vec![];
    assert!(detect_fixpoint_batch(&empty, &empty));
}

// ---------------------------------------------------------------------------
// Pass ordering analysis tests
// ---------------------------------------------------------------------------

#[test]
fn test_known_pass_dependencies_nonempty() {
    let deps = known_pass_dependencies();
    assert!(!deps.is_empty());
}

#[test]
fn test_check_pass_order_default_is_valid() {
    let order: Vec<OptPassId> = OptPassId::iterative_passes().to_vec();
    let violations = check_pass_order(&order);
    assert!(
        violations.is_empty(),
        "default order has violations: {:?}",
        violations
    );
}

#[test]
fn test_check_pass_order_reversed_detects_violation() {
    let mut order: Vec<OptPassId> = OptPassId::iterative_passes().to_vec();
    order.reverse();
    let violations = check_pass_order(&order);
    assert!(
        !violations.is_empty(),
        "reversed order should have violations"
    );
}

#[test]
fn test_check_pass_order_empty_is_valid() {
    let violations = check_pass_order(&[]);
    assert!(violations.is_empty());
}

#[test]
fn test_check_pass_order_single_pass_is_valid() {
    let violations = check_pass_order(&[OptPassId::Dce]);
    assert!(violations.is_empty());
}

#[test]
fn test_pass_dependency_reason_nonempty() {
    for dep in known_pass_dependencies() {
        assert!(
            !dep.reason.is_empty(),
            "{:?} -> {:?} has no reason",
            dep.before,
            dep.after
        );
    }
}

// ---------------------------------------------------------------------------
// PassProfile tests
// ---------------------------------------------------------------------------

#[test]
fn test_pass_profile_size_delta_shrink() {
    let p = PassProfile {
        ir_size_before: 100,
        ir_size_after: 80,
        ..Default::default()
    };
    assert_eq!(p.size_delta(), -20);
    assert!(p.shrank());
}

#[test]
fn test_pass_profile_size_delta_grow() {
    let p = PassProfile {
        ir_size_before: 50,
        ir_size_after: 70,
        ..Default::default()
    };
    assert_eq!(p.size_delta(), 20);
    assert!(!p.shrank());
}

#[test]
fn test_pass_profile_size_delta_unchanged() {
    let p = PassProfile {
        ir_size_before: 50,
        ir_size_after: 50,
        ..Default::default()
    };
    assert_eq!(p.size_delta(), 0);
    assert!(!p.shrank());
}

// ---------------------------------------------------------------------------
// OptimizationStats tests
// ---------------------------------------------------------------------------

#[test]
fn test_stats_aggregate_by_pass_empty() {
    let stats = OptimizationStats::default();
    let agg = stats.aggregate_by_pass();
    assert!(agg.is_empty());
}

#[test]
fn test_stats_aggregate_by_pass_single() {
    let mut stats = OptimizationStats::default();
    stats.profiles.push((
        OptPassId::Dce,
        PassProfile {
            duration: Duration::from_micros(100),
            ir_size_before: 50,
            ir_size_after: 40,
            changed: true,
        },
    ));
    let agg = stats.aggregate_by_pass();
    let dce = agg.get(&OptPassId::Dce).expect("dce stats");
    assert_eq!(dce.invocations, 1);
    assert_eq!(dce.times_changed, 1);
    assert_eq!(dce.times_shrank, 1);
    assert_eq!(dce.total_size_delta, -10);
}

#[test]
fn test_stats_aggregate_by_pass_multiple_invocations() {
    let mut stats = OptimizationStats::default();
    stats.profiles.push((
        OptPassId::Cse,
        PassProfile {
            ir_size_before: 100,
            ir_size_after: 90,
            changed: true,
            ..Default::default()
        },
    ));
    stats.profiles.push((
        OptPassId::Cse,
        PassProfile {
            ir_size_before: 90,
            ir_size_after: 90,
            changed: false,
            ..Default::default()
        },
    ));
    let agg = stats.aggregate_by_pass();
    let cse = agg.get(&OptPassId::Cse).expect("cse stats");
    assert_eq!(cse.invocations, 2);
    assert_eq!(cse.times_changed, 1);
    assert_eq!(cse.times_shrank, 1);
    assert_eq!(cse.total_size_delta, -10);
}

#[test]
fn test_stats_total_size_delta() {
    let stats = OptimizationStats {
        initial_ir_size: 100,
        final_ir_size: 60,
        ..Default::default()
    };
    assert_eq!(stats.total_size_delta(), -40);
}

#[test]
fn test_stats_ineffective_passes_empty() {
    let stats = OptimizationStats::default();
    assert!(stats.ineffective_passes().is_empty());
}

#[test]
fn test_stats_ineffective_passes_detects_unchanged() {
    let mut stats = OptimizationStats::default();
    stats.profiles.push((
        OptPassId::Inline,
        PassProfile {
            changed: false,
            ..Default::default()
        },
    ));
    stats.profiles.push((
        OptPassId::Dce,
        PassProfile {
            changed: true,
            ..Default::default()
        },
    ));
    let ineffective = stats.ineffective_passes();
    assert_eq!(ineffective.len(), 1);
    assert_eq!(ineffective[0], OptPassId::Inline);
}

// ---------------------------------------------------------------------------
// PassConfig / ExtOptConfig tests
// ---------------------------------------------------------------------------

#[test]
fn test_pass_config_defaults() {
    let pc = PassConfig::new(OptPassId::Dce);
    assert!(pc.enabled);
    assert_eq!(pc.priority, 100);
}

#[test]
fn test_pass_config_builder() {
    let pc = PassConfig::new(OptPassId::Cse)
        .with_enabled(false)
        .with_priority(50);
    assert!(!pc.enabled);
    assert_eq!(pc.priority, 50);
}

#[test]
fn test_ext_opt_config_defaults() {
    let config = ExtOptConfig::default();
    assert!(config.is_pass_enabled(OptPassId::Dce));
    assert!(config.is_pass_enabled(OptPassId::Cse));
    assert!(config.is_pass_enabled(OptPassId::Inline));
}

#[test]
fn test_ext_opt_config_pass_override_disable() {
    let config = ExtOptConfig {
        pass_configs: vec![PassConfig::new(OptPassId::Cse).with_enabled(false)],
        ..Default::default()
    };
    assert!(!config.is_pass_enabled(OptPassId::Cse));
    assert!(config.is_pass_enabled(OptPassId::Dce));
}

#[test]
fn test_ext_opt_config_falls_back_to_base() {
    let base = OptConfig {
        enable_dce: false,
        ..OptConfig::default()
    };
    let config = ExtOptConfig {
        base,
        ..Default::default()
    };
    assert!(!config.is_pass_enabled(OptPassId::Dce));
}

#[test]
fn test_ext_opt_config_validate_ok() {
    let config = ExtOptConfig::default();
    assert!(config.validate().is_ok());
}

#[test]
fn test_ext_opt_config_validate_zero_priority() {
    let config = ExtOptConfig {
        pass_configs: vec![PassConfig::new(OptPassId::Dce).with_priority(0)],
        ..Default::default()
    };
    assert!(config.validate().is_err());
}

#[test]
fn test_ext_opt_config_sorted_iterative_passes_default() {
    let config = ExtOptConfig::default();
    let passes = config.sorted_iterative_passes();
    assert_eq!(passes.len(), 5);
}

#[test]
fn test_ext_opt_config_sorted_by_priority() {
    let config = ExtOptConfig {
        pass_configs: vec![
            PassConfig::new(OptPassId::Inline).with_priority(200),
            PassConfig::new(OptPassId::Dce).with_priority(50),
        ],
        ..Default::default()
    };
    let passes = config.sorted_iterative_passes();
    assert_eq!(passes[0], OptPassId::Inline);
    assert_eq!(*passes.last().expect("non-empty"), OptPassId::Dce);
}

#[test]
fn test_ext_opt_config_sorted_skips_disabled() {
    let config = ExtOptConfig {
        pass_configs: vec![PassConfig::new(OptPassId::Cse).with_enabled(false)],
        ..Default::default()
    };
    let passes = config.sorted_iterative_passes();
    assert_eq!(passes.len(), 4);
    assert!(!passes.contains(&OptPassId::Cse));
}

// ---------------------------------------------------------------------------
// IrSizeTracker tests
// ---------------------------------------------------------------------------

#[test]
fn test_tracker_empty_peak() {
    let tracker = IrSizeTracker::new();
    assert_eq!(tracker.peak_size(), 0);
}

#[test]
fn test_tracker_record_and_peak() {
    let mut tracker = IrSizeTracker::new();
    let decls_small = vec![make_decl("f", simple_return_code())];
    let decls_big = vec![make_decl("g", nested_let_code())];
    tracker.record("initial", &decls_small);
    tracker.record("after_inline", &decls_big);
    assert_eq!(tracker.peak_size(), count_code_nodes(&nested_let_code()));
}

#[test]
fn test_tracker_record_single() {
    let mut tracker = IrSizeTracker::new();
    tracker.record_single("before", &simple_return_code());
    assert_eq!(tracker.snapshots.len(), 1);
    assert_eq!(tracker.snapshots[0].total_nodes, 1);
    assert_eq!(tracker.snapshots[0].decl_count, 1);
}

#[test]
fn test_tracker_total_delta_shrink() {
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "start".into(),
        total_nodes: 100,
        decl_count: 5,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "end".into(),
        total_nodes: 70,
        decl_count: 5,
    });
    assert_eq!(tracker.total_delta(), -30);
}

#[test]
fn test_tracker_bloat_warnings_none() {
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "a".into(),
        total_nodes: 100,
        decl_count: 1,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "b".into(),
        total_nodes: 105,
        decl_count: 1,
    });
    assert!(tracker.bloat_warnings(10.0).is_empty());
}

#[test]
fn test_tracker_bloat_warnings_detected() {
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "a".into(),
        total_nodes: 100,
        decl_count: 1,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "after_inline".into(),
        total_nodes: 150,
        decl_count: 1,
    });
    let warnings = tracker.bloat_warnings(10.0);
    assert_eq!(warnings.len(), 1);
    assert_eq!(warnings[0].0, "after_inline");
    assert!((warnings[0].1 - 50.0).abs() < 0.1);
}

#[test]
fn test_tracker_bloat_from_zero_no_panic() {
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "a".into(),
        total_nodes: 0,
        decl_count: 0,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "b".into(),
        total_nodes: 50,
        decl_count: 1,
    });
    // 0 -> 50 should not panic (divide by zero guard)
    let warnings = tracker.bloat_warnings(10.0);
    assert!(warnings.is_empty()); // prev == 0 guard
}

// ---------------------------------------------------------------------------
// Report generation tests
// ---------------------------------------------------------------------------

#[test]
fn test_generate_report_empty_stats() {
    let stats = OptimizationStats::default();
    let tracker = IrSizeTracker::new();
    let report = generate_report(&stats, &tracker);
    assert!(report.contains("Optimization Report"));
    assert!(report.contains("Iterations: 0"));
}

#[test]
fn test_generate_report_with_data() {
    let mut stats = OptimizationStats {
        iterations: 3,
        reached_fixpoint: true,
        initial_ir_size: 100,
        final_ir_size: 60,
        total_duration: Duration::from_millis(5),
        ..Default::default()
    };
    stats.profiles.push((
        OptPassId::Dce,
        PassProfile {
            duration: Duration::from_micros(500),
            ir_size_before: 100,
            ir_size_after: 80,
            changed: true,
        },
    ));
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "initial".into(),
        total_nodes: 100,
        decl_count: 5,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "final".into(),
        total_nodes: 60,
        decl_count: 5,
    });

    let report = generate_report(&stats, &tracker);
    assert!(report.contains("fixpoint: yes"));
    assert!(report.contains("IR size: 100 -> 60"));
    assert!(report.contains("dce"));
    assert!(report.contains("Size Trace"));
}

#[test]
fn test_generate_report_shows_ineffective() {
    let mut stats = OptimizationStats::default();
    stats.profiles.push((
        OptPassId::Inline,
        PassProfile {
            changed: false,
            ..Default::default()
        },
    ));
    let tracker = IrSizeTracker::new();
    let report = generate_report(&stats, &tracker);
    assert!(report.contains("Ineffective passes"));
    assert!(report.contains("inline"));
}

#[test]
fn test_generate_report_shows_bloat() {
    let stats = OptimizationStats::default();
    let mut tracker = IrSizeTracker::new();
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "before".into(),
        total_nodes: 100,
        decl_count: 1,
    });
    tracker.snapshots.push(crate::opt_ext::IrSizeSnapshot {
        label: "after_inline".into(),
        total_nodes: 200,
        decl_count: 1,
    });
    let report = generate_report(&stats, &tracker);
    assert!(report.contains("Bloat Warnings"));
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[test]
fn test_count_code_nodes_deeply_nested_lets() {
    let mut code = Code::Return(fvar(100));
    for i in (0..50).rev() {
        let decl = LetDecl::new(
            fvar(i),
            Name::from_string(&format!("v{}", i)),
            nat_type(),
            LetValue::nat(i),
        );
        code = Code::let_bind(decl, code);
    }
    // 50 lets * (1 + 1 value) + 1 return = 101
    assert_eq!(count_code_nodes(&code), 101);
}

#[test]
fn test_batch_code_size_with_extern_mixed() {
    let decls = vec![
        make_decl("f", nested_let_code()),
        make_extern_decl("ext1"),
        make_decl("g", simple_return_code()),
        make_extern_decl("ext2"),
    ];
    let expected = count_code_nodes(&nested_let_code()) + 1;
    assert_eq!(batch_code_size(&decls), expected);
}

#[test]
fn test_ext_opt_config_all_passes_disabled_via_base() {
    let config = ExtOptConfig {
        base: OptConfig::minimal(),
        ..Default::default()
    };
    // Minimal only enables DCE
    assert!(config.is_pass_enabled(OptPassId::Dce));
    assert!(!config.is_pass_enabled(OptPassId::Cse));
    assert!(!config.is_pass_enabled(OptPassId::Inline));
}

#[test]
fn test_pass_priority_default_value() {
    let config = ExtOptConfig::default();
    assert_eq!(config.pass_priority(OptPassId::Dce), 100);
}
