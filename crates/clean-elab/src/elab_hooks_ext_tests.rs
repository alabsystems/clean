// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended elaboration hook management module.

use std::sync::Arc;

use clean_kernel::Expr;

use crate::elab_hooks::{
    ElabHookContext, ElabHookEntry, ElabHookFn, ElabHookRegistry, ElabHookResult, ElabPhase,
};
use crate::elab_hooks_ext::*;

// ============================================================================
// PhaseFilter
// ============================================================================

#[test]
fn test_phase_filter_new_specific_phases() {
    let filter = PhaseFilter::new(&[ElabPhase::PreElaborate, ElabPhase::OnError]);
    assert!(filter.matches(&ElabPhase::PreElaborate));
    assert!(filter.matches(&ElabPhase::OnError));
    assert!(!filter.matches(&ElabPhase::PostElaborate));
    assert!(!filter.matches(&ElabPhase::PreTypeCheck));
    assert!(!filter.matches(&ElabPhase::PostTypeCheck));
    assert_eq!(filter.len(), 2);
    assert!(!filter.is_empty());
}

#[test]
fn test_phase_filter_all() {
    let filter = PhaseFilter::all();
    assert_eq!(filter.len(), 5);
    for phase in ElabPhase::ALL {
        assert!(filter.matches(phase));
    }
}

#[test]
fn test_phase_filter_none() {
    let filter = PhaseFilter::none();
    assert!(filter.is_empty());
    assert_eq!(filter.len(), 0);
    for phase in ElabPhase::ALL {
        assert!(!filter.matches(phase));
    }
}

#[test]
fn test_phase_filter_single_phase() {
    let filter = PhaseFilter::new(&[ElabPhase::PostTypeCheck]);
    assert_eq!(filter.len(), 1);
    assert!(filter.matches(&ElabPhase::PostTypeCheck));
    assert!(!filter.matches(&ElabPhase::PreElaborate));
}

#[test]
fn test_phase_filter_dedup_same_phases() {
    let filter = PhaseFilter::new(&[ElabPhase::PreElaborate, ElabPhase::PreElaborate]);
    assert_eq!(filter.len(), 1);
}

// ============================================================================
// HookCondition
// ============================================================================

#[test]
fn test_condition_name_contains_match() {
    let cond = HookCondition::NameContains("Nat".to_owned());
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_decl_name("Nat.add");
    assert!(cond.evaluate(&ctx));
}

#[test]
fn test_condition_name_contains_no_match() {
    let cond = HookCondition::NameContains("Nat".to_owned());
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_decl_name("Int.sub");
    assert!(!cond.evaluate(&ctx));
}

#[test]
fn test_condition_name_contains_no_decl_name() {
    let cond = HookCondition::NameContains("foo".to_owned());
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(!cond.evaluate(&ctx));
}

#[test]
fn test_condition_phase_is_match() {
    let cond = HookCondition::PhaseIs(ElabPhase::OnError);
    let ctx = ElabHookContext::new(ElabPhase::OnError);
    assert!(cond.evaluate(&ctx));
}

#[test]
fn test_condition_phase_is_no_match() {
    let cond = HookCondition::PhaseIs(ElabPhase::OnError);
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(!cond.evaluate(&ctx));
}

#[test]
fn test_condition_has_expr_true() {
    let cond = HookCondition::HasExpr;
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_expr(Expr::prop());
    assert!(cond.evaluate(&ctx));
}

#[test]
fn test_condition_has_expr_false() {
    let cond = HookCondition::HasExpr;
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(!cond.evaluate(&ctx));
}

#[test]
fn test_condition_has_expected_type_true() {
    let cond = HookCondition::HasExpectedType;
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_expected_type(Expr::type_());
    assert!(cond.evaluate(&ctx));
}

#[test]
fn test_condition_has_expected_type_false() {
    let cond = HookCondition::HasExpectedType;
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(!cond.evaluate(&ctx));
}

#[test]
fn test_condition_custom_predicate() {
    let cond = HookCondition::Custom(Arc::new(|ctx| ctx.source_span.is_some()));
    let ctx_with = ElabHookContext::new(ElabPhase::PreElaborate).with_source_span(0, 10);
    let ctx_without = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(cond.evaluate(&ctx_with));
    assert!(!cond.evaluate(&ctx_without));
}

#[test]
fn test_condition_debug_formatting() {
    assert!(format!("{:?}", HookCondition::HasExpr).contains("HasExpr"));
    assert!(format!("{:?}", HookCondition::NameContains("x".into())).contains("NameContains"));
    assert!(format!("{:?}", HookCondition::PhaseIs(ElabPhase::OnError)).contains("PhaseIs"));
    assert!(format!("{:?}", HookCondition::HasExpectedType).contains("HasExpectedType"));
    let custom = HookCondition::Custom(Arc::new(|_| true));
    assert!(format!("{custom:?}").contains("Custom"));
}

// ============================================================================
// ConditionalHook
// ============================================================================

#[test]
fn test_conditional_hook_fires_when_met() {
    let inner: ElabHookFn = Arc::new(|_| ElabHookResult::Replace(Expr::prop()));
    let ch = ConditionalHook::new(HookCondition::HasExpr, inner);
    let hook_fn = ch.into_hook_fn();
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_expr(Expr::type_());
    assert!(matches!(hook_fn(&ctx), ElabHookResult::Replace(_)));
}

#[test]
fn test_conditional_hook_skips_when_unmet() {
    let inner: ElabHookFn = Arc::new(|_| ElabHookResult::Error("fail".to_owned()));
    let ch = ConditionalHook::new(HookCondition::HasExpr, inner);
    let hook_fn = ch.into_hook_fn();
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate); // no expr
    assert!(matches!(hook_fn(&ctx), ElabHookResult::Continue));
}

#[test]
fn test_conditional_hook_debug() {
    let ch = ConditionalHook::new(
        HookCondition::HasExpr,
        Arc::new(|_| ElabHookResult::Continue),
    );
    let dbg = format!("{ch:?}");
    assert!(dbg.contains("ConditionalHook"));
    assert!(dbg.contains("HasExpr"));
}

// ============================================================================
// HookStats / HookStatsCollector
// ============================================================================

#[test]
fn test_hook_stats_default_values() {
    let stats = HookStats::default();
    assert_eq!(stats.invocations, 0);
    assert_eq!(stats.successes, 0);
    assert_eq!(stats.failures, 0);
    assert_eq!(stats.skips, 0);
    assert_eq!(stats.total_duration, std::time::Duration::ZERO);
}

#[test]
fn test_hook_stats_success_rate_zero_invocations() {
    let stats = HookStats::default();
    assert!((stats.success_rate() - 0.0).abs() < f64::EPSILON);
}

#[test]
fn test_hook_stats_success_rate_all_success() {
    let stats = HookStats {
        invocations: 10,
        successes: 10,
        ..Default::default()
    };
    assert!((stats.success_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_hook_stats_success_rate_partial() {
    let stats = HookStats {
        invocations: 4,
        successes: 3,
        failures: 1,
        ..Default::default()
    };
    assert!((stats.success_rate() - 0.75).abs() < f64::EPSILON);
}

#[test]
fn test_hook_stats_avg_duration_zero() {
    let stats = HookStats::default();
    assert_eq!(stats.avg_duration(), std::time::Duration::ZERO);
}

#[test]
fn test_hook_stats_avg_duration_computed() {
    let stats = HookStats {
        invocations: 2,
        total_duration: std::time::Duration::from_millis(100),
        ..Default::default()
    };
    assert_eq!(stats.avg_duration(), std::time::Duration::from_millis(50));
}

#[test]
fn test_stats_collector_record_and_get() {
    let mut collector = HookStatsCollector::new();
    collector.record(
        "h1",
        &ElabHookResult::Continue,
        std::time::Duration::from_millis(1),
    );
    collector.record(
        "h1",
        &ElabHookResult::Error("x".into()),
        std::time::Duration::from_millis(2),
    );
    collector.record(
        "h1",
        &ElabHookResult::Skip,
        std::time::Duration::from_millis(3),
    );

    let s = collector.get("h1").expect("should have stats");
    assert_eq!(s.invocations, 3);
    assert_eq!(s.successes, 1);
    assert_eq!(s.failures, 1);
    assert_eq!(s.skips, 1);
    assert_eq!(s.total_duration, std::time::Duration::from_millis(6));
}

#[test]
fn test_stats_collector_replace_counted_as_success() {
    let mut collector = HookStatsCollector::new();
    collector.record(
        "h",
        &ElabHookResult::Replace(Expr::prop()),
        std::time::Duration::ZERO,
    );
    let s = collector.get("h").unwrap();
    assert_eq!(s.successes, 1);
}

#[test]
fn test_stats_collector_hook_count_and_clear() {
    let mut collector = HookStatsCollector::new();
    collector.record("a", &ElabHookResult::Continue, std::time::Duration::ZERO);
    collector.record("b", &ElabHookResult::Continue, std::time::Duration::ZERO);
    assert_eq!(collector.hook_count(), 2);
    collector.clear();
    assert_eq!(collector.hook_count(), 0);
    assert!(collector.get("a").is_none());
}

#[test]
fn test_stats_collector_iter() {
    let mut collector = HookStatsCollector::new();
    collector.record("x", &ElabHookResult::Continue, std::time::Duration::ZERO);
    collector.record("y", &ElabHookResult::Continue, std::time::Duration::ZERO);
    let names: Vec<&str> = collector.iter().map(|(n, _)| n).collect();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"x"));
    assert!(names.contains(&"y"));
}

// ============================================================================
// HookChain
// ============================================================================

fn make_entry(name: &str, phase: ElabPhase, priority: u32, hook: ElabHookFn) -> ElabHookEntry {
    ElabHookEntry {
        name: name.to_owned(),
        phase,
        priority,
        hook,
    }
}

#[test]
fn test_chain_new_is_empty() {
    let chain = HookChain::new();
    assert!(chain.is_empty());
    assert_eq!(chain.len(), 0);
}

#[test]
fn test_chain_push_maintains_priority_order() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "c",
        ElabPhase::PreElaborate,
        300,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    chain.push(make_entry(
        "a",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    chain.push(make_entry(
        "b",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    assert_eq!(chain.names(), vec!["a", "b", "c"]);
}

#[test]
fn test_chain_run_empty_returns_error() {
    let chain = HookChain::new();
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = chain.run(&ctx, None);
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), HookExtError::EmptyChain));
}

#[test]
fn test_chain_run_all_continue() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "a",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    chain.push(make_entry(
        "b",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = chain.run(&ctx, None).unwrap();
    assert!(matches!(result, ElabHookResult::Continue));
}

#[test]
fn test_chain_run_early_exit_on_error() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "fail",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Error("boom".into())),
    ));
    chain.push(make_entry(
        "never",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Replace(Expr::prop())),
    ));
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = chain.run(&ctx, None).unwrap();
    assert!(matches!(result, ElabHookResult::Error(ref m) if m == "boom"));
}

#[test]
fn test_chain_run_early_exit_on_replace() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "rep",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Replace(Expr::type_())),
    ));
    chain.push(make_entry(
        "never",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Error("should not reach".into())),
    ));
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = chain.run(&ctx, None).unwrap();
    assert!(matches!(result, ElabHookResult::Replace(_)));
}

#[test]
fn test_chain_run_skip_converts_to_continue() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "skip",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Skip),
    ));
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = chain.run(&ctx, None).unwrap();
    assert!(matches!(result, ElabHookResult::Continue));
}

#[test]
fn test_chain_run_with_stats_collection() {
    let mut chain = HookChain::new();
    chain.push(make_entry(
        "a",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    chain.push(make_entry(
        "b",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let mut stats = HookStatsCollector::new();
    chain.run(&ctx, Some(&mut stats)).unwrap();
    assert_eq!(stats.hook_count(), 2);
    assert_eq!(stats.get("a").unwrap().invocations, 1);
    assert_eq!(stats.get("b").unwrap().invocations, 1);
}

// ============================================================================
// HookGroup
// ============================================================================

#[test]
fn test_group_new_is_enabled() {
    let group = HookGroup::new("my_group", vec!["h1".into(), "h2".into()]);
    assert!(group.enabled);
    assert_eq!(group.len(), 2);
    assert!(!group.is_empty());
    assert_eq!(group.name, "my_group");
}

#[test]
fn test_group_empty() {
    let group = HookGroup::new("empty", vec![]);
    assert!(group.is_empty());
    assert_eq!(group.len(), 0);
}

#[test]
fn test_group_disable_removes_hooks() {
    let mut registry = ElabHookRegistry::new();
    registry.register(make_entry(
        "h1",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    registry.register(make_entry(
        "h2",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    registry.register(make_entry(
        "h3",
        ElabPhase::PreElaborate,
        300,
        Arc::new(|_| ElabHookResult::Continue),
    ));

    let mut group = HookGroup::new("test", vec!["h1".into(), "h2".into()]);
    group.disable(&mut registry);
    assert!(!group.enabled);
    assert_eq!(registry.hook_count(), 1); // only h3 remains
}

#[test]
fn test_group_enable_re_registers_hooks() {
    let mut registry = ElabHookRegistry::new();
    let entries = vec![
        make_entry(
            "h1",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "h2",
            ElabPhase::PostElaborate,
            200,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let mut group = HookGroup::new("test", vec!["h1".into(), "h2".into()]);
    group.enabled = false;
    group.enable(&mut registry, &entries);
    assert!(group.enabled);
    assert_eq!(registry.hook_count(), 2);
}

// ============================================================================
// DiagnosticCollector
// ============================================================================

#[test]
fn test_diagnostic_collector_new_is_empty() {
    let dc = DiagnosticCollector::new();
    assert!(dc.is_empty());
    assert_eq!(dc.len(), 0);
    assert!(dc.entries().is_empty());
}

#[test]
fn test_diagnostic_collector_push_and_query() {
    let mut dc = DiagnosticCollector::new();
    dc.push(DiagnosticEntry {
        hook_name: "diag1".into(),
        phase: ElabPhase::PreElaborate,
        message: "checked pre".into(),
        decl_name: Some("foo".into()),
    });
    dc.push(DiagnosticEntry {
        hook_name: "diag2".into(),
        phase: ElabPhase::OnError,
        message: "error hit".into(),
        decl_name: None,
    });
    assert_eq!(dc.len(), 2);
    assert_eq!(dc.entries_for_phase(&ElabPhase::PreElaborate).len(), 1);
    assert_eq!(dc.entries_for_phase(&ElabPhase::OnError).len(), 1);
    assert_eq!(dc.entries_for_phase(&ElabPhase::PostElaborate).len(), 0);
}

#[test]
fn test_diagnostic_collector_clear() {
    let mut dc = DiagnosticCollector::new();
    dc.push(DiagnosticEntry {
        hook_name: "x".into(),
        phase: ElabPhase::PreElaborate,
        message: "m".into(),
        decl_name: None,
    });
    dc.clear();
    assert!(dc.is_empty());
}

#[test]
fn test_make_diagnostic_hook_records_entry() {
    let collector = Arc::new(std::sync::Mutex::new(DiagnosticCollector::new()));
    let hook_fn = make_diagnostic_hook(
        "test_diag",
        Arc::new(|ctx| format!("phase={:?}", ctx.phase)),
        Arc::clone(&collector),
    );
    let ctx = ElabHookContext::new(ElabPhase::PostTypeCheck).with_decl_name("my_thm");
    let result = hook_fn(&ctx);
    assert!(matches!(result, ElabHookResult::Continue));
    let coll = collector.lock().unwrap();
    assert_eq!(coll.len(), 1);
    let entry = &coll.entries()[0];
    assert_eq!(entry.hook_name, "test_diag");
    assert_eq!(entry.phase, ElabPhase::PostTypeCheck);
    assert!(entry.message.contains("PostTypeCheck"));
    assert_eq!(entry.decl_name.as_deref(), Some("my_thm"));
}

// ============================================================================
// Validation
// ============================================================================

#[test]
fn test_validate_entries_clean() {
    let entries = vec![
        make_entry(
            "a",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "b",
            ElabPhase::PostElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "c",
            ElabPhase::PreTypeCheck,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "d",
            ElabPhase::PostTypeCheck,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "e",
            ElabPhase::OnError,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let findings = validate_entries(&entries);
    // No duplicate names, no duplicate priorities in same phase, all phases covered
    assert!(
        !findings
            .iter()
            .all(|f| f.kind == ValidationFindingKind::EmptyPhase)
            || findings.is_empty(),
        "expected no findings for clean entries, got: {findings:?}"
    );
    assert!(findings.is_empty());
}

#[test]
fn test_validate_entries_duplicate_name() {
    let entries = vec![
        make_entry(
            "dup",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "dup",
            ElabPhase::PostElaborate,
            200,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let findings = validate_entries(&entries);
    assert!(findings
        .iter()
        .any(|f| f.kind == ValidationFindingKind::DuplicateName));
}

#[test]
fn test_validate_entries_duplicate_priority_same_phase() {
    let entries = vec![
        make_entry(
            "a",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "b",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let findings = validate_entries(&entries);
    assert!(findings
        .iter()
        .any(|f| f.kind == ValidationFindingKind::DuplicatePriority));
}

#[test]
fn test_validate_entries_same_priority_different_phases_ok() {
    let entries = vec![
        make_entry(
            "a",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "b",
            ElabPhase::PostElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let findings = validate_entries(&entries);
    // No DuplicatePriority finding (same priority but different phases is fine)
    assert!(!findings
        .iter()
        .any(|f| f.kind == ValidationFindingKind::DuplicatePriority));
}

#[test]
fn test_validate_entries_missing_phases() {
    let entries = vec![make_entry(
        "a",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    )];
    let findings = validate_entries(&entries);
    let empty_count = findings
        .iter()
        .filter(|f| f.kind == ValidationFindingKind::EmptyPhase)
        .count();
    assert_eq!(empty_count, 4); // 5 phases - 1 covered = 4 empty
}

#[test]
fn test_validate_entries_empty_input() {
    let findings = validate_entries(&[]);
    let empty_count = findings
        .iter()
        .filter(|f| f.kind == ValidationFindingKind::EmptyPhase)
        .count();
    assert_eq!(empty_count, 5);
}

// ============================================================================
// register_validated
// ============================================================================

#[test]
fn test_register_validated_success() {
    let mut registry = ElabHookRegistry::new();
    let entries = vec![
        make_entry(
            "a",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "b",
            ElabPhase::PostElaborate,
            200,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    register_validated(&mut registry, entries).expect("should succeed");
    assert_eq!(registry.hook_count(), 2);
}

#[test]
fn test_register_validated_rejects_duplicate() {
    let mut registry = ElabHookRegistry::new();
    let entries = vec![
        make_entry(
            "dup",
            ElabPhase::PreElaborate,
            100,
            Arc::new(|_| ElabHookResult::Continue),
        ),
        make_entry(
            "dup",
            ElabPhase::PostElaborate,
            200,
            Arc::new(|_| ElabHookResult::Continue),
        ),
    ];
    let err = register_validated(&mut registry, entries).unwrap_err();
    assert!(matches!(err, HookExtError::DuplicateName(ref n) if n == "dup"));
}

// ============================================================================
// run_hooks_with_stats
// ============================================================================

#[test]
fn test_run_hooks_with_stats_collects() {
    let mut registry = ElabHookRegistry::new();
    registry.register(make_entry(
        "s1",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    registry.register(make_entry(
        "s2",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Continue),
    ));

    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let mut stats = HookStatsCollector::new();
    let result = run_hooks_with_stats(&registry, ElabPhase::PreElaborate, &ctx, &mut stats);
    assert!(matches!(result, ElabHookResult::Continue));
    assert_eq!(stats.hook_count(), 2);
}

#[test]
fn test_run_hooks_with_stats_early_exit_records_partial() {
    let mut registry = ElabHookRegistry::new();
    registry.register(make_entry(
        "ok",
        ElabPhase::PreElaborate,
        100,
        Arc::new(|_| ElabHookResult::Continue),
    ));
    registry.register(make_entry(
        "fail",
        ElabPhase::PreElaborate,
        200,
        Arc::new(|_| ElabHookResult::Error("stop".into())),
    ));
    registry.register(make_entry(
        "never",
        ElabPhase::PreElaborate,
        300,
        Arc::new(|_| ElabHookResult::Continue),
    ));

    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let mut stats = HookStatsCollector::new();
    let result = run_hooks_with_stats(&registry, ElabPhase::PreElaborate, &ctx, &mut stats);
    assert!(matches!(result, ElabHookResult::Error(_)));
    assert_eq!(stats.hook_count(), 2); // "ok" and "fail", not "never"
    assert!(stats.get("never").is_none());
}

// ============================================================================
// HookExtError display
// ============================================================================

#[test]
fn test_hook_ext_error_display() {
    let e1 = HookExtError::DuplicateName("foo".into());
    assert!(e1.to_string().contains("duplicate hook name: foo"));

    let e2 = HookExtError::EmptyChain;
    assert!(e2.to_string().contains("empty hook chain"));

    let e3 = HookExtError::HookNotFound("bar".into());
    assert!(e3.to_string().contains("hook not found: bar"));

    let e4 = HookExtError::DuplicatePriority {
        phase: ElabPhase::PreElaborate,
        priority: 100,
        first: "a".into(),
        second: "b".into(),
    };
    let msg = e4.to_string();
    assert!(msg.contains("100"));
    assert!(msg.contains("PreElaborate"));
}
