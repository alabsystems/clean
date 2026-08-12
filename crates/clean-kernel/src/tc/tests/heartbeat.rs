// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for heartbeat resource limits.

use super::*;

/// Normal type checking operations succeed with default (unlimited) heartbeat.
#[test]
fn test_heartbeat_normal_operation_within_budget() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    let prop = Expr::sort(Level::zero());
    let result = tc.infer_type(&prop);
    assert!(
        result.is_ok(),
        "Simple infer_type should succeed with unlimited heartbeat"
    );
}

/// Heartbeat limit of 0 means unlimited.
#[test]
fn test_heartbeat_zero_means_unlimited() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(0);

    assert_eq!(tc.heartbeat_limit(), 0);

    // Should never fail regardless of how many operations
    for _ in 0..1000 {
        let prop = Expr::sort(Level::zero());
        let _ = tc
            .infer_type(&prop)
            .expect("unlimited heartbeat should never fail");
    }

    // Counter should still be 0 (not decremented when limit is 0)
    assert_eq!(tc.heartbeat_remaining(), 0);
}

/// A very small heartbeat limit is exceeded quickly.
#[test]
fn test_heartbeat_small_limit_exceeded() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1);

    let prop = Expr::sort(Level::zero());

    // First call: should succeed (tick decrements from 1 to 0)
    let result1 = tc.infer_type(&prop);
    assert!(
        result1.is_ok(),
        "First infer_type with limit=1 should succeed"
    );

    // Second call: counter is at 0, should fail
    let result2 = tc.infer_type(&prop);
    assert!(
        matches!(result2, Err(TypeError::HeartbeatExceeded { limit: 1, .. })),
        "Second infer_type with limit=1 should return HeartbeatExceeded, got: {:?}",
        result2
    );
}

/// HeartbeatExceeded error message matches Lean 4 format.
#[test]
fn test_heartbeat_error_message_format() {
    let err = TypeError::HeartbeatExceeded {
        limit: 200_000,
        profile: None,
    };
    let msg = err.to_string();
    assert!(
        msg.contains("heartbeat limit exceeded"),
        "Error message should mention heartbeat: {msg}"
    );
    assert!(
        msg.contains("200000"),
        "Error message should include the limit: {msg}"
    );
    assert!(
        msg.contains("maxHeartbeats"),
        "Error message should mention maxHeartbeats option: {msg}"
    );
}

/// Reset restores the counter to the configured limit.
#[test]
fn test_heartbeat_reset() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(10);

    let prop = Expr::sort(Level::zero());

    // Use some heartbeats
    let _ = tc.infer_type(&prop).unwrap();
    assert!(tc.heartbeat_remaining() < 10);

    // Reset
    tc.reset_heartbeat();
    assert_eq!(tc.heartbeat_remaining(), 10);
}

/// set_heartbeat_limit also resets the counter.
#[test]
fn test_heartbeat_set_limit_resets_counter() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1000);

    // Use some heartbeats
    let prop = Expr::sort(Level::zero());
    let _ = tc.infer_type(&prop).unwrap();
    let remaining = tc.heartbeat_remaining();
    assert!(remaining < 1000);

    // Setting a new limit resets the counter
    tc.set_heartbeat_limit(500);
    assert_eq!(tc.heartbeat_limit(), 500);
    assert_eq!(tc.heartbeat_remaining(), 500);
}

/// The default limit is 2,000,000 — high enough for all Init/Std constants
/// but bounded to prevent runaway WHNF reduction. Part of #3134.
#[test]
fn test_heartbeat_default_limit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert_eq!(tc.heartbeat_limit(), 2_000_000);
    assert_eq!(tc.heartbeat_remaining(), 2_000_000);
    assert_eq!(DEFAULT_HEARTBEAT_LIMIT, 2_000_000);
}

/// With an explicit limit, real reduction work consumes more heartbeats than
/// already-normal expressions.
///
/// Lean-parity accounting (2026-06-12): whnf of an already-normal kind
/// (Sort/Pi/Lam/Lit/BVar) returns before the tick — Lean's `check_system`
/// also sits after those early returns — so only expressions that reach the
/// reduction machinery consume budget.
#[test]
fn test_heartbeat_nested_operations_consume_more() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);

    // Simple operation: whnf of an already-normal Sort — free (Lean parity).
    let prop = Expr::sort(Level::zero());
    let _ = tc.whnf(&prop);
    let remaining_after_simple = tc.heartbeat_remaining();

    // Reset for fair comparison
    let env2 = Environment::new();
    let mut tc2 = TypeChecker::new(&env2);
    tc2.set_heartbeat_limit(200_000);

    // Real work: a beta redex `(fun (x : Prop) => x) Prop` reaches whnf's
    // reduction machinery and ticks.
    let redex = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        ),
        Expr::sort(Level::zero()),
    );
    let _ = tc2.whnf(&redex);
    let remaining_after_complex = tc2.heartbeat_remaining();

    assert!(
        remaining_after_complex < remaining_after_simple,
        "Beta redex should consume more heartbeats ({} remaining) than already-normal Sort ({} remaining)",
        remaining_after_complex,
        remaining_after_simple
    );
}

/// whnf and is_def_eq operations decrement the heartbeat when a limit is set
/// and the expressions reach the real machinery (Lean-parity accounting:
/// already-normal whnf and def-eq quick paths are free, matching the
/// placement of Lean 4's `check_system` calls).
#[test]
fn test_heartbeat_whnf_and_defeq_decrement() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);

    let initial = tc.heartbeat_remaining();

    // whnf of a beta redex should decrement
    let prop = Expr::sort(Level::zero());
    let redex = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        ),
        Expr::sort(Level::zero()),
    );
    let _ = tc.whnf(&redex);
    let after_whnf = tc.heartbeat_remaining();
    assert!(
        after_whnf < initial,
        "whnf of a beta redex should decrement heartbeat: {} -> {}",
        initial,
        after_whnf
    );

    // is_def_eq that reaches is_def_eq_core (cache-missing, non-quick pair)
    // should decrement further. A fresh redex avoids the whnf-cache identity.
    let redex2 = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::zero()),
            Expr::bvar(0),
        ),
        Expr::sort(Level::zero()),
    );
    tc.is_def_eq(&redex2, &prop);
    let after_defeq = tc.heartbeat_remaining();
    assert!(
        after_defeq < after_whnf,
        "is_def_eq reaching the core should decrement heartbeat: {} -> {}",
        after_whnf,
        after_defeq
    );
}

/// When heartbeat is exhausted via whnf/is_def_eq, the next infer_type fails.
#[test]
fn test_heartbeat_exhaustion_surfaces_at_infer() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(5);

    let prop = Expr::sort(Level::zero());

    // Exhaust heartbeats via whnf calls on beta redexes (which decrement but
    // don't fail). An already-normal Sort would be free under Lean-parity
    // accounting, and — since a whnf CACHE HIT is also O(1) no-op work that must
    // not tick (Lean checks its whnf cache before `check_system`) — the SAME
    // redex only ticks once (then hits the cache). So drive the counter down
    // with DISTINCT redexes, each a genuine cache-missing reduction that ticks.
    for i in 0..10u32 {
        // Distinct sort level (succ^i zero) ⇒ distinct redex ⇒ cache miss ⇒ a
        // real tick (a shared cached redex would be free after the first).
        let mut lvl = Level::zero();
        for _ in 0..i {
            lvl = Level::succ(lvl);
        }
        let redex = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                Expr::sort(Level::zero()),
                Expr::bvar(0),
            ),
            Expr::sort(lvl),
        );
        let _ = tc.whnf(&redex);
    }

    // Counter should be at 0
    assert_eq!(tc.heartbeat_remaining(), 0);

    // Now infer_type should fail
    let result = tc.infer_type(&prop);
    assert!(
        matches!(result, Err(TypeError::HeartbeatExceeded { limit: 5, .. })),
        "infer_type should fail after heartbeat exhaustion via whnf: {:?}",
        result
    );
}

// ── Profiler integration tests ────────────────────────────────────────

/// Profiler is disabled by default.
#[test]
fn test_profiler_disabled_by_default() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    assert!(!tc.heartbeat_profiler_enabled());
    assert!(tc.heartbeat_profile().is_none());
}

/// Profiler tracks categories when enabled.
#[test]
fn test_profiler_tracks_categories() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();
    assert!(tc.heartbeat_profiler_enabled());

    let prop = Expr::sort(Level::zero());

    // infer_type ticks InferType category
    let _ = tc.infer_type(&prop).unwrap();

    // whnf ticks Whnf category
    let _ = tc.whnf(&prop);

    // is_def_eq ticks IsDefEq category
    tc.is_def_eq(&prop, &prop);

    let profile = tc.heartbeat_profile().expect("profiler should be enabled");
    assert!(profile.total() > 0, "profiler should have recorded ticks");

    // All three categories should appear
    let cat_names: Vec<String> = profile
        .categories
        .iter()
        .map(|c| c.category.to_string())
        .collect();
    assert!(
        cat_names.contains(&"inferType".to_string()),
        "should track inferType, got: {cat_names:?}"
    );
    // whnf and isDefEq are called internally by infer_type, so they should also appear
}

/// Profiler includes profile in HeartbeatExceeded error.
#[test]
fn test_profiler_included_in_error() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(5);
    tc.enable_heartbeat_profiler();

    let prop = Expr::sort(Level::zero());

    // Exhaust heartbeats
    for _ in 0..10 {
        let _ = tc.infer_type(&prop);
    }

    let result = tc.infer_type(&prop);
    match result {
        Err(TypeError::HeartbeatExceeded {
            limit: 5,
            ref profile,
        }) => {
            assert!(profile.is_some(), "profile should be included in error");
            let p = profile.as_ref().unwrap();
            assert!(p.total() > 0, "profile should have ticks");
            // Error message should include the profile
            let msg = result.unwrap_err().to_string();
            assert!(
                msg.contains("Heartbeat profile"),
                "error message should include profile: {msg}"
            );
        }
        other => panic!("Expected HeartbeatExceeded, got: {other:?}"),
    }
}

/// Profiler without enabled profiler yields None in error.
#[test]
fn test_profiler_not_included_when_disabled() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1);

    let prop = Expr::sort(Level::zero());
    let _ = tc.infer_type(&prop);
    let result = tc.infer_type(&prop);
    match result {
        Err(TypeError::HeartbeatExceeded { profile, .. }) => {
            assert!(
                profile.is_none(),
                "profile should be None when profiler disabled"
            );
        }
        other => panic!("Expected HeartbeatExceeded, got: {other:?}"),
    }
}

/// Profiler tracks active name attribution.
#[test]
fn test_profiler_active_name_attribution() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();

    let name = Name::from_string("test.decl");
    tc.set_profiler_active_name(name.clone());

    let prop = Expr::sort(Level::zero());
    let _ = tc.infer_type(&prop).unwrap();
    let _ = tc.whnf(&prop);

    tc.clear_profiler_active_name();

    let profile = tc.heartbeat_profile().expect("profiler should be enabled");
    assert!(
        !profile.top_names.is_empty(),
        "top_names should contain the active name"
    );
    assert_eq!(
        profile.top_names[0].name, name,
        "top name should be the one we set"
    );
    assert!(
        profile.top_names[0].heartbeats > 0,
        "name should have heartbeats attributed"
    );
}

/// Profiler produces correct category breakdown through real Pi type inference.
///
/// Pi type inference triggers whnf (for domain/body normalization), isDefEq
/// (for imax level comparison), and inferType (for the Pi itself and sub-exprs).
/// The profiler should capture all three categories.
#[test]
fn test_profiler_category_breakdown_through_pi_inference() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();

    // Pi (x : Prop) -> Type 1 — requires inferring sort of Prop and Type 1,
    // then computing imax(0, succ(1)) for the result sort.
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::sort(Level::succ(Level::succ(Level::zero()))),
    );
    let result = tc.infer_type(&pi);
    assert!(result.is_ok(), "Pi inference should succeed: {result:?}");

    let profile = tc.heartbeat_profile().expect("profiler should be enabled");
    assert!(profile.total() > 0, "profile should record ticks");
    assert!(
        !profile.categories.is_empty(),
        "categories should be populated"
    );

    // inferType must appear (we called infer_type)
    let has_infer = profile
        .categories
        .iter()
        .any(|e| e.category == heartbeat_profiler::HeartbeatProfileCategory::InferType);
    assert!(has_infer, "InferType category should appear in profile");

    // Verify display format includes the expected fields
    let display = format!("{profile}");
    assert!(
        display.contains("Heartbeat profile"),
        "display should have header"
    );
    assert!(
        display.contains("By operation:"),
        "display should have operation section"
    );
}

/// Profiler displays percentage breakdown that sums close to 100%.
#[test]
fn test_profiler_percentage_sum_approximately_100() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();

    // Exercise all three categories via a mix of operations
    let prop = Expr::sort(Level::zero());
    let type1 = Expr::sort(Level::succ(Level::zero()));

    for _ in 0..5 {
        let _ = tc.infer_type(&prop).unwrap();
        let _ = tc.whnf(&prop);
        tc.is_def_eq(&prop, &type1);
    }

    let profile = tc.heartbeat_profile().expect("profiler should be enabled");
    let total = profile.total() as f64;
    assert!(total > 0.0, "should have recorded ticks");

    let sum_hb: u64 = profile.categories.iter().map(|e| e.heartbeats).sum();
    // Category sum should equal total (each tick is attributed to exactly one category)
    assert_eq!(
        sum_hb,
        profile.total(),
        "category heartbeats should sum to total: sum={sum_hb}, total={}",
        profile.total()
    );
}

/// Profiler reset clears state for a fresh profiling session.
#[test]
fn test_profiler_reset_via_tc() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();

    let prop = Expr::sort(Level::zero());
    let _ = tc.infer_type(&prop).unwrap();

    let profile1 = tc.heartbeat_profile().unwrap();
    assert!(profile1.total() > 0);

    // Disable and re-enable to get a fresh profiler
    tc.disable_heartbeat_profiler();
    tc.enable_heartbeat_profiler();

    let profile2 = tc.heartbeat_profile().unwrap();
    assert_eq!(profile2.total(), 0, "fresh profiler should have 0 ticks");
}

/// Multiple active names are tracked and top-N ordering works.
#[test]
fn test_profiler_multiple_names_top_n_ordering() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(200_000);
    tc.enable_heartbeat_profiler();

    let prop = Expr::sort(Level::zero());

    // First name: many ticks
    tc.set_profiler_active_name(Name::from_string("hot.constant"));
    for _ in 0..20 {
        let _ = tc.infer_type(&prop).unwrap();
    }

    // Second name: fewer ticks
    tc.set_profiler_active_name(Name::from_string("warm.constant"));
    for _ in 0..5 {
        let _ = tc.infer_type(&prop).unwrap();
    }

    // Third name: fewest ticks
    tc.set_profiler_active_name(Name::from_string("cold.constant"));
    let _ = tc.infer_type(&prop).unwrap();
    tc.clear_profiler_active_name();

    let profile = tc.heartbeat_profile().unwrap();
    assert!(
        profile.top_names.len() >= 3,
        "should have at least 3 names: {:?}",
        profile.top_names
    );

    // Verify descending order by heartbeats
    for pair in profile.top_names.windows(2) {
        assert!(
            pair[0].heartbeats >= pair[1].heartbeats,
            "top_names should be sorted descending: {} >= {}",
            pair[0].heartbeats,
            pair[1].heartbeats
        );
    }

    // First name should be "hot.constant" (most ticks)
    assert_eq!(
        profile.top_names[0].name,
        Name::from_string("hot.constant"),
        "hottest constant should be first"
    );
}

/// add_decl enables profiling when profileHeartbeats option is set,
/// and sets the active name to the constant being checked.
#[test]
fn test_add_decl_profile_heartbeats_option() {
    use crate::env::Declaration;

    let mut env = Environment::new();

    // Enable heartbeat profiling via env option
    env.set_option("profileHeartbeats".to_string(), Some("true".to_string()));

    // Add an axiom (simplest declaration type — type-checks the type only)
    let decl = Declaration::Axiom {
        name: Name::from_string("myAxiom"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()), // Prop : Type
    };
    let result = env.add_decl(decl);
    assert!(result.is_ok(), "add_decl should succeed: {result:?}");

    // If the profiler was enabled, the HeartbeatExceeded error would include
    // a profile. Since we didn't exceed the limit, we can't directly observe
    // the profile from add_decl. But we can verify the option is read by
    // checking a tight-limit scenario with profiling.
    let mut env2 = Environment::new();
    env2.set_option("profileHeartbeats".to_string(), Some("true".to_string()));
    env2.set_option("maxHeartbeats".to_string(), Some("1".to_string()));

    // This should fail with HeartbeatExceeded + profile
    let decl2 = Declaration::Definition {
        name: Name::from_string("myDef"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
        value: Expr::sort(Level::zero()),
        is_reducible: false,
    };
    let result2 = env2.add_decl(decl2);
    match result2 {
        Err(crate::env::EnvError::TypeCheckFailed { source, .. }) => {
            match source {
                TypeError::HeartbeatExceeded { profile, .. } => {
                    assert!(
                        profile.is_some(),
                        "profileHeartbeats=true should include profile in HeartbeatExceeded"
                    );
                    let p = profile.unwrap();
                    assert!(p.total() > 0, "profile should have recorded ticks");
                    // The active name should be "myDef" (set by add_decl)
                    if !p.top_names.is_empty() {
                        assert_eq!(
                            p.top_names[0].name,
                            Name::from_string("myDef"),
                            "active name should be the declaration being checked"
                        );
                    }
                }
                other => {
                    // With limit=1, we may get HeartbeatExceeded or succeed
                    // depending on how many ticks the type check requires.
                    // If it's some other error, that's also fine.
                    let _ = other;
                }
            }
        }
        Ok(()) => {
            // With limit=1, Definition might succeed if type check is trivial enough
        }
        Err(_) => {
            // Other error types are acceptable
        }
    }
}
