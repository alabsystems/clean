// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof coverage tests — TcCaches cross-call reuse.
//!
//! Covers:
//! - `TypeChecker::with_context_and_caches` (tc/mod.rs:664) — ZERO previous coverage
//! - `TypeChecker::take_caches` (tc/mod.rs:692) — ZERO previous coverage
//! - Cache transfer preserves correctness across TC instances
//! - `batch_check_with_stats` (tc/batch.rs:280) — ZERO previous coverage
//!
//! The cache reuse path is the mechanism for elaborator → TC cross-call caching
//! (Part of #1671). If it silently corrupts, the elaborator would produce wrong types.

use super::*;
use crate::env::Declaration;

/// Helper: create an environment with basic axioms for cache testing.
fn env_with_axioms() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add axiom A : Type");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add axiom B : Type");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .expect("add axiom a : A");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("B"), vec![]),
        ),
    })
    .expect("add axiom f : A → B");

    env
}

fn cache_count(debug: &str, field: &str) -> usize {
    debug
        .split_once(&format!("{field}: "))
        .and_then(|(_, rest)| rest.split([',', '}']).next())
        .and_then(|value| value.parse().ok())
        .unwrap_or_else(|| panic!("missing {field} in cache debug: {debug}"))
}

fn env_with_pair_projection() -> Environment {
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let pair = Name::from_string("Pair");

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    Expr::prop(),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::prop(),
                        Expr::const_(pair.clone(), vec![]),
                    ),
                ),
            }],
        }],
    };
    env.add_inductive(decl).expect("add Pair inductive");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pairVal"),
        level_params: vec![],
        type_: Expr::const_(pair, vec![]),
    })
    .expect("add pairVal axiom");
    env
}

// =============================================================================
// take_caches: extraction yields non-empty caches after computation
// =============================================================================

#[test]
fn test_take_caches_empty_on_new_tc() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);
    let caches = tc.take_caches();

    // A fresh TC should have empty caches
    assert_eq!(
        format!("{:?}", caches),
        "TcCaches { whnf_entries: 0, whnf_core_entries: 0, def_eq_entries: 0, proj_type_entries: 0, unfold_entries: 0, next_fvar_id: 0 }",
        "Fresh TypeChecker should have empty caches"
    );
}

#[test]
fn test_take_caches_populated_after_computation() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // Perform some computations to populate caches
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let _ty = tc.infer_type(&a_const).expect("infer_type(A)");

    // is_def_eq populates def_eq_cache
    assert!(tc.is_def_eq(&a_const, &a_const));

    // whnf populates whnf_cache
    let _w = tc.whnf(&a_const);

    let caches = tc.take_caches();
    let debug = format!("{:?}", caches);
    // After computations, at least one cache should be non-empty
    assert!(
        !debug.contains("whnf_entries: 0, whnf_core_entries: 0, def_eq_entries: 0"),
        "Caches should be populated after computation, got: {debug}"
    );
}

#[test]
fn test_take_caches_empties_tc() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // Populate caches
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let _ty = tc.infer_type(&a_const).expect("infer_type(A)");
    assert!(tc.is_def_eq(&a_const, &a_const));
    let _w = tc.whnf(&a_const);

    // Take caches — should empty the TC
    let _caches = tc.take_caches();

    // After take, TC caches should be empty
    let caches2 = tc.take_caches();
    assert_eq!(
        format!("{:?}", caches2),
        "TcCaches { whnf_entries: 0, whnf_core_entries: 0, def_eq_entries: 0, proj_type_entries: 0, unfold_entries: 0, next_fvar_id: 0 }",
        "TC caches should be empty after take_caches"
    );
}

// =============================================================================
// with_context_and_caches: cache transfer correctness
// =============================================================================

#[test]
fn test_with_context_and_caches_preserves_correctness() {
    let env = env_with_axioms();

    // First TC: do some work, extract caches
    let tc1 = TypeChecker::new(&env);
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let f_const = Expr::const_(Name::from_string("f"), vec![]);
    let a_val = Expr::const_(Name::from_string("a"), vec![]);
    let f_a = Expr::app(f_const.clone(), a_val.clone());

    let ty_a = tc1.infer_type(&a_const).expect("infer_type(A)");
    let ty_f_a = tc1.infer_type(&f_a).expect("infer_type(f a)");
    assert!(tc1.is_def_eq(&a_const, &a_const));
    let _ = tc1.whnf(&a_const);
    let _ = tc1.whnf(&f_a);

    let caches = tc1.take_caches();

    // Second TC: inject caches from first TC
    let tc2 = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);

    // Verify that the second TC produces the same results
    let ty_a_2 = tc2
        .infer_type(&a_const)
        .expect("infer_type(A) via cached TC");
    let ty_f_a_2 = tc2.infer_type(&f_a).expect("infer_type(f a) via cached TC");

    assert_eq!(
        ty_a, ty_a_2,
        "Cache-injected TC should produce same type for A"
    );
    assert_eq!(
        ty_f_a, ty_f_a_2,
        "Cache-injected TC should produce same type for f(a)"
    );

    // def_eq should work correctly with transferred caches
    assert!(
        tc2.is_def_eq(&a_const, &a_const),
        "def_eq reflexivity should work with cached TC"
    );
    assert!(
        !tc2.is_def_eq(&a_const, &Expr::const_(Name::from_string("B"), vec![])),
        "A and B should not be def_eq even with caches"
    );
}

#[test]
fn test_with_context_and_caches_inherits_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let caches = TcCaches::default();

    let tc = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);

    let interval = Expr::from_kind(ExprKind::CubicalInterval);
    let ty = tc
        .infer_type(&interval)
        .expect("with_context_and_caches should inherit cubical mode from the environment");
    assert_eq!(tc.mode(), env.mode());
    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_with_context_and_caches_preserves_projection_cache() {
    let env = env_with_pair_projection();
    let pair_val = Expr::const_(Name::from_string("pairVal"), vec![]);
    let proj = Expr::proj(Name::from_string("Pair"), 1, pair_val);

    let tc1 = TypeChecker::new(&env);
    let ty1 = tc1
        .infer_type(&proj)
        .expect("infer_type should compute projection type");
    assert_eq!(ty1, Expr::prop(), "pairVal.snd should have type Prop");

    let caches = tc1.take_caches();
    let debug = format!("{:?}", caches);
    assert!(
        cache_count(&debug, "proj_type_entries") > 0,
        "projection inference should populate proj_type cache: {debug}"
    );

    let tc2 = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches);
    assert!(
        tc2.proj_type_cache_entries() > 0,
        "with_context_and_caches should preserve projection cache entries"
    );

    let ty2 = tc2
        .infer_type(&proj)
        .expect("infer_type should succeed with transferred projection cache");
    assert_eq!(ty2, ty1, "projection type should survive cache transfer");
}

#[test]
fn test_cache_roundtrip_multiple_cycles() {
    let env = env_with_axioms();
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let a_val = Expr::const_(Name::from_string("a"), vec![]);

    // Cycle 1
    let tc1 = TypeChecker::new(&env);
    let _ = tc1.infer_type(&a_const).expect("cycle 1: infer A");
    let _ = tc1.infer_type(&a_val).expect("cycle 1: infer a");
    assert!(tc1.is_def_eq(&a_const, &a_const));
    let caches1 = tc1.take_caches();

    // Cycle 2: use caches from cycle 1
    let tc2 = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches1);
    let _ = tc2.infer_type(&Expr::prop()).expect("cycle 2: infer Prop");
    assert!(tc2.is_def_eq(&a_val, &a_val));
    let caches2 = tc2.take_caches();

    // Cycle 3: use caches from cycle 2
    let tc3 = TypeChecker::with_context_and_caches(&env, LocalContext::new(), caches2);
    let ty = tc3.infer_type(&a_const).expect("cycle 3: infer A");
    assert!(
        matches!(&ty.kind, ExprKind::Sort(_)),
        "Type inference should still work after 3 cache transfer cycles"
    );
}

// =============================================================================
// check_type: primary verification entry point (tc/infer.rs:670)
// =============================================================================

#[test]
fn test_check_type_success_axiom() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // a : A, so check_type(a, A) should succeed
    let a_val = Expr::const_(Name::from_string("a"), vec![]);
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    tc.check_type(&a_val, &a_type)
        .expect("check_type(a, A) should succeed since a : A");
}

#[test]
fn test_check_type_success_sort() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Prop : Type, so check_type(Prop, Type) should succeed
    tc.check_type(&Expr::prop(), &Expr::type_())
        .expect("check_type(Prop, Type) should succeed");
}

#[test]
fn test_check_type_success_nat_lit() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // 42 : Nat
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    tc.check_type(&Expr::nat_lit(42), &nat_type)
        .expect("check_type(42, Nat) should succeed");
}

#[test]
fn test_check_type_failure_type_mismatch() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // a : A, so check_type(a, B) should fail since A ≠ B
    let a_val = Expr::const_(Name::from_string("a"), vec![]);
    let b_type = Expr::const_(Name::from_string("B"), vec![]);
    let result = tc.check_type(&a_val, &b_type);
    match result.expect_err("check_type(a, B) should fail since a : A and A ≠ B") {
        TypeError::TypeMismatch {
            expected, inferred, ..
        } => {
            assert_eq!(*expected, b_type, "expected type should be B");
            assert_eq!(
                *inferred,
                Expr::const_(Name::from_string("A"), vec![]),
                "inferred type should be A"
            );
        }
        other => panic!("Expected TypeMismatch, got: {other:?}"),
    }
}

#[test]
fn test_check_type_application() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // f : A → B, a : A, so f(a) : B
    let f_const = Expr::const_(Name::from_string("f"), vec![]);
    let a_val = Expr::const_(Name::from_string("a"), vec![]);
    let b_type = Expr::const_(Name::from_string("B"), vec![]);
    let f_a = Expr::app(f_const, a_val);

    tc.check_type(&f_a, &b_type)
        .expect("check_type(f(a), B) should succeed since f : A → B and a : A");
}

#[test]
fn test_check_type_lambda() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // λ (x : A), x : A → A
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let identity = Expr::lam(BinderInfo::Default, a_type.clone(), Expr::bvar(0));
    let expected_type = Expr::pi(BinderInfo::Default, a_type.clone(), a_type);

    tc.check_type(&identity, &expected_type)
        .expect("check_type(λ x:A, x, A → A) should succeed");
}

#[test]
fn test_check_type_dangling_bvar() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // BVar(99) with no binder context should fail
    let result = tc.check_type(&Expr::bvar(99), &Expr::type_());
    let _err = result.expect_err("check_type on dangling BVar should fail");
}

// =============================================================================
// infer_sort: universe level inference (tc/infer.rs:683)
// =============================================================================

#[test]
fn test_infer_sort_prop() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // typeof(Prop) = Type = Sort(1), so infer_sort(Prop) = Level(1)
    let level = tc.infer_sort(&Expr::prop()).expect("infer_sort(Prop)");
    assert_eq!(
        level,
        Level::succ(Level::zero()),
        "infer_sort(Prop) should return Level(1)"
    );
}

#[test]
fn test_infer_sort_type() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // typeof(Type) = Sort(2), so infer_sort(Type) = Level(2)
    let level = tc.infer_sort(&Expr::type_()).expect("infer_sort(Type)");
    assert_eq!(
        level,
        Level::succ(Level::succ(Level::zero())),
        "infer_sort(Type) should return Level(2)"
    );
}

#[test]
fn test_infer_sort_non_sort_fails() {
    let env = env_with_axioms();
    let tc = TypeChecker::new(&env);

    // a : A, typeof(a) = A which is not a Sort
    let a_val = Expr::const_(Name::from_string("a"), vec![]);
    let result = tc.infer_sort(&a_val);
    let _err = result.expect_err("infer_sort on a term (not a type) should fail");
}

// =============================================================================
// batch_check_with_stats (tc/batch.rs:280) — ZERO previous coverage
// =============================================================================

#[test]
fn test_batch_check_with_stats() {
    use crate::tc::batch::BatchVerifier;

    let env = env_with_axioms();
    let verifier = BatchVerifier::new(&env);

    let exprs = vec![
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::bvar(99), // invalid
        Expr::prop(),
        Expr::const_(Name::from_string("a"), vec![]),
    ];

    let (results, stats) = verifier.batch_check_with_stats(&exprs);

    assert_eq!(results.len(), 4, "Should have 4 results");
    assert!(results[0].valid, "A should be valid");
    assert!(!results[1].valid, "BVar(99) should be invalid");
    assert!(results[2].valid, "Prop should be valid");
    assert!(results[3].valid, "a should be valid");

    assert_eq!(stats.total, 4, "Stats should show 4 total");
    assert_eq!(stats.valid, 3, "Stats should show 3 valid");
    assert_eq!(stats.invalid, 1, "Stats should show 1 invalid");
}

// =============================================================================
// set_transparency: mutable setter (tc/mod.rs:645) — ZERO previous coverage
// =============================================================================

#[test]
fn test_set_transparency() {
    let env = env_with_axioms();
    let mut tc = TypeChecker::new(&env);

    // Default transparency is Default
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let _ = tc
        .infer_type(&a_const)
        .expect("should work with default transparency");

    // Change to All — should still work
    tc.set_transparency(TransparencyMode::All);
    let _ = tc
        .infer_type(&a_const)
        .expect("should work with All transparency");

    // Change to Reducible — most conservative, should still work for axioms
    tc.set_transparency(TransparencyMode::Reducible);
    let _ = tc
        .infer_type(&a_const)
        .expect("should work with Reducible transparency for axioms");
}

// =============================================================================
// with_context_and_mode (tc/mod.rs:304) — ZERO previous coverage
// =============================================================================

#[test]
fn test_with_context_and_mode() {
    let env = env_with_axioms();
    let tc = TypeChecker::with_context_and_mode(&env, LocalContext::new(), CleanMode::default());

    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    let ty = tc
        .infer_type(&a_const)
        .expect("infer_type with context_and_mode");
    assert!(
        matches!(&ty.kind, ExprKind::Sort(_)),
        "A : Type should infer to Sort"
    );
}

#[test]
fn test_with_context_and_mode_with_local_decl() {
    let env = env_with_axioms();
    let mut ctx = LocalContext::new();
    let fvar_id = ctx.push(
        Name::from_string("x"),
        Expr::const_(Name::from_string("A"), vec![]),
        BinderInfo::Default,
    );

    let tc = TypeChecker::with_context_and_mode(&env, ctx, CleanMode::default());

    // The local variable x should be accessible
    let x_fvar = Expr::fvar(fvar_id);
    let ty = tc
        .infer_type(&x_fvar)
        .expect("infer_type of local variable");
    assert_eq!(
        ty,
        Expr::const_(Name::from_string("A"), vec![]),
        "x should have type A"
    );
}

// =============================================================================
// tracing system (tc/mod.rs:520-543) — ZERO previous coverage
// =============================================================================

#[test]
fn test_tracing_disabled_by_default() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    assert!(
        !tc.tracing_enabled(),
        "Tracing should be disabled by default"
    );
    assert!(
        tc.trace_collector().is_none(),
        "No trace collector should be set by default"
    );
}

#[test]
fn test_set_trace_collector_enables_tracing() {
    use crate::cert::ThreadedCollector;
    use std::sync::Arc;

    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);

    // Set a real trace collector
    let collector: crate::cert::SharedTraceCollector = Arc::new(ThreadedCollector::new());
    tc.set_trace_collector(Some(collector.clone()));

    assert!(
        tc.trace_collector().is_some(),
        "Trace collector should be set after set_trace_collector(Some(...))"
    );
    assert!(
        tc.tracing_enabled(),
        "Tracing should be enabled with ThreadedCollector"
    );

    // Clear the trace collector
    tc.set_trace_collector(None);
    assert!(
        tc.trace_collector().is_none(),
        "Trace collector should be None after set_trace_collector(None)"
    );
    assert!(
        !tc.tracing_enabled(),
        "Tracing should be disabled after clearing collector"
    );
}

#[test]
fn test_null_collector_reports_disabled() {
    use crate::cert::NullCollector;
    use std::sync::Arc;

    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);

    // NullCollector is set but reports enabled() = false
    let collector: crate::cert::SharedTraceCollector = Arc::new(NullCollector);
    tc.set_trace_collector(Some(collector));

    assert!(
        tc.trace_collector().is_some(),
        "Collector should be set even with NullCollector"
    );
    assert!(
        !tc.tracing_enabled(),
        "NullCollector should report tracing as disabled"
    );
}
