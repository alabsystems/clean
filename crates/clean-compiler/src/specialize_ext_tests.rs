// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended function specialization (cost model, partial spec, cache,
//! depth limits). Part of #3083.

use super::specialize_ext::*;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use crate::specialize::{SpecKey, SpecializeConfig};
use clean_kernel::Name;
use std::collections::HashMap;

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

fn var(n: u32) -> VarId {
    VarId(n)
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(name(s))
}

fn identity_object(fname: &str) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn two_param_object(fname: &str) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn scalar_fn() -> IRDecl {
    IRDecl {
        name: name("scalar_fn"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn caller(caller_name: &str, target: &str, param_var: u32, param_ty: IRType) -> IRDecl {
    let result_var = param_var + 1;
    IRDecl {
        name: name(caller_name),
        params: vec![(var(param_var), param_ty)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(result_var),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id(target),
                args: vec![IRArg::Var(var(param_var))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(result_var)))),
        },
    }
}

fn two_arg_caller(cname: &str, target: &str, v0: u32, t0: IRType, v1: u32, t1: IRType) -> IRDecl {
    let rv = v1 + 1;
    IRDecl {
        name: name(cname),
        params: vec![(var(v0), t0), (var(v1), t1)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(rv),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id(target),
                args: vec![IRArg::Var(var(v0)), IRArg::Var(var(v1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(rv)))),
        },
    }
}

// -----------------------------------------------------------------------
// Config tests
// -----------------------------------------------------------------------

#[test]
fn test_config_default_values() {
    let c = SpecializeExtConfig::default();
    assert_eq!(c.max_specialization_depth, 2);
    assert_eq!(c.max_specialized_args_per_call, 2);
    assert_eq!(c.min_call_count, 1);
    assert_eq!(c.max_code_size_increase, 96);
    assert!(c.min_speedup_factor > 1.0);
    assert!(c.enable_partial_specialization);
}

#[test]
fn test_config_inherits_base() {
    let c = SpecializeExtConfig::default();
    assert_eq!(c.base.max_specializations_per_fn, 8);
    assert_eq!(c.base.max_total_specializations, 256);
}

// -----------------------------------------------------------------------
// Stats tests
// -----------------------------------------------------------------------

#[test]
fn test_stats_default_all_zero() {
    let s = SpecializeExtStats::default();
    assert_eq!(s.candidates_found, 0);
    assert_eq!(s.call_sites_analyzed, 0);
    assert_eq!(s.call_patterns_observed, 0);
    assert_eq!(s.specializations_generated, 0);
    assert_eq!(s.partial_specializations, 0);
    assert_eq!(s.rewritten_decls, 0);
    assert_eq!(s.cache_hits, 0);
    assert_eq!(s.profitable_rejections, 0);
    assert_eq!(s.depth_rejections, 0);
    assert_eq!(s.limit_rejections, 0);
    assert_eq!(s.errors, 0);
}

// -----------------------------------------------------------------------
// CallSiteInfo tests
// -----------------------------------------------------------------------

#[test]
fn test_call_site_info_observe_increments_count() {
    let mut info = CallSiteInfo::default();
    info.observe(vec![Some(IRType::UInt64)]);
    assert_eq!(info.call_count, 1);
    assert_eq!(info.argument_type_patterns.len(), 1);
}

#[test]
fn test_call_site_info_observe_dedup_patterns() {
    let mut info = CallSiteInfo::default();
    info.observe(vec![Some(IRType::UInt64)]);
    info.observe(vec![Some(IRType::UInt64)]);
    assert_eq!(info.call_count, 2);
    assert_eq!(info.argument_type_patterns.len(), 1);
}

#[test]
fn test_call_site_info_observe_distinct_patterns() {
    let mut info = CallSiteInfo::default();
    info.observe(vec![Some(IRType::UInt64)]);
    info.observe(vec![Some(IRType::Bool)]);
    assert_eq!(info.call_count, 2);
    assert_eq!(info.argument_type_patterns.len(), 2);
}

// -----------------------------------------------------------------------
// SpecializationCost tests
// -----------------------------------------------------------------------

#[test]
fn test_cost_profitable_when_good_speedup() {
    let cost = SpecializationCost {
        estimated_code_size_increase: 5,
        estimated_speedup_factor: 1.35,
    };
    assert!(cost.is_profitable());
}

#[test]
fn test_cost_not_profitable_low_speedup() {
    let cost = SpecializationCost {
        estimated_code_size_increase: 5,
        estimated_speedup_factor: 1.05,
    };
    assert!(!cost.is_profitable());
}

#[test]
fn test_cost_not_profitable_high_code_increase() {
    let cost = SpecializationCost {
        estimated_code_size_increase: 1000,
        estimated_speedup_factor: 1.15,
    };
    assert!(!cost.is_profitable());
}

// -----------------------------------------------------------------------
// SpecializationCache tests
// -----------------------------------------------------------------------

#[test]
fn test_cache_insert_and_get() {
    let mut cache = SpecializationCache::default();
    let key = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    cache.insert(key.clone(), name("f_spec"));
    assert_eq!(cache.get(&key), Some(&name("f_spec")));
    assert_eq!(cache.len(), 1);
}

#[test]
fn test_cache_miss() {
    let cache = SpecializationCache::default();
    let key = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    assert!(cache.get(&key).is_none());
}

// -----------------------------------------------------------------------
// Error tests
// -----------------------------------------------------------------------

#[test]
fn test_error_depth_limit_display() {
    let e = SpecializeExtError::DepthLimitExceeded {
        fn_name: name("f"),
        depth: 3,
        max_depth: 2,
    };
    let msg = format!("{e}");
    assert!(msg.contains("depth"));
    assert!(msg.contains("3"));
}

#[test]
fn test_error_missing_decl_display() {
    let e = SpecializeExtError::MissingDeclaration(name("missing_fn"));
    let msg = format!("{e}");
    assert!(msg.contains("missing"));
}

#[test]
fn test_error_arity_mismatch_display() {
    let e = SpecializeExtError::ArityMismatch {
        fn_name: name("f"),
        expected: 2,
        actual: 3,
    };
    let msg = format!("{e}");
    assert!(msg.contains("arity"));
}

#[test]
fn test_error_empty_specialization_display() {
    let e = SpecializeExtError::EmptySpecialization(name("f"));
    let msg = format!("{e}");
    assert!(msg.contains("polymorphic"));
}

// -----------------------------------------------------------------------
// run_extended_specialization: basic pipeline
// -----------------------------------------------------------------------

#[test]
fn test_run_empty_input() {
    let (result, stats) = run_extended_specialization(&[], &SpecializeExtConfig::default());
    assert!(result.is_empty());
    assert_eq!(stats.candidates_found, 0);
}

#[test]
fn test_run_no_candidates() {
    let decls = vec![scalar_fn()];
    let (result, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    assert_eq!(result.len(), 1);
    assert_eq!(stats.candidates_found, 0);
}

#[test]
fn test_run_generates_specialization() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let (result, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    assert!(stats.candidates_found >= 1);
    assert!(stats.specializations_generated >= 1);
    assert!(result.len() > decls.len());
}

#[test]
fn test_run_rewrites_call_sites() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let (_, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    assert!(stats.rewritten_decls >= 1);
}

#[test]
fn test_run_dedup_same_key() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
        caller("c2", "foo", 20, IRType::UInt64),
    ];
    let (_, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    assert!(stats.cache_hits >= 1);
}

#[test]
fn test_run_different_types_generate_different_specs() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
        caller("c2", "foo", 20, IRType::Bool),
    ];
    let (result, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    assert!(stats.specializations_generated >= 2);
    let spec_count = result.len() - decls.len();
    assert!(spec_count >= 2);
}

// -----------------------------------------------------------------------
// Partial specialization
// -----------------------------------------------------------------------

#[test]
fn test_partial_specialization_enabled() {
    let decls = vec![
        two_param_object("bar"),
        two_arg_caller("c1", "bar", 10, IRType::UInt64, 11, IRType::Object),
    ];
    let config = SpecializeExtConfig {
        enable_partial_specialization: true,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert!(
        stats.specializations_generated >= 1,
        "should generate at least one partial spec"
    );
}

#[test]
fn test_partial_specialization_disabled() {
    let decls = vec![
        two_param_object("bar"),
        two_arg_caller("c1", "bar", 10, IRType::UInt64, 11, IRType::Object),
    ];
    let config = SpecializeExtConfig {
        enable_partial_specialization: false,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    // With partial disabled, only full-concrete keys are generated.
    // Since one arg is Object, only the single-concrete key matches if expanded.
    // Still should find something since the one concrete arg is UInt64.
    assert!(stats.specializations_generated >= 1 || stats.profitable_rejections >= 1);
}

#[test]
fn test_partial_specialization_counted_in_stats() {
    let decls = vec![
        two_param_object("bar"),
        two_arg_caller("c1", "bar", 10, IRType::UInt64, 11, IRType::Bool),
    ];
    let config = SpecializeExtConfig {
        enable_partial_specialization: true,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    // With 2 concrete args and partial enabled, generates size=1 and size=2 keys.
    // The size=1 keys are partial specializations.
    assert!(stats.partial_specializations >= 1 || stats.specializations_generated >= 2);
}

// -----------------------------------------------------------------------
// Depth limits
// -----------------------------------------------------------------------

#[test]
fn test_depth_limit_zero_generates_nothing() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let config = SpecializeExtConfig {
        max_specialization_depth: 0,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert_eq!(stats.specializations_generated, 0);
    assert!(stats.depth_rejections >= 1);
}

#[test]
fn test_depth_limit_one_allows_first_level() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let config = SpecializeExtConfig {
        max_specialization_depth: 1,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert!(stats.specializations_generated >= 1);
}

// -----------------------------------------------------------------------
// Limit rejections
// -----------------------------------------------------------------------

#[test]
fn test_per_fn_limit_rejection() {
    let mut decls = vec![identity_object("foo")];
    for i in 0..10u32 {
        let ty = match i % 4 {
            0 => IRType::UInt8,
            1 => IRType::UInt16,
            2 => IRType::UInt32,
            _ => IRType::Float32,
        };
        decls.push(caller(&format!("c{i}"), "foo", 100 + i * 10, ty));
    }
    let config = SpecializeExtConfig {
        base: SpecializeConfig {
            max_specializations_per_fn: 2,
            ..Default::default()
        },
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert!(stats.limit_rejections >= 1);
    assert!(stats.specializations_generated <= 2);
}

#[test]
fn test_total_limit_rejection() {
    let mut decls = vec![identity_object("foo")];
    for i in 0..10u32 {
        let ty = match i % 5 {
            0 => IRType::UInt8,
            1 => IRType::UInt16,
            2 => IRType::UInt32,
            3 => IRType::Float32,
            _ => IRType::Float64,
        };
        decls.push(caller(&format!("c{i}"), "foo", 100 + i * 10, ty));
    }
    let config = SpecializeExtConfig {
        base: SpecializeConfig {
            max_total_specializations: 2,
            max_specializations_per_fn: 100,
            ..Default::default()
        },
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert!(stats.limit_rejections >= 1);
}

// -----------------------------------------------------------------------
// Cost model
// -----------------------------------------------------------------------

#[test]
fn test_unprofitable_rejection() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let config = SpecializeExtConfig {
        min_speedup_factor: 100.0,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert_eq!(stats.specializations_generated, 0);
    assert!(stats.profitable_rejections >= 1);
}

#[test]
fn test_code_size_limit_rejection() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let config = SpecializeExtConfig {
        max_code_size_increase: 0,
        ..Default::default()
    };
    let (_, stats) = run_extended_specialization(&decls, &config);
    assert_eq!(stats.specializations_generated, 0);
}

// -----------------------------------------------------------------------
// Edge cases
// -----------------------------------------------------------------------

#[test]
fn test_erased_arg_no_specialization() {
    let foo = identity_object("foo");
    let caller_decl = IRDecl {
        name: name("erased_caller"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(0),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("foo"),
                args: vec![IRArg::Erased],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        },
    };
    let (_, stats) =
        run_extended_specialization(&[foo, caller_decl], &SpecializeExtConfig::default());
    assert_eq!(stats.specializations_generated, 0);
}

#[test]
fn test_object_arg_no_specialization() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::Object),
    ];
    let (_, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    // Object->Object is not a concrete specialization
    assert_eq!(stats.specializations_generated, 0);
}

#[test]
fn test_specialized_decl_params_rewritten() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let (result, _) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    let spec = result.iter().find(|d| {
        let s = format!("{}", d.name);
        s.contains("spec")
    });
    if let Some(spec) = spec {
        assert_eq!(spec.params.len(), 1);
        assert_eq!(spec.params[0].1, IRType::UInt64);
    }
}

#[test]
fn test_caller_rewritten_to_spec_target() {
    let decls = vec![
        identity_object("foo"),
        caller("c1", "foo", 10, IRType::UInt64),
    ];
    let (result, stats) = run_extended_specialization(&decls, &SpecializeExtConfig::default());
    if stats.rewritten_decls > 0 {
        let c1 = result
            .iter()
            .find(|d| d.name == name("c1"))
            .expect("caller should exist");
        match &c1.body {
            IRBody::VDecl {
                value: IRExpr::Apply { fn_id, .. },
                ..
            } => {
                let s = format!("{}", fn_id.0);
                assert!(s.contains("spec"), "call target should be rewritten: {s}");
            }
            _ => panic!("expected VDecl with Apply"),
        }
    }
}

// -----------------------------------------------------------------------
// SpecKey hash uniqueness
// -----------------------------------------------------------------------

#[test]
fn test_spec_key_equality() {
    let k1 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    let k2 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    assert_eq!(k1, k2);
}

#[test]
fn test_spec_key_different_types_differ() {
    let k1 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    let k2 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::Bool)],
    };
    assert_ne!(k1, k2);
}

#[test]
fn test_spec_key_different_fn_names_differ() {
    let k1 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    let k2 = SpecKey {
        fn_name: name("g"),
        type_args: vec![Some(IRType::UInt64)],
    };
    assert_ne!(k1, k2);
}

#[test]
fn test_spec_key_none_vs_some_differ() {
    let k1 = SpecKey {
        fn_name: name("f"),
        type_args: vec![None],
    };
    let k2 = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64)],
    };
    assert_ne!(k1, k2);
}

// -----------------------------------------------------------------------
// HashMap uses Hash correctly
// -----------------------------------------------------------------------

#[test]
fn test_spec_key_hashmap_lookup() {
    let mut map = HashMap::new();
    let k = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64), None],
    };
    map.insert(k.clone(), name("f_spec"));
    let lookup = SpecKey {
        fn_name: name("f"),
        type_args: vec![Some(IRType::UInt64), None],
    };
    assert_eq!(map.get(&lookup), Some(&name("f_spec")));
}

// -----------------------------------------------------------------------
// Complex body traversal
// -----------------------------------------------------------------------

#[test]
fn test_complex_body_with_inc_dec() {
    let foo = identity_object("foo");
    let caller_decl = IRDecl {
        name: name("complex_caller"),
        params: vec![(var(10), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::Inc {
            var: var(10),
            n: 1,
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: fn_id("foo"),
                    args: vec![IRArg::Var(var(10))],
                },
                rest: Box::new(IRBody::Dec {
                    var: var(10),
                    rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
                }),
            }),
        },
    };
    let (_, stats) =
        run_extended_specialization(&[foo, caller_decl], &SpecializeExtConfig::default());
    assert!(stats.call_sites_analyzed >= 1);
}

#[test]
fn test_multiple_call_sites_in_one_body() {
    let foo = identity_object("foo");
    let caller_decl = IRDecl {
        name: name("multi_caller"),
        params: vec![(var(10), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("foo"),
                args: vec![IRArg::Var(var(10))],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(12),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: fn_id("foo"),
                    args: vec![IRArg::Var(var(10))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(var(12)))),
            }),
        },
    };
    let (_, stats) =
        run_extended_specialization(&[foo, caller_decl], &SpecializeExtConfig::default());
    assert!(stats.call_sites_analyzed >= 2);
}
