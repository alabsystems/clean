// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended monomorphization (type erasure, specialization, caching,
//! recursive types, closures, statistics). Part of #3083.

use super::to_mono_ext::*;
use crate::ir::{FnId, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
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

fn simple_object_fn(fname: &str) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn two_param_fn(fname: &str, ty0: IRType, ty1: IRType) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(0), ty0), (var(1), ty1)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    }
}

fn erased_caller_fn(caller_name: &str, target: &str) -> IRDecl {
    IRDecl {
        name: name(caller_name),
        params: vec![(var(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id(target),
                args: vec![IRArg::Erased],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(var(11)))),
        },
    }
}

// -----------------------------------------------------------------------
// Config tests
// -----------------------------------------------------------------------

#[test]
fn test_config_default_values() {
    let config = MonoExtConfig::default();
    assert_eq!(config.max_specializations_per_fn, 8);
    assert_eq!(config.max_total_specializations, 256);
    assert_eq!(config.max_recursion_depth, 16);
    assert!(config.erase_type_class_evidence);
    assert!(config.monomorphize_closures);
}

#[test]
fn test_config_custom_values() {
    let config = MonoExtConfig {
        max_specializations_per_fn: 4,
        max_total_specializations: 64,
        max_recursion_depth: 8,
        erase_type_class_evidence: false,
        monomorphize_closures: false,
    };
    assert_eq!(config.max_specializations_per_fn, 4);
    assert!(!config.erase_type_class_evidence);
    assert!(!config.monomorphize_closures);
}

// -----------------------------------------------------------------------
// Type erasure tests
// -----------------------------------------------------------------------

#[test]
fn test_erase_type_args_erased_params() {
    let params = vec![
        (var(0), IRType::Erased),
        (var(1), IRType::UInt64),
        (var(2), IRType::Void),
    ];
    let (result, count) = erase_type_args(&params, &name("f"), false);
    assert_eq!(count, 2);
    assert_eq!(result[0].1, IRType::Object); // Erased -> Object
    assert_eq!(result[1].1, IRType::UInt64); // unchanged
    assert_eq!(result[2].1, IRType::Object); // Void -> Object
}

#[test]
fn test_erase_type_args_no_erasure_needed() {
    let params = vec![(var(0), IRType::UInt64), (var(1), IRType::Bool)];
    let (result, count) = erase_type_args(&params, &name("f"), false);
    assert_eq!(count, 0);
    assert_eq!(result[0].1, IRType::UInt64);
    assert_eq!(result[1].1, IRType::Bool);
}

#[test]
fn test_erase_type_args_all_erased() {
    let params = vec![(var(0), IRType::Erased), (var(1), IRType::Erased)];
    let (_, count) = erase_type_args(&params, &name("f"), false);
    assert_eq!(count, 2);
}

#[test]
fn test_erase_type_args_empty_params() {
    let params: Vec<(VarId, IRType)> = vec![];
    let (result, count) = erase_type_args(&params, &name("f"), false);
    assert_eq!(count, 0);
    assert!(result.is_empty());
}

// -----------------------------------------------------------------------
// Type class evidence erasure tests
// -----------------------------------------------------------------------

#[test]
fn test_is_type_class_evidence_inst() {
    assert!(is_type_class_evidence(&name("Add_inst"), &IRType::Object));
}

#[test]
fn test_is_type_class_evidence_tc() {
    assert!(is_type_class_evidence(&name("Monad_tc"), &IRType::Object));
}

#[test]
fn test_is_type_class_evidence_dict() {
    assert!(is_type_class_evidence(&name("Eq_dict"), &IRType::Object));
}

#[test]
fn test_is_type_class_evidence_non_object() {
    // Even with _inst suffix, non-Object types are not evidence
    assert!(!is_type_class_evidence(&name("_inst"), &IRType::UInt64));
}

#[test]
fn test_is_type_class_evidence_regular_name() {
    assert!(!is_type_class_evidence(&name("foo"), &IRType::Object));
}

#[test]
fn test_erase_type_class_evidence() {
    let params = vec![
        (var(0), IRType::Object), // normal Object param
    ];
    // The function name contains _inst, so all Object params get checked
    let (result, count) = erase_type_args(&params, &name("Add_inst"), true);
    assert_eq!(count, 1);
    assert_eq!(result[0].1, IRType::Erased);
}

// -----------------------------------------------------------------------
// Erased type representation tests
// -----------------------------------------------------------------------

#[test]
fn test_erased_type_repr_erased() {
    assert_eq!(erased_type_repr(&IRType::Erased), IRType::Object);
}

#[test]
fn test_erased_type_repr_void() {
    assert_eq!(erased_type_repr(&IRType::Void), IRType::Object);
}

#[test]
fn test_erased_type_repr_scalar_unchanged() {
    assert_eq!(erased_type_repr(&IRType::UInt64), IRType::UInt64);
    assert_eq!(erased_type_repr(&IRType::Bool), IRType::Bool);
    assert_eq!(erased_type_repr(&IRType::Float64), IRType::Float64);
}

#[test]
fn test_erased_type_repr_object_unchanged() {
    assert_eq!(erased_type_repr(&IRType::Object), IRType::Object);
}

#[test]
fn test_erased_type_repr_nested_struct() {
    let ty = IRType::Struct(vec![IRType::Erased, IRType::UInt64]);
    let result = erased_type_repr(&ty);
    assert_eq!(result, IRType::Struct(vec![IRType::Object, IRType::UInt64]));
}

#[test]
fn test_erased_type_repr_nested_union() {
    let ty = IRType::Union(vec![IRType::Void, IRType::Bool]);
    let result = erased_type_repr(&ty);
    assert_eq!(result, IRType::Union(vec![IRType::Object, IRType::Bool]));
}

// -----------------------------------------------------------------------
// Monomorphization cache tests
// -----------------------------------------------------------------------

#[test]
fn test_cache_empty() {
    let cache = MonoCache::default();
    assert_eq!(cache.len(), 0);
    let key = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    assert!(cache.get(&key).is_none());
}

#[test]
fn test_cache_insert_and_get() {
    let mut cache = MonoCache::default();
    let key = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    cache.insert(key.clone(), name("f_mono_u64"));
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.get(&key), Some(&name("f_mono_u64")));
}

#[test]
fn test_cache_different_keys() {
    let mut cache = MonoCache::default();
    let key1 = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    let key2 = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::Bool],
    };
    cache.insert(key1.clone(), name("f_u64"));
    cache.insert(key2.clone(), name("f_bool"));
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.get(&key1), Some(&name("f_u64")));
    assert_eq!(cache.get(&key2), Some(&name("f_bool")));
}

#[test]
fn test_cache_overwrite() {
    let mut cache = MonoCache::default();
    let key = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    cache.insert(key.clone(), name("v1"));
    cache.insert(key.clone(), name("v2"));
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.get(&key), Some(&name("v2")));
}

// -----------------------------------------------------------------------
// Recursive type handling tests
// -----------------------------------------------------------------------

#[test]
fn test_recursion_tracker_basic() {
    let mut tracker = RecursionTracker::default();
    assert!(!tracker.is_expanding(&name("f")));
    assert!(tracker.enter(&name("f"), 3));
    assert!(tracker.is_expanding(&name("f")));
    tracker.leave(&name("f"));
    assert!(!tracker.is_expanding(&name("f")));
}

#[test]
fn test_recursion_tracker_depth_limit() {
    let mut tracker = RecursionTracker::default();
    assert!(tracker.enter(&name("f"), 2)); // depth 1
    assert!(tracker.enter(&name("f"), 2)); // depth 2
    assert!(!tracker.enter(&name("f"), 2)); // depth 3 - rejected
    tracker.leave(&name("f"));
    tracker.leave(&name("f"));
    assert!(!tracker.is_expanding(&name("f")));
}

#[test]
fn test_recursion_tracker_independent_functions() {
    let mut tracker = RecursionTracker::default();
    assert!(tracker.enter(&name("f"), 1));
    assert!(tracker.enter(&name("g"), 1));
    assert!(!tracker.enter(&name("f"), 1)); // f already at limit
    assert!(!tracker.enter(&name("g"), 1)); // g already at limit
    tracker.leave(&name("f"));
    tracker.leave(&name("g"));
}

// -----------------------------------------------------------------------
// Specialization name tests
// -----------------------------------------------------------------------

#[test]
fn test_mono_specialized_name_single_type() {
    let result = mono_specialized_name(&name("f"), &[IRType::UInt64]);
    let s = format!("{result:?}");
    assert!(s.contains("mono"), "name should contain 'mono': {s}");
    assert!(s.contains("u64"), "name should contain 'u64': {s}");
}

#[test]
fn test_mono_specialized_name_multiple_types() {
    let result = mono_specialized_name(&name("g"), &[IRType::Bool, IRType::Float64]);
    let s = format!("{result:?}");
    assert!(s.contains("mono"), "name should contain 'mono': {s}");
    assert!(s.contains("b"), "name should contain 'b' for Bool: {s}");
    assert!(s.contains("f64"), "name should contain 'f64': {s}");
}

// -----------------------------------------------------------------------
// Specialization creation tests
// -----------------------------------------------------------------------

#[test]
fn test_specialize_decl_basic() {
    let decl = simple_object_fn("identity");
    let result = specialize_decl(&decl, &[IRType::UInt64]);
    assert!(result.is_some());
    let spec = result.unwrap();
    assert_eq!(spec.params[0].1, IRType::UInt64);
    assert_ne!(spec.name, decl.name);
}

#[test]
fn test_specialize_decl_no_change_needed() {
    let decl = IRDecl {
        name: name("scalar"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    // Trying to specialize UInt64 to UInt64 — no Object params to substitute.
    let result = specialize_decl(&decl, &[IRType::UInt64]);
    assert!(
        result.is_none(),
        "should return None when no Object params to specialize"
    );
}

#[test]
fn test_specialize_decl_arity_mismatch() {
    let decl = simple_object_fn("f");
    let result = specialize_decl(&decl, &[IRType::UInt64, IRType::Bool]);
    assert!(result.is_none(), "should return None on arity mismatch");
}

#[test]
fn test_specialize_decl_two_params() {
    let decl = two_param_fn("pair", IRType::Object, IRType::Object);
    let result = specialize_decl(&decl, &[IRType::UInt64, IRType::Bool]);
    assert!(result.is_some());
    let spec = result.unwrap();
    assert_eq!(spec.params[0].1, IRType::UInt64);
    assert_eq!(spec.params[1].1, IRType::Bool);
}

#[test]
fn test_specialize_decl_partial_types() {
    let decl = two_param_fn("mixed", IRType::Object, IRType::UInt64);
    let result = specialize_decl(&decl, &[IRType::Bool, IRType::UInt64]);
    assert!(result.is_some());
    let spec = result.unwrap();
    assert_eq!(spec.params[0].1, IRType::Bool); // specialized
    assert_eq!(spec.params[1].1, IRType::UInt64); // unchanged
}

// -----------------------------------------------------------------------
// Top-level run tests
// -----------------------------------------------------------------------

#[test]
fn test_run_mono_ext_empty() {
    let (result, stats) = run_mono_ext(&[], &MonoExtConfig::default());
    assert!(result.is_empty());
    assert_eq!(stats.decls_processed, 0);
}

#[test]
fn test_run_mono_ext_single_decl_no_erasure() {
    let decl = IRDecl {
        name: name("pure_scalar"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.decls_processed, 1);
    assert_eq!(stats.types_erased, 0);
    assert!(!result.is_empty());
}

#[test]
fn test_run_mono_ext_erased_params() {
    let decl = IRDecl {
        name: name("type_fn"),
        params: vec![(var(0), IRType::Erased), (var(1), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(1))),
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.types_erased, 1);
    // The erased param should be mapped to Object.
    assert_eq!(result[0].params[0].1, IRType::Object);
    assert_eq!(result[0].params[1].1, IRType::UInt64);
}

#[test]
fn test_run_mono_ext_return_type_erased() {
    let decl = IRDecl {
        name: name("erased_ret"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Erased,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.decls_processed, 1);
    // Erased return type -> Object
    assert_eq!(result[0].return_type, IRType::Object);
}

#[test]
fn test_run_mono_ext_statistics_tracking() {
    let decl = IRDecl {
        name: name("stats_fn"),
        params: vec![
            (var(0), IRType::Erased),
            (var(1), IRType::Void),
            (var(2), IRType::UInt64),
        ],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(2))),
    };
    let (_, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.decls_processed, 1);
    assert_eq!(stats.types_erased, 2); // Erased + Void
}

// -----------------------------------------------------------------------
// Closure monomorphization tests
// -----------------------------------------------------------------------

#[test]
fn test_collect_closure_type_captures_partial_apply() {
    let body = IRBody::VDecl {
        var: var(5),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("target"),
            arity: 2,
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(5)))),
    };
    let mut var_types = HashMap::new();
    var_types.insert(var(0), IRType::UInt64);
    let captures = collect_closure_type_captures(&body, &var_types);
    assert!(captures.contains_key(&var(0)));
    assert_eq!(captures[&var(0)], IRType::UInt64);
}

#[test]
fn test_collect_closure_type_captures_no_scalar() {
    let body = IRBody::VDecl {
        var: var(5),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("target"),
            arity: 2,
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(5)))),
    };
    let mut var_types = HashMap::new();
    var_types.insert(var(0), IRType::Object);
    let captures = collect_closure_type_captures(&body, &var_types);
    // Object is not scalar, so no capture recorded.
    assert!(captures.is_empty());
}

#[test]
fn test_collect_closure_type_captures_closure_apply() {
    let body = IRBody::VDecl {
        var: var(5),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(1)),
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(5)))),
    };
    let mut var_types = HashMap::new();
    var_types.insert(var(0), IRType::Bool);
    let captures = collect_closure_type_captures(&body, &var_types);
    assert_eq!(captures.get(&var(0)), Some(&IRType::Bool));
}

// -----------------------------------------------------------------------
// Edge case tests
// -----------------------------------------------------------------------

#[test]
fn test_already_monomorphic() {
    let decl = IRDecl {
        name: name("mono_fn"),
        params: vec![(var(0), IRType::UInt64), (var(1), IRType::Bool)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.types_erased, 0);
    assert_eq!(stats.specializations_created, 0);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_no_params() {
    let decl = IRDecl {
        name: name("nullary"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Erased),
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.types_erased, 0);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_deeply_nested_inc_dec() {
    // Test that body traversal handles Inc/Dec chains.
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
        }),
    };
    let decl = IRDecl {
        name: name("incr_decr"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };
    let (result, stats) = run_mono_ext(&[decl], &MonoExtConfig::default());
    assert_eq!(stats.decls_processed, 1);
    assert!(!result.is_empty());
}

#[test]
fn test_erased_arg_in_call_site() {
    let target = simple_object_fn("target");
    let caller = erased_caller_fn("caller", "target");
    let (result, stats) = run_mono_ext(&[target, caller], &MonoExtConfig::default());
    assert_eq!(stats.decls_processed, 2);
    assert!(result.len() >= 2);
}

#[test]
fn test_run_mono_ext_default_wrapper() {
    let decl = simple_object_fn("f");
    let result = run_mono_ext_default(&[decl]);
    assert!(!result.is_empty());
}

#[test]
fn test_per_fn_specialization_limit() {
    let config = MonoExtConfig {
        max_specializations_per_fn: 1,
        max_total_specializations: 256,
        ..MonoExtConfig::default()
    };
    let target = simple_object_fn("target");
    let c1 = erased_caller_fn("c1", "target");
    let c2 = erased_caller_fn("c2", "target");
    let (_, stats) = run_mono_ext(&[target, c1, c2], &config);
    // At most 1 specialization per function.
    assert!(stats.specializations_created <= 1);
}

#[test]
fn test_total_specialization_limit() {
    let config = MonoExtConfig {
        max_total_specializations: 0,
        ..MonoExtConfig::default()
    };
    let target = simple_object_fn("target");
    let caller = erased_caller_fn("caller", "target");
    let (_, stats) = run_mono_ext(&[target, caller], &config);
    assert_eq!(stats.specializations_created, 0);
}

#[test]
fn test_mono_key_equality() {
    let k1 = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    let k2 = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::UInt64],
    };
    let k3 = MonoKey {
        fn_name: name("f"),
        type_args: vec![IRType::Bool],
    };
    assert_eq!(k1, k2);
    assert_ne!(k1, k3);
}

#[test]
fn test_substitute_types_in_body_vdecl() {
    let body = IRBody::VDecl {
        var: var(0),
        ty: IRType::Object,
        value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var(0)))),
    };
    let mut type_map = HashMap::new();
    type_map.insert(var(0), IRType::UInt64);

    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };
    let result = specialize_decl(&decl, &[IRType::UInt64]);
    assert!(result.is_some());
}

#[test]
fn test_disable_type_class_erasure() {
    let config = MonoExtConfig {
        erase_type_class_evidence: false,
        ..MonoExtConfig::default()
    };
    let params = vec![(var(0), IRType::Object)];
    let (result, count) = erase_type_args(&params, &name("Add_inst"), false);
    assert_eq!(count, 0);
    assert_eq!(result[0].1, IRType::Object); // unchanged
                                             // Verify the config flag propagates to run_mono_ext.
    let decl = IRDecl {
        name: name("Add_inst"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(var(0))),
    };
    let (_, stats) = run_mono_ext(&[decl], &config);
    assert_eq!(stats.evidence_erased, 0);
}

#[test]
fn test_disable_closure_monomorphization() {
    let config = MonoExtConfig {
        monomorphize_closures: false,
        ..MonoExtConfig::default()
    };
    let body = IRBody::VDecl {
        var: var(5),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("target"),
            arity: 2,
            args: vec![IRArg::Var(var(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(var(5)))),
    };
    let decl = IRDecl {
        name: name("closure_fn"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::Object,
        body,
    };
    let (_, stats) = run_mono_ext(&[decl], &config);
    assert_eq!(stats.closures_monomorphized, 0);
}
