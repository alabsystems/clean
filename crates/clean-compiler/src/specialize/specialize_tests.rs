// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR function specialization pass.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;
use std::collections::HashSet;

// ═══════════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════════

fn mk_name(s: &str) -> Name {
    Name::from_string(s)
}

fn mk_fn_id(s: &str) -> FnId {
    FnId(mk_name(s))
}

fn mk_var(n: u32) -> VarId {
    VarId(n)
}

/// Simple function: `fn foo(x: Object) -> Object { return x }`
fn mk_identity_object() -> IRDecl {
    IRDecl {
        name: mk_name("foo"),
        params: vec![(mk_var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(mk_var(0))),
    }
}

/// Function with two Object params: `fn bar(x: Object, y: Object) -> Object`
fn mk_two_param_object() -> IRDecl {
    IRDecl {
        name: mk_name("bar"),
        params: vec![(mk_var(0), IRType::Object), (mk_var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(mk_var(0))),
    }
}

/// Function with scalar param (not a candidate).
fn mk_scalar_fn() -> IRDecl {
    IRDecl {
        name: mk_name("scalar_fn"),
        params: vec![(mk_var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(mk_var(0))),
    }
}

/// Caller that invokes foo with a UInt64-typed local.
fn mk_caller_u64() -> IRDecl {
    IRDecl {
        name: mk_name("caller"),
        params: vec![(mk_var(10), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("foo"),
                args: vec![IRArg::Var(mk_var(10))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(11)))),
        },
    }
}

/// Caller that invokes bar with one UInt64 and one Object.
fn mk_caller_mixed() -> IRDecl {
    IRDecl {
        name: mk_name("caller_mixed"),
        params: vec![(mk_var(10), IRType::UInt64), (mk_var(11), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(12),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("bar"),
                args: vec![IRArg::Var(mk_var(10)), IRArg::Var(mk_var(11))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(12)))),
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Candidate Identification Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_is_specialization_candidate_object_param() {
    let decl = mk_identity_object();
    assert!(is_specialization_candidate(&decl));
}

#[test]
fn test_is_specialization_candidate_scalar_param() {
    let decl = mk_scalar_fn();
    assert!(!is_specialization_candidate(&decl));
}

#[test]
fn test_is_specialization_candidate_mixed_params() {
    let decl = IRDecl {
        name: mk_name("mixed"),
        params: vec![(mk_var(0), IRType::UInt64), (mk_var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(mk_var(0))),
    };
    assert!(is_specialization_candidate(&decl));
}

#[test]
fn test_find_candidates_basic() {
    let decls = vec![mk_identity_object(), mk_scalar_fn()];
    let config = SpecializeConfig::default();
    let candidates = find_candidates(&decls, &config);
    assert_eq!(candidates.len(), 1);
    assert!(candidates.contains(&mk_name("foo")));
}

#[test]
fn test_find_candidates_with_skip() {
    let decls = vec![mk_identity_object(), mk_two_param_object()];
    let mut config = SpecializeConfig::default();
    config.skip_functions.insert(mk_name("foo"));
    let candidates = find_candidates(&decls, &config);
    assert_eq!(candidates.len(), 1);
    assert!(candidates.contains(&mk_name("bar")));
}

#[test]
fn test_find_candidates_with_only_filter() {
    let decls = vec![mk_identity_object(), mk_two_param_object()];
    let mut config = SpecializeConfig::default();
    config.specialize_only.insert(mk_name("foo"));
    let candidates = find_candidates(&decls, &config);
    assert_eq!(candidates.len(), 1);
    assert!(candidates.contains(&mk_name("foo")));
}

// ═══════════════════════════════════════════════════════════════════════════
// Type Environment Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_build_type_env_params() {
    let decl = mk_caller_u64();
    let env = build_type_env(&decl);
    assert_eq!(env.get(&mk_var(10)), Some(&IRType::UInt64));
    // VDecl should also be collected
    assert_eq!(env.get(&mk_var(11)), Some(&IRType::Object));
}

#[test]
fn test_build_type_env_nested_vdecls() {
    let decl = IRDecl {
        name: mk_name("nested"),
        params: vec![(mk_var(0), IRType::Bool)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: mk_var(1),
            ty: IRType::UInt32,
            value: IRExpr::Lit(IRLiteral::UInt32(42)),
            rest: Box::new(IRBody::VDecl {
                var: mk_var(2),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(100)),
                rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(2)))),
            }),
        },
    };
    let env = build_type_env(&decl);
    assert_eq!(env.get(&mk_var(0)), Some(&IRType::Bool));
    assert_eq!(env.get(&mk_var(1)), Some(&IRType::UInt32));
    assert_eq!(env.get(&mk_var(2)), Some(&IRType::UInt64));
}

// ═══════════════════════════════════════════════════════════════════════════
// Call Site Collection Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_collect_call_sites_finds_apply() {
    let caller = mk_caller_u64();
    let env = build_type_env(&caller);
    let mut candidates = HashSet::new();
    candidates.insert(mk_name("foo"));
    let mut sites = Vec::new();
    collect_call_sites(&caller.body, &env, &candidates, &mut sites);
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].key.fn_name, mk_name("foo"));
    assert_eq!(sites[0].key.type_args, vec![Some(IRType::UInt64)]);
}

#[test]
fn test_collect_call_sites_no_match_for_non_candidate() {
    let caller = mk_caller_u64();
    let env = build_type_env(&caller);
    let candidates = HashSet::new(); // empty
    let mut sites = Vec::new();
    collect_call_sites(&caller.body, &env, &candidates, &mut sites);
    assert!(sites.is_empty());
}

#[test]
fn test_collect_call_sites_mixed_args() {
    let caller = mk_caller_mixed();
    let env = build_type_env(&caller);
    let mut candidates = HashSet::new();
    candidates.insert(mk_name("bar"));
    let mut sites = Vec::new();
    collect_call_sites(&caller.body, &env, &candidates, &mut sites);
    assert_eq!(sites.len(), 1);
    // First arg is UInt64 (scalar), second is Object (not scalar -> None)
    assert_eq!(sites[0].key.type_args, vec![Some(IRType::UInt64), None]);
}

#[test]
fn test_collect_call_sites_in_case_branch() {
    let mut candidates = HashSet::new();
    candidates.insert(mk_name("foo"));

    let decl = IRDecl {
        name: mk_name("case_caller"),
        params: vec![(mk_var(0), IRType::UInt64), (mk_var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: mk_var(1),
            alts: vec![IRAlt {
                ctor: CtorInfo {
                    name: mk_name("Ctor1"),
                    tag: 0,
                    num_scalars: 0,
                    num_objects: 0,
                    field_types: vec![],
                },
                body: Box::new(IRBody::VDecl {
                    var: mk_var(2),
                    ty: IRType::Object,
                    value: IRExpr::Apply {
                        fn_id: mk_fn_id("foo"),
                        args: vec![IRArg::Var(mk_var(0))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(2)))),
                }),
            }],
            default: None,
        },
    };

    let env = build_type_env(&decl);
    let mut sites = Vec::new();
    collect_call_sites(&decl.body, &env, &candidates, &mut sites);
    assert_eq!(sites.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Specialized Name Generation Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_specialized_name_single_type() {
    let name = specialized_name(&mk_name("foo"), &[Some(IRType::UInt64)]);
    let s = format!("{name}");
    assert!(s.contains("spec"));
    assert!(s.contains("u64"));
}

#[test]
fn test_specialized_name_mixed() {
    let name = specialized_name(&mk_name("bar"), &[Some(IRType::UInt64), None]);
    let s = format!("{name}");
    assert!(s.contains("spec"));
    assert!(s.contains("u64"));
    assert!(s.contains("_"));
}

#[test]
fn test_specialized_name_dedup_same_key() {
    let name1 = specialized_name(&mk_name("f"), &[Some(IRType::Bool)]);
    let name2 = specialized_name(&mk_name("f"), &[Some(IRType::Bool)]);
    assert_eq!(name1, name2);
}

#[test]
fn test_specialized_name_different_types_differ() {
    let name1 = specialized_name(&mk_name("f"), &[Some(IRType::Bool)]);
    let name2 = specialized_name(&mk_name("f"), &[Some(IRType::UInt64)]);
    assert_ne!(name1, name2);
}

// ═══════════════════════════════════════════════════════════════════════════
// Body Specialization Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_specialize_body_replaces_vdecl_type() {
    let body = IRBody::VDecl {
        var: mk_var(1),
        ty: IRType::Object,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(1)))),
    };
    let mut param_map = HashMap::new();
    param_map.insert(mk_var(1), IRType::UInt64);
    let result = specialize_body(&body, &param_map);

    match result {
        IRBody::VDecl { ty, .. } => assert_eq!(ty, IRType::UInt64),
        _ => panic!("expected VDecl"),
    }
}

#[test]
fn test_specialize_body_preserves_unmapped_type() {
    let body = IRBody::VDecl {
        var: mk_var(1),
        ty: IRType::Bool,
        value: IRExpr::Lit(IRLiteral::Bool(true)),
        rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(1)))),
    };
    let param_map = HashMap::new(); // empty
    let result = specialize_body(&body, &param_map);

    match result {
        IRBody::VDecl { ty, .. } => assert_eq!(ty, IRType::Bool),
        _ => panic!("expected VDecl"),
    }
}

#[test]
fn test_specialize_body_handles_case() {
    let body = IRBody::Case {
        scrutinee: mk_var(0),
        alts: vec![IRAlt {
            ctor: CtorInfo {
                name: mk_name("C"),
                tag: 0,
                num_scalars: 0,
                num_objects: 0,
                field_types: vec![],
            },
            body: Box::new(IRBody::Ret(IRArg::Var(mk_var(1)))),
        }],
        default: Some(Box::new(IRBody::Ret(IRArg::Var(mk_var(2))))),
    };
    let param_map = HashMap::new();
    let result = specialize_body(&body, &param_map);
    match result {
        IRBody::Case { alts, default, .. } => {
            assert_eq!(alts.len(), 1);
            assert!(default.is_some());
        }
        _ => panic!("expected Case"),
    }
}

#[test]
fn test_specialize_body_jdecl_params() {
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![(mk_var(5), IRType::Object)],
        body: Box::new(IRBody::Ret(IRArg::Var(mk_var(5)))),
        rest: Box::new(IRBody::Unreachable),
    };
    let mut param_map = HashMap::new();
    param_map.insert(mk_var(5), IRType::Float64);
    let result = specialize_body(&body, &param_map);
    match result {
        IRBody::JDecl { params, .. } => {
            assert_eq!(params[0].1, IRType::Float64);
        }
        _ => panic!("expected JDecl"),
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Full Pipeline (specialize_ir) Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_specialize_ir_generates_specialized_decl() {
    let decls = vec![mk_identity_object(), mk_caller_u64()];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);

    // Should have original 2 + 1 specialized
    assert_eq!(result.len(), 3);
    assert_eq!(stats.candidates_found, 1);
    assert_eq!(stats.specializations_generated, 1);
}

#[test]
fn test_specialize_ir_no_candidates_passthrough() {
    let decls = vec![mk_scalar_fn()];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);
    assert_eq!(result.len(), 1);
    assert_eq!(stats.candidates_found, 0);
    assert_eq!(stats.specializations_generated, 0);
}

#[test]
fn test_specialize_ir_deduplication() {
    // Two callers calling foo with the same type pattern
    let caller2 = IRDecl {
        name: mk_name("caller2"),
        params: vec![(mk_var(20), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(21),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("foo"),
                args: vec![IRArg::Var(mk_var(20))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(21)))),
        },
    };
    let decls = vec![mk_identity_object(), mk_caller_u64(), caller2];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);

    // Still only 1 specialization generated despite 2 call sites
    assert_eq!(stats.specializations_generated, 1);
    assert!(stats.dedup_hits > 0);
    // 3 original + 1 specialized
    assert_eq!(result.len(), 4);
}

#[test]
fn test_specialize_ir_max_per_fn_limit() {
    // Create many callers with different type args
    let foo = mk_two_param_object();
    let types = [
        IRType::UInt8,
        IRType::UInt16,
        IRType::UInt32,
        IRType::UInt64,
        IRType::Float32,
        IRType::Float64,
        IRType::Bool,
        IRType::USize,
    ];
    let mut decls = vec![foo];
    for (i, ty) in types.iter().enumerate() {
        let base = (i as u32 + 1) * 100;
        decls.push(IRDecl {
            name: mk_name(&format!("caller_{i}")),
            params: vec![(VarId(base), ty.clone()), (VarId(base + 1), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(base + 2),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: mk_fn_id("bar"),
                    args: vec![IRArg::Var(VarId(base)), IRArg::Var(VarId(base + 1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(base + 2)))),
            },
        });
    }

    let config = SpecializeConfig {
        max_specializations_per_fn: 3,
        ..Default::default()
    };
    let (_, stats) = specialize_ir(&decls, &config);
    assert!(stats.specializations_generated <= 3);
    assert!(stats.skipped_limit > 0);
}

#[test]
fn test_specialize_ir_rewrites_call_site() {
    let decls = vec![mk_identity_object(), mk_caller_u64()];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);

    assert!(stats.call_sites_rewritten > 0);

    // The caller's body should now reference the specialized function
    let caller = result.iter().find(|d| d.name == mk_name("caller")).unwrap();
    match &caller.body {
        IRBody::VDecl { value, .. } => match value {
            IRExpr::Apply { fn_id, .. } => {
                let name_str = format!("{}", fn_id.0);
                assert!(
                    name_str.contains("spec"),
                    "call should be rewritten to spec version, got: {name_str}"
                );
            }
            _ => panic!("expected Apply"),
        },
        _ => panic!("expected VDecl"),
    }
}

#[test]
fn test_specialize_ir_specialized_decl_has_correct_params() {
    let decls = vec![mk_identity_object(), mk_caller_u64()];
    let config = SpecializeConfig::default();
    let (result, _) = specialize_ir(&decls, &config);

    // Find the specialized decl
    let spec = result
        .iter()
        .find(|d| {
            let s = format!("{}", d.name);
            s.contains("spec")
        })
        .expect("should have a spec decl");

    // The specialized version should have UInt64 param instead of Object
    assert_eq!(spec.params.len(), 1);
    assert_eq!(spec.params[0].1, IRType::UInt64);
}

#[test]
fn test_specialize_ir_default_convenience() {
    let decls = vec![mk_identity_object(), mk_caller_u64()];
    let result = specialize_ir_default(&decls);
    assert_eq!(result.len(), 3);
}

#[test]
fn test_specialize_ir_empty_input() {
    let decls: Vec<IRDecl> = vec![];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);
    assert!(result.is_empty());
    assert_eq!(stats.candidates_found, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Configuration Tests
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_config_default_values() {
    let config = SpecializeConfig::default();
    assert_eq!(config.max_specializations_per_fn, 8);
    assert_eq!(config.max_total_specializations, 256);
    assert!(config.specialize_only.is_empty());
    assert!(config.skip_functions.is_empty());
}

#[test]
fn test_stats_default_zero() {
    let stats = SpecStats::default();
    assert_eq!(stats.candidates_found, 0);
    assert_eq!(stats.call_sites_analyzed, 0);
    assert_eq!(stats.specializations_generated, 0);
    assert_eq!(stats.call_sites_rewritten, 0);
    assert_eq!(stats.skipped_limit, 0);
    assert_eq!(stats.dedup_hits, 0);
}

// ═══════════════════════════════════════════════════════════════════════════
// Edge Cases
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn test_specialize_erased_arg_ignored() {
    // Call with an erased arg should not trigger specialization
    let foo = mk_identity_object();
    let caller = IRDecl {
        name: mk_name("erased_caller"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(0),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("foo"),
                args: vec![IRArg::Erased],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(0)))),
        },
    };
    let decls = vec![foo, caller];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);
    // No specialization because erased args have no concrete type
    assert_eq!(stats.specializations_generated, 0);
    assert_eq!(result.len(), 2);
}

#[test]
fn test_specialize_object_arg_not_specialized() {
    // Call with an Object-typed arg should not trigger specialization
    let foo = mk_identity_object();
    let caller = IRDecl {
        name: mk_name("obj_caller"),
        params: vec![(mk_var(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("foo"),
                args: vec![IRArg::Var(mk_var(10))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(11)))),
        },
    };
    let decls = vec![foo, caller];
    let config = SpecializeConfig::default();
    let (_, stats) = specialize_ir(&decls, &config);
    assert_eq!(stats.specializations_generated, 0);
}

#[test]
fn test_specialize_self_recursive_fn() {
    // A function calling itself should not infinite-loop in collection
    let rec_fn = IRDecl {
        name: mk_name("rec_fn"),
        params: vec![(mk_var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("rec_fn"),
                args: vec![IRArg::Var(mk_var(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(1)))),
        },
    };
    // The call uses an Object arg (from param), so no specialization
    let decls = vec![rec_fn];
    let config = SpecializeConfig::default();
    let (result, _) = specialize_ir(&decls, &config);
    assert_eq!(result.len(), 1);
}

#[test]
fn test_specialize_multiple_different_types() {
    // Two callers with different concrete types produce two specializations
    let foo = mk_identity_object();
    let caller_u64 = mk_caller_u64();
    let caller_bool = IRDecl {
        name: mk_name("caller_bool"),
        params: vec![(mk_var(30), IRType::Bool)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: mk_var(31),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: mk_fn_id("foo"),
                args: vec![IRArg::Var(mk_var(30))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(31)))),
        },
    };

    let decls = vec![foo, caller_u64, caller_bool];
    let config = SpecializeConfig::default();
    let (result, stats) = specialize_ir(&decls, &config);
    assert_eq!(stats.specializations_generated, 2);
    // 3 original + 2 specialized
    assert_eq!(result.len(), 5);
}

#[test]
fn test_ir_type_suffix_all_variants() {
    assert_eq!(ir_type_suffix(&IRType::Bool), "b");
    assert_eq!(ir_type_suffix(&IRType::UInt8), "u8");
    assert_eq!(ir_type_suffix(&IRType::UInt16), "u16");
    assert_eq!(ir_type_suffix(&IRType::UInt32), "u32");
    assert_eq!(ir_type_suffix(&IRType::UInt64), "u64");
    assert_eq!(ir_type_suffix(&IRType::USize), "us");
    assert_eq!(ir_type_suffix(&IRType::Float32), "f32");
    assert_eq!(ir_type_suffix(&IRType::Float64), "f64");
    assert_eq!(ir_type_suffix(&IRType::Object), "obj");
    assert_eq!(ir_type_suffix(&IRType::TObject), "tobj");
    assert_eq!(ir_type_suffix(&IRType::Erased), "e");
    assert_eq!(ir_type_suffix(&IRType::Void), "v");
    assert_eq!(ir_type_suffix(&IRType::Struct(vec![])), "st");
    assert_eq!(ir_type_suffix(&IRType::Union(vec![])), "un");
}

#[test]
fn test_specialize_body_inc_dec_passthrough() {
    let body = IRBody::Inc {
        var: mk_var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: mk_var(1),
            rest: Box::new(IRBody::Ret(IRArg::Var(mk_var(0)))),
        }),
    };
    let param_map = HashMap::new();
    let result = specialize_body(&body, &param_map);
    match result {
        IRBody::Inc { var, n, rest } => {
            assert_eq!(var, mk_var(0));
            assert_eq!(n, 1);
            match *rest {
                IRBody::Dec { var, .. } => assert_eq!(var, mk_var(1)),
                _ => panic!("expected Dec"),
            }
        }
        _ => panic!("expected Inc"),
    }
}

#[test]
fn test_specialize_body_unreachable() {
    let body = IRBody::Unreachable;
    let param_map = HashMap::new();
    let result = specialize_body(&body, &param_map);
    assert!(matches!(result, IRBody::Unreachable));
}

#[test]
fn test_resolve_arg_type_var() {
    let mut env = HashMap::new();
    env.insert(mk_var(0), IRType::UInt64);
    let result = resolve_arg_type(&IRArg::Var(mk_var(0)), &env);
    assert_eq!(result, Some(IRType::UInt64));
}

#[test]
fn test_resolve_arg_type_erased() {
    let env = HashMap::new();
    let result = resolve_arg_type(&IRArg::Erased, &env);
    assert_eq!(result, None);
}

#[test]
fn test_resolve_arg_type_unknown_var() {
    let env = HashMap::new();
    let result = resolve_arg_type(&IRArg::Var(mk_var(99)), &env);
    assert_eq!(result, None);
}
