// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended closure conversion optimizations.
//!
//! Part of #3084 - Runtime closure support.

use crate::closure_convert_ext::*;
use crate::ir::{
    CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use clean_kernel::Name;

// Test helpers

fn var(n: u32) -> VarId {
    VarId(n)
}

fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}

fn ret_var(n: u32) -> IRBody {
    IRBody::Ret(IRArg::Var(var(n)))
}

fn simple_ctor_info() -> CtorInfo {
    CtorInfo {
        name: Name::from_string("Nat.zero"),
        tag: 0,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    }
}

fn make_decl(name: &str, params: Vec<(VarId, IRType)>, body: IRBody) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params,
        return_type: IRType::Object,
        body,
    }
}

fn partial_apply_body(
    result_var: u32,
    fn_name: &str,
    arity: u16,
    args: Vec<IRArg>,
    rest: IRBody,
) -> IRBody {
    IRBody::VDecl {
        var: var(result_var),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id(fn_name),
            arity,
            args,
        },
        rest: Box::new(rest),
    }
}

fn closure_apply_body(result_var: u32, closure_var: u32, args: Vec<IRArg>, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(result_var),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(var(closure_var)),
            args,
        },
        rest: Box::new(rest),
    }
}

// Config tests

#[test]
fn test_config_default_values() {
    let config = ClosureConvertExtConfig::default();
    assert!(config.inline_small_closures);
    assert_eq!(config.small_closure_threshold, 5);
    assert!(!config.defunctionalize);
    assert!(config.hoist_invariant_closures);
}

#[test]
fn test_config_custom_values() {
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        small_closure_threshold: 10,
        defunctionalize: true,
        hoist_invariant_closures: false,
    };
    assert!(!config.inline_small_closures);
    assert_eq!(config.small_closure_threshold, 10);
    assert!(config.defunctionalize);
    assert!(!config.hoist_invariant_closures);
}

// Stats tests

#[test]
fn test_stats_default() {
    let stats = ClosureConvertExtStats::default();
    assert_eq!(stats.closures_converted, 0);
    assert_eq!(stats.closures_inlined, 0);
    assert_eq!(stats.closures_hoisted, 0);
    assert_eq!(stats.defunctionalized, 0);
}

#[test]
fn test_stats_equality() {
    let a = ClosureConvertExtStats {
        closures_converted: 1,
        closures_inlined: 2,
        closures_hoisted: 3,
        defunctionalized: 4,
        paps_generated: 5,
        mutual_groups: 6,
    };
    let b = a.clone();
    assert_eq!(a, b);
}

// identify_closures tests

#[test]
fn test_identify_closures_empty_body() {
    let body = ret_var(0);
    let closures = identify_closures(&body);
    assert!(closures.is_empty());
}

#[test]
fn test_identify_closures_single_partial_apply() {
    let body = partial_apply_body(1, "f", 3, vec![IRArg::Var(var(10))], ret_var(1));
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
    assert_eq!(closures[0].var, var(1));
    assert_eq!(closures[0].captured, vec![var(10)]);
    assert_eq!(closures[0].arity, 3);
}

#[test]
fn test_identify_closures_zero_captures() {
    let body = partial_apply_body(1, "f", 2, vec![], ret_var(1));
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
    assert!(closures[0].captured.is_empty());
}

#[test]
fn test_identify_closures_multiple() {
    let body = partial_apply_body(
        1,
        "f",
        3,
        vec![IRArg::Var(var(10))],
        partial_apply_body(
            2,
            "g",
            4,
            vec![IRArg::Var(var(10)), IRArg::Var(var(11))],
            ret_var(2),
        ),
    );
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 2);
    assert_eq!(closures[0].captured.len(), 1);
    assert_eq!(closures[1].captured.len(), 2);
}

#[test]
fn test_identify_closures_erased_args_not_captured() {
    let body = partial_apply_body(
        1,
        "f",
        3,
        vec![IRArg::Var(var(10)), IRArg::Erased, IRArg::Var(var(11))],
        ret_var(1),
    );
    let closures = identify_closures(&body);
    assert_eq!(closures[0].captured, vec![var(10), var(11)]);
}

#[test]
fn test_identify_closures_in_case_alt() {
    let body = IRBody::Case {
        scrutinee: var(1),
        alts: vec![IRAlt {
            ctor: simple_ctor_info(),
            body: Box::new(partial_apply_body(
                2,
                "g",
                2,
                vec![IRArg::Var(var(1))],
                ret_var(2),
            )),
        }],
        default: None,
    };
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
}

#[test]
fn test_identify_closures_in_case_default() {
    let body = IRBody::Case {
        scrutinee: var(1),
        alts: vec![],
        default: Some(Box::new(partial_apply_body(2, "g", 2, vec![], ret_var(2)))),
    };
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
}

#[test]
fn test_identify_closures_in_join_point() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![(var(5), IRType::Object)],
        body: Box::new(partial_apply_body(
            6,
            "h",
            3,
            vec![IRArg::Var(var(5))],
            ret_var(6),
        )),
        rest: Box::new(ret_var(1)),
    };
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
}

#[test]
fn test_identify_closures_in_inc_rest() {
    let body = IRBody::Inc {
        var: var(1),
        n: 1,
        rest: Box::new(partial_apply_body(
            2,
            "f",
            2,
            vec![IRArg::Var(var(1))],
            ret_var(2),
        )),
    };
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
}

#[test]
fn test_identify_closures_non_partial_apply_ignored() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(ret_var(1)),
    };
    let closures = identify_closures(&body);
    assert!(closures.is_empty());
}

// is_small_closure tests

#[test]
fn test_is_small_closure_below_threshold() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![],
        arity: 2,
        body_size: 3,
    };
    assert!(is_small_closure(&info, 5));
}

#[test]
fn test_is_small_closure_at_threshold() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![],
        arity: 2,
        body_size: 5,
    };
    assert!(is_small_closure(&info, 5));
}

#[test]
fn test_is_small_closure_above_threshold() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![],
        arity: 2,
        body_size: 6,
    };
    assert!(!is_small_closure(&info, 5));
}

#[test]
fn test_is_small_closure_zero_threshold() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![],
        arity: 2,
        body_size: 0,
    };
    assert!(is_small_closure(&info, 0));
}

// body_size tests

#[test]
fn test_body_size_ret() {
    assert_eq!(body_size(&ret_var(0)), 1);
}

#[test]
fn test_body_size_unreachable() {
    assert_eq!(body_size(&IRBody::Unreachable), 1);
}

#[test]
fn test_body_size_vdecl_chain() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(1)),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(2)),
            rest: Box::new(ret_var(2)),
        }),
    };
    assert_eq!(body_size(&body), 3);
}

#[test]
fn test_body_size_case_with_alts() {
    let body = IRBody::Case {
        scrutinee: var(1),
        alts: vec![
            IRAlt {
                ctor: simple_ctor_info(),
                body: Box::new(ret_var(2)),
            },
            IRAlt {
                ctor: simple_ctor_info(),
                body: Box::new(ret_var(3)),
            },
        ],
        default: Some(Box::new(ret_var(4))),
    };
    // 1 (case) + 1 (alt1 ret) + 1 (alt2 ret) + 1 (default ret) = 4
    assert_eq!(body_size(&body), 4);
}

#[test]
fn test_body_size_inc_dec_chain() {
    let body = IRBody::Inc {
        var: var(1),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(1),
            rest: Box::new(ret_var(1)),
        }),
    };
    assert_eq!(body_size(&body), 3);
}

#[test]
fn test_body_size_jdecl() {
    let body = IRBody::JDecl {
        jp: JoinPointId(0),
        params: vec![],
        body: Box::new(ret_var(1)),
        rest: Box::new(ret_var(2)),
    };
    // 1 (jdecl) + 1 (jp body ret) + 1 (rest ret) = 3
    assert_eq!(body_size(&body), 3);
}

#[test]
fn test_body_size_jmp() {
    let body = IRBody::Jmp {
        jp: JoinPointId(0),
        args: vec![IRArg::Var(var(1))],
    };
    assert_eq!(body_size(&body), 1);
}

// inline_closure_at_call_site tests

#[test]
fn test_inline_closure_at_call_site_found() {
    let replacement = ret_var(99);
    let mut body = closure_apply_body(2, 1, vec![IRArg::Var(var(3))], ret_var(2));
    let result = inline_closure_at_call_site(&mut body, var(1), &replacement);
    assert!(result);
}

#[test]
fn test_inline_closure_at_call_site_not_found() {
    let replacement = ret_var(99);
    let mut body = ret_var(1);
    let result = inline_closure_at_call_site(&mut body, var(1), &replacement);
    assert!(!result);
}

#[test]
fn test_inline_closure_wrong_target() {
    let replacement = ret_var(99);
    let mut body = closure_apply_body(
        2,
        5, // different closure var
        vec![],
        ret_var(2),
    );
    let result = inline_closure_at_call_site(&mut body, var(1), &replacement);
    assert!(!result);
}

// hoist_invariant_closure tests

#[test]
fn test_hoist_invariant_closure_zero_captures() {
    // Body: let v1 = PartialApply(g, 2, []); let v2 = ClosureApply(v1, [v3, v4]); ret v2
    // This uses v1 in an exact ClosureApply with arity 2, so hoisting succeeds.
    let mut decl = make_decl(
        "f",
        vec![(var(3), IRType::Object), (var(4), IRType::Object)],
        partial_apply_body(
            1,
            "g",
            2,
            vec![],
            closure_apply_body(
                2,
                1,
                vec![IRArg::Var(var(3)), IRArg::Var(var(4))],
                ret_var(2),
            ),
        ),
    );
    let hoisted = hoist_invariant_closure(&mut decl, var(1));
    assert!(hoisted.is_some());
    let h = hoisted.unwrap();
    assert!(h.name.to_string().contains("_closure"));
    assert_eq!(h.params.len(), 2);
}

#[test]
fn test_hoist_invariant_closure_with_captures_returns_none() {
    let mut decl = make_decl(
        "f",
        vec![(var(10), IRType::Object)],
        partial_apply_body(1, "g", 3, vec![IRArg::Var(var(10))], ret_var(1)),
    );
    let hoisted = hoist_invariant_closure(&mut decl, var(1));
    assert!(hoisted.is_none());
}

#[test]
fn test_hoist_invariant_closure_nonexistent_var() {
    let mut decl = make_decl("f", vec![], ret_var(0));
    let hoisted = hoist_invariant_closure(&mut decl, var(99));
    assert!(hoisted.is_none());
}

#[test]
fn test_hoist_invariant_closure_ret_use_returns_none() {
    // Closure var used in Ret (not ClosureApply), so hoisting should fail.
    let mut decl = make_decl(
        "f",
        vec![],
        partial_apply_body(1, "g", 2, vec![], ret_var(1)),
    );
    let hoisted = hoist_invariant_closure(&mut decl, var(1));
    assert!(hoisted.is_none());
}

#[test]
fn test_hoist_invariant_closure_removes_vdecl() {
    let mut decl = make_decl(
        "f",
        vec![(var(3), IRType::Object), (var(4), IRType::Object)],
        partial_apply_body(
            1,
            "g",
            2,
            vec![],
            closure_apply_body(
                2,
                1,
                vec![IRArg::Var(var(3)), IRArg::Var(var(4))],
                ret_var(2),
            ),
        ),
    );
    let result = hoist_invariant_closure(&mut decl, var(1));
    assert!(result.is_some());
    // After hoisting, the PartialApply VDecl is removed and the ClosureApply
    // is rewritten to a direct Apply to the hoisted wrapper.
    match &decl.body {
        IRBody::VDecl {
            value: IRExpr::Apply { fn_id, .. },
            ..
        } => {
            assert!(fn_id.0.to_string().contains("_closure"));
        }
        _ => panic!("expected VDecl with Apply after hoisting"),
    }
}

// defunctionalize_closure tests

#[test]
fn test_defunctionalize_closure_single_capture() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![var(10)],
        arity: 3,
        body_size: 5,
    };
    let (decl, env_ty) = defunctionalize_closure(&info);
    assert!(decl.name.to_string().contains("defun.apply"));
    assert_eq!(env_ty, IRType::Struct(vec![IRType::Object]));
    // params: env + (arity - captures) = 1 + (3 - 1) = 3
    assert_eq!(decl.params.len(), 3);
}

#[test]
fn test_defunctionalize_closure_no_captures() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![],
        arity: 2,
        body_size: 3,
    };
    let (decl, env_ty) = defunctionalize_closure(&info);
    assert_eq!(env_ty, IRType::Struct(vec![]));
    // params: env + (arity - 0) = 1 + 2 = 3
    assert_eq!(decl.params.len(), 3);
}

#[test]
fn test_defunctionalize_closure_multiple_captures() {
    let info = ClosureInfo {
        var: var(1),
        captured: vec![var(10), var(11), var(12)],
        arity: 5,
        body_size: 10,
    };
    let (decl, env_ty) = defunctionalize_closure(&info);
    assert_eq!(
        env_ty,
        IRType::Struct(vec![IRType::Object, IRType::Object, IRType::Object])
    );
    // params: env + (5 - 3) = 1 + 2 = 3
    assert_eq!(decl.params.len(), 3);
    assert_eq!(decl.return_type, IRType::Object);
}

#[test]
fn test_defunctionalize_closure_saturated_arity() {
    // captures == arity: remaining = 0
    let info = ClosureInfo {
        var: var(1),
        captured: vec![var(10), var(11)],
        arity: 2,
        body_size: 3,
    };
    let (decl, _) = defunctionalize_closure(&info);
    // params: env + 0 = 1
    assert_eq!(decl.params.len(), 1);
}

// convert_closures_ext integration tests

#[test]
fn test_convert_closures_ext_default_empty() {
    let mut decls = vec![];
    let stats = convert_closures_ext_default(&mut decls);
    assert_eq!(stats, ClosureConvertExtStats::default());
    assert!(decls.is_empty());
}

#[test]
fn test_convert_closures_ext_no_closures() {
    let mut decls = vec![make_decl("f", vec![(var(1), IRType::Object)], ret_var(1))];
    let stats = convert_closures_ext_default(&mut decls);
    assert_eq!(stats.closures_converted, 0);
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_convert_closures_ext_hoist_zero_capture() {
    let mut decls = vec![make_decl(
        "f",
        vec![(var(3), IRType::Object), (var(4), IRType::Object)],
        partial_apply_body(
            1,
            "g",
            2,
            vec![],
            closure_apply_body(
                2,
                1,
                vec![IRArg::Var(var(3)), IRArg::Var(var(4))],
                ret_var(2),
            ),
        ),
    )];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: true,
        defunctionalize: false,
        ..Default::default()
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.closures_converted, 1);
    assert_eq!(stats.closures_hoisted, 1);
    // Original + hoisted
    assert_eq!(decls.len(), 2);
}

#[test]
fn test_convert_closures_ext_defunctionalize() {
    // arity=3, 1 capture -> remaining=2: ClosureApply needs 2 args
    let mut decls = vec![make_decl(
        "f",
        vec![
            (var(10), IRType::Object),
            (var(11), IRType::Object),
            (var(12), IRType::Object),
        ],
        partial_apply_body(
            1,
            "g",
            3,
            vec![IRArg::Var(var(10))],
            closure_apply_body(
                2,
                1,
                vec![IRArg::Var(var(11)), IRArg::Var(var(12))],
                ret_var(2),
            ),
        ),
    )];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: false,
        defunctionalize: true,
        ..Default::default()
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.closures_converted, 1);
    assert_eq!(stats.defunctionalized, 1);
    // Original + defunc apply decl
    assert_eq!(decls.len(), 2);
}

#[test]
fn test_convert_closures_ext_all_disabled() {
    let mut decls = vec![make_decl(
        "f",
        vec![(var(10), IRType::Object)],
        partial_apply_body(1, "g", 3, vec![IRArg::Var(var(10))], ret_var(1)),
    )];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: false,
        defunctionalize: false,
        small_closure_threshold: 0,
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.closures_converted, 1);
    assert_eq!(stats.closures_inlined, 0);
    assert_eq!(stats.closures_hoisted, 0);
    assert_eq!(stats.defunctionalized, 0);
    assert_eq!(stats.paps_generated, 0);
    assert_eq!(stats.mutual_groups, 0);
    assert_eq!(decls.len(), 1);
}

#[test]
fn test_convert_closures_ext_multiple_decls() {
    let mut decls = vec![
        // First decl: zero-capture closure used in ClosureApply -> hoistable
        make_decl(
            "f",
            vec![(var(3), IRType::Object), (var(4), IRType::Object)],
            partial_apply_body(
                1,
                "g",
                2,
                vec![],
                closure_apply_body(
                    2,
                    1,
                    vec![IRArg::Var(var(3)), IRArg::Var(var(4))],
                    ret_var(2),
                ),
            ),
        ),
        // Second decl: closure with captures, returned directly -> defunctionalizable
        make_decl(
            "h",
            vec![(var(10), IRType::Object)],
            partial_apply_body(1, "k", 3, vec![IRArg::Var(var(10))], ret_var(1)),
        ),
    ];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: true,
        defunctionalize: true,
        ..Default::default()
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.closures_converted, 2);
    assert_eq!(stats.closures_hoisted, 1); // first decl
                                           // Second decl: defunctionalize requires exact calls, but ret_var(1) isn't one
                                           // so it won't defunctionalize either
    assert_eq!(stats.defunctionalized, 0);
}

// Edge cases

#[test]
fn test_body_size_deeply_nested() {
    // Chain: set -> set_tag -> uset -> ret
    let body = IRBody::Set {
        var: var(1),
        idx: 0,
        value: var(2),
        rest: Box::new(IRBody::SetTag {
            var: var(1),
            tag: 1,
            rest: Box::new(IRBody::USet {
                var: var(1),
                idx: 0,
                value: var(3),
                rest: Box::new(ret_var(1)),
            }),
        }),
    };
    assert_eq!(body_size(&body), 4);
}

#[test]
fn test_body_size_sset() {
    let body = IRBody::SSet {
        var: var(1),
        n: 0,
        offset: 0,
        value: var(2),
        ty: IRType::UInt64,
        rest: Box::new(ret_var(1)),
    };
    assert_eq!(body_size(&body), 2);
}

#[test]
fn test_identify_closures_in_dec_rest() {
    let body = IRBody::Dec {
        var: var(1),
        rest: Box::new(partial_apply_body(2, "f", 2, vec![], ret_var(2))),
    };
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
}

#[test]
fn test_closure_info_body_size_accuracy() {
    // The body_size in ClosureInfo should reflect the rest after the VDecl,
    // not the entire body.
    let rest = IRBody::Inc {
        var: var(1),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(1),
            rest: Box::new(ret_var(1)),
        }),
    };
    let body = partial_apply_body(2, "f", 2, vec![IRArg::Var(var(1))], rest);
    let closures = identify_closures(&body);
    assert_eq!(closures.len(), 1);
    // rest is: inc -> dec -> ret = 3 nodes
    assert_eq!(closures[0].body_size, 3);
}

// detect_mutual_groups tests

#[test]
fn test_detect_mutual_groups_empty() {
    let body = ret_var(0);
    let groups = detect_mutual_groups(&body);
    assert!(groups.is_empty());
}

#[test]
fn test_detect_mutual_groups_no_mutual_refs() {
    // Two closures that don't reference each other
    let body = partial_apply_body(
        1,
        "f",
        2,
        vec![IRArg::Var(var(10))],
        partial_apply_body(2, "g", 2, vec![IRArg::Var(var(11))], ret_var(2)),
    );
    let groups = detect_mutual_groups(&body);
    assert!(groups.is_empty());
}

#[test]
fn test_detect_mutual_groups_with_mutual_ref() {
    // v1 = PartialApply(f, 2, [v2]) -- v1 captures v2
    // v2 = PartialApply(g, 2, [v1]) -- v2 captures v1
    // This is a mutual reference: v1 and v2 reference each other.
    let body = partial_apply_body(
        1,
        "f",
        2,
        vec![IRArg::Var(var(2))],
        partial_apply_body(2, "g", 2, vec![IRArg::Var(var(1))], ret_var(2)),
    );
    let groups = detect_mutual_groups(&body);
    assert_eq!(groups.len(), 1);
    assert!(groups[0].members.contains(&var(1)));
    assert!(groups[0].members.contains(&var(2)));
    assert!(groups[0].shared_captures.is_empty());
}

#[test]
fn test_detect_mutual_groups_one_way_ref_not_mutual() {
    // v1 captures v10 (not a closure), v2 captures v1
    // Only v2 -> v1, not v1 -> v2, but still forms a group since v2 refs a closure var
    let body = partial_apply_body(
        1,
        "f",
        2,
        vec![IRArg::Var(var(10))],
        partial_apply_body(2, "g", 2, vec![IRArg::Var(var(1))], ret_var(2)),
    );
    let groups = detect_mutual_groups(&body);
    // v2 captures v1 (a closure var) so it forms a group {v2, v1}
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].shared_captures, vec![var(10)]);
}

// generate_pap_wrapper tests

#[test]
fn test_generate_pap_wrapper_basic() {
    let fid = fn_id("add");
    let pap = generate_pap_wrapper(&fid, 3, 1);
    assert!(pap.is_some());
    let decl = pap.unwrap();
    assert!(decl.name.to_string().contains("_pap_1"));
    assert_eq!(decl.params.len(), 1);
    assert_eq!(decl.return_type, IRType::Object);
}

#[test]
fn test_generate_pap_wrapper_two_applied() {
    let fid = fn_id("add");
    let pap = generate_pap_wrapper(&fid, 4, 2);
    assert!(pap.is_some());
    let decl = pap.unwrap();
    assert!(decl.name.to_string().contains("_pap_2"));
    assert_eq!(decl.params.len(), 2);
}

#[test]
fn test_generate_pap_wrapper_saturated_returns_none() {
    let fid = fn_id("f");
    let pap = generate_pap_wrapper(&fid, 3, 3);
    assert!(pap.is_none());
}

#[test]
fn test_generate_pap_wrapper_over_saturated_returns_none() {
    let fid = fn_id("f");
    let pap = generate_pap_wrapper(&fid, 2, 5);
    assert!(pap.is_none());
}

#[test]
fn test_generate_pap_wrapper_zero_applied_returns_none() {
    let fid = fn_id("f");
    let pap = generate_pap_wrapper(&fid, 3, 0);
    assert!(pap.is_none());
}

#[test]
fn test_generate_pap_wrapper_body_is_partial_apply() {
    let fid = fn_id("mul");
    let pap = generate_pap_wrapper(&fid, 3, 2).unwrap();
    // Body should be: let vN = PartialApply(mul, 3, [v0, v1]); ret vN
    match &pap.body {
        IRBody::VDecl {
            value:
                IRExpr::PartialApply {
                    fn_id: f,
                    arity,
                    args,
                },
            rest,
            ..
        } => {
            assert_eq!(f, &fn_id("mul"));
            assert_eq!(*arity, 3);
            assert_eq!(args.len(), 2);
            assert!(matches!(rest.as_ref(), IRBody::Ret(_)));
        }
        _ => panic!("expected VDecl with PartialApply"),
    }
}

// Stats new fields tests

#[test]
fn test_stats_new_fields_default() {
    let stats = ClosureConvertExtStats::default();
    assert_eq!(stats.paps_generated, 0);
    assert_eq!(stats.mutual_groups, 0);
}

#[test]
fn test_stats_new_fields_equality() {
    let a = ClosureConvertExtStats {
        closures_converted: 1,
        closures_inlined: 2,
        closures_hoisted: 3,
        defunctionalized: 4,
        paps_generated: 5,
        mutual_groups: 6,
    };
    let b = a.clone();
    assert_eq!(a, b);
}

// PAP phase integration test

#[test]
fn test_convert_closures_ext_pap_generation() {
    // Decl "f" with a PartialApply to "g" (arity 3, 1 capture).
    // "g" must be in fn_map for PAP to generate.
    let mut decls = vec![
        make_decl(
            "g",
            vec![
                (var(0), IRType::Object),
                (var(1), IRType::Object),
                (var(2), IRType::Object),
            ],
            ret_var(0),
        ),
        make_decl(
            "f",
            vec![(var(10), IRType::Object)],
            partial_apply_body(1, "g", 3, vec![IRArg::Var(var(10))], ret_var(1)),
        ),
    ];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: false,
        defunctionalize: false,
        ..Default::default()
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.paps_generated, 1);
    // Original 2 + 1 PAP wrapper
    assert_eq!(decls.len(), 3);
    assert!(decls[2].name.to_string().contains("_pap_1"));
}

#[test]
fn test_convert_closures_ext_mutual_group_counting() {
    // Two closures that mutually reference each other
    let mut decls = vec![make_decl(
        "f",
        vec![],
        partial_apply_body(
            1,
            "a",
            2,
            vec![IRArg::Var(var(2))],
            partial_apply_body(2, "b", 2, vec![IRArg::Var(var(1))], ret_var(2)),
        ),
    )];
    let config = ClosureConvertExtConfig {
        inline_small_closures: false,
        hoist_invariant_closures: false,
        defunctionalize: false,
        ..Default::default()
    };
    let stats = convert_closures_ext(&mut decls, &config);
    assert_eq!(stats.mutual_groups, 1);
}
