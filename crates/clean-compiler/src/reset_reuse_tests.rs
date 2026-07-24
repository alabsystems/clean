// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the reset/reuse memory optimization pass.

use super::*;
use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

// ── Helpers ────────────────────────────────────────────────────────────

fn var(id: u32) -> VarId {
    VarId(id)
}

fn arg_var(id: u32) -> IRArg {
    IRArg::Var(VarId(id))
}

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn simple_ctor(tag: u32, num_objects: u32, num_scalars: u32) -> CtorInfo {
    let mut field_types = Vec::new();
    for _ in 0..num_objects {
        field_types.push(IRType::Object);
    }
    for _ in 0..num_scalars {
        field_types.push(IRType::UInt64);
    }
    CtorInfo {
        name: name(&format!("Ctor{tag}")),
        tag,
        num_scalars,
        num_objects,
        field_types,
    }
}

/// Build: `let var := Ctor(info, args); rest`
fn vdecl_ctor(v: u32, info: CtorInfo, args: Vec<IRArg>, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Ctor { info, args },
        rest: Box::new(rest),
    }
}

/// Build: `let var := Proj(idx, src); rest`
fn vdecl_proj(v: u32, idx: u32, src: u32, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx,
            ty: IRType::Object,
            arg: arg_var(src),
        },
        rest: Box::new(rest),
    }
}

fn ret(v: u32) -> IRBody {
    IRBody::Ret(arg_var(v))
}

fn make_decl(body: IRBody) -> IRDecl {
    IRDecl {
        name: name("test_fn"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    }
}

fn default_config() -> ResetReuseConfig {
    ResetReuseConfig::default()
}

// ── CtorLayout Tests ───────────────────────────────────────────────────

#[test]
fn test_ctor_layout_same_constructor_compatible() {
    let ctor = simple_ctor(0, 2, 1);
    assert!(layouts_compatible(&ctor, &ctor));
}

#[test]
fn test_ctor_layout_different_tag_same_size_compatible() {
    let ctor_a = simple_ctor(0, 2, 1);
    let ctor_b = simple_ctor(1, 2, 1);
    assert!(layouts_compatible(&ctor_a, &ctor_b));
}

#[test]
fn test_ctor_layout_different_num_objects_incompatible() {
    let ctor_a = simple_ctor(0, 2, 1);
    let ctor_b = simple_ctor(0, 3, 1);
    assert!(!layouts_compatible(&ctor_a, &ctor_b));
}

#[test]
fn test_ctor_layout_different_scalar_size_incompatible() {
    let a = CtorInfo {
        name: name("A"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt64],
    };
    let b = CtorInfo {
        name: name("B"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt8],
    };
    assert!(!layouts_compatible(&a, &b));
}

#[test]
fn test_ctor_layout_zero_fields_compatible() {
    let a = simple_ctor(0, 0, 0);
    let b = simple_ctor(1, 0, 0);
    assert!(layouts_compatible(&a, &b));
}

// ── Threshold Tests ────────────────────────────────────────────────────

#[test]
fn test_within_threshold_small_ctor_passes() {
    let ctor = simple_ctor(0, 2, 1);
    let config = default_config();
    assert!(within_threshold(&ctor, &config));
}

#[test]
fn test_within_threshold_too_many_objects_rejected() {
    let ctor = simple_ctor(0, 100, 0);
    let config = ResetReuseConfig {
        max_object_fields: 64,
        ..default_config()
    };
    assert!(!within_threshold(&ctor, &config));
}

#[test]
fn test_within_threshold_too_many_scalar_bytes_rejected() {
    // Each UInt64 is 8 bytes. 100 of them = 800 bytes.
    let ctor = simple_ctor(0, 0, 100);
    let config = ResetReuseConfig {
        max_scalar_bytes: 512,
        ..default_config()
    };
    assert!(!within_threshold(&ctor, &config));
}

// ── Config Disabled ────────────────────────────────────────────────────

#[test]
fn test_disabled_returns_unchanged() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let config = ResetReuseConfig {
        enabled: false,
        ..default_config()
    };
    let (result, stats) = insert_reset_reuse(&[decl], &config);
    assert_eq!(stats.pairs_inserted, 0);
    assert_eq!(result.len(), 1);
}

// ── Basic Reset/Reuse Insertion ────────────────────────────────────────

#[test]
fn test_simple_case_with_compatible_ctor_inserts_pair() {
    // case v0 of
    //   Ctor0(2 objs) =>
    //     let v1 := Ctor0(2 objs, []);
    //     ret v1
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (result, stats) = insert_reset_reuse(&[decl], &default_config());

    assert_eq!(stats.pairs_inserted, 1);
    assert_eq!(stats.alts_scanned, 1);
    // The result should have a Reset followed by a Reuse
    let result_body = &result[0].body;
    if let IRBody::Case { alts, .. } = result_body {
        if let IRBody::VDecl {
            value: IRExpr::Reset(rv),
            rest,
            ..
        } = &*alts[0].body
        {
            assert_eq!(*rv, var(0), "reset should target scrutinee");
            if let IRBody::VDecl {
                value: IRExpr::Reuse { .. },
                ..
            } = &**rest
            {
                // OK
            } else {
                panic!("expected Reuse after Reset");
            }
        } else {
            panic!("expected Reset VDecl in alt body");
        }
    } else {
        panic!("expected Case");
    }
}

#[test]
fn test_different_tag_same_layout_inserts_pair() {
    // Source is tag=0, target is tag=1, both have 2 objects + 0 scalars
    let source = simple_ctor(0, 2, 0);
    let target = simple_ctor(1, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: source.clone(),
            body: Box::new(vdecl_ctor(1, target, vec![], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

#[test]
fn test_incompatible_layout_no_insertion() {
    let source = simple_ctor(0, 2, 0);
    let target = simple_ctor(0, 3, 0); // different num_objects
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: source.clone(),
            body: Box::new(vdecl_ctor(1, target, vec![], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 0);
    assert_eq!(stats.size_mismatches, 1);
}

// ── Projection Interaction ─────────────────────────────────────────────

#[test]
fn test_proj_then_ctor_with_proj_vars_skips_reuse() {
    // case v0 of
    //   Ctor0(2 objs) =>
    //     let v1 := proj 0 v0;
    //     let v2 := Ctor0(2 objs, [v1]); // uses projected var
    //     ret v2
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_proj(
                1,
                0,
                0,
                vdecl_ctor(2, ctor.clone(), vec![arg_var(1)], ret(2)),
            )),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    // The Ctor uses v1 which is a projection from v0. The pass should skip.
    assert_eq!(stats.pairs_inserted, 0);
}

#[test]
fn test_proj_then_ctor_without_proj_vars_inserts() {
    // case v0 of
    //   Ctor0(2 objs) =>
    //     let v1 := proj 0 v0;
    //     let v2 := Ctor0(2 objs, [v3]); // v3 is NOT a projection from v0
    //     ret v2
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_proj(
                1,
                0,
                0,
                vdecl_ctor(2, ctor.clone(), vec![arg_var(3)], ret(2)),
            )),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Multiple Alternatives ──────────────────────────────────────────────

#[test]
fn test_multiple_alts_independent_reuse() {
    let ctor_a = simple_ctor(0, 2, 0);
    let ctor_b = simple_ctor(1, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: ctor_a.clone(),
                body: Box::new(vdecl_ctor(1, ctor_a.clone(), vec![], ret(1))),
            },
            IRAlt {
                ctor: ctor_b.clone(),
                body: Box::new(vdecl_ctor(2, ctor_b.clone(), vec![], ret(2))),
            },
        ],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 2);
    assert_eq!(stats.alts_scanned, 2);
}

#[test]
fn test_one_alt_compatible_one_not() {
    let ctor_a = simple_ctor(0, 2, 0);
    let ctor_b = simple_ctor(1, 2, 0);
    let ctor_c = simple_ctor(2, 3, 0); // incompatible with ctor_b
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: ctor_a.clone(),
                body: Box::new(vdecl_ctor(1, ctor_a.clone(), vec![], ret(1))),
            },
            IRAlt {
                ctor: ctor_b.clone(),
                body: Box::new(vdecl_ctor(2, ctor_c, vec![], ret(2))),
            },
        ],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
    assert_eq!(stats.size_mismatches, 1);
}

// ── First Match Wins ───────────────────────────────────────────────────

#[test]
fn test_first_compatible_ctor_gets_reuse() {
    // Two Ctor allocations in the same alt; only the first should be reused.
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(
                1,
                ctor.clone(),
                vec![],
                vdecl_ctor(2, ctor.clone(), vec![], ret(2)),
            )),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (result, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(
        stats.pairs_inserted, 1,
        "only the first Ctor should be reused"
    );

    // Verify structure: Reset -> Reuse -> (second Ctor unchanged)
    if let IRBody::Case { alts, .. } = &result[0].body {
        if let IRBody::VDecl {
            value: IRExpr::Reset(_),
            rest,
            ..
        } = &*alts[0].body
        {
            if let IRBody::VDecl {
                value: IRExpr::Reuse { .. },
                rest: inner,
                ..
            } = &**rest
            {
                if let IRBody::VDecl {
                    value: IRExpr::Ctor { .. },
                    ..
                } = &**inner
                {
                    // Correct: second Ctor is still a plain Ctor.
                } else {
                    panic!("expected second allocation to remain a Ctor");
                }
            } else {
                panic!("expected first allocation to be Reuse");
            }
        } else {
            panic!("expected Reset at top of alt body");
        }
    }
}

// ── No Case = No Transformation ────────────────────────────────────────

#[test]
fn test_no_case_no_transformation() {
    let ctor = simple_ctor(0, 2, 0);
    let body = vdecl_ctor(1, ctor, vec![], ret(1));
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 0);
    assert_eq!(stats.alts_scanned, 0);
}

// ── Return / Unreachable in Alt Body ───────────────────────────────────

#[test]
fn test_unreachable_alt_body_no_crash() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(IRBody::Unreachable),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 0);
}

#[test]
fn test_ret_only_alt_body_no_crash() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(ret(0)),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 0);
}

// ── Nested Cases ───────────────────────────────────────────────────────

#[test]
fn test_nested_case_inner_gets_reuse() {
    let outer_ctor = simple_ctor(0, 1, 0);
    let inner_ctor = simple_ctor(1, 3, 0);

    // case v0 of
    //   Ctor0(1 obj) =>
    //     let v1 := proj 0 v0;
    //     case v1 of
    //       Ctor1(3 obj) =>
    //         let v2 := Ctor1(3 obj, []);
    //         ret v2
    let inner_case = IRBody::Case {
        scrutinee: var(1),
        alts: vec![IRAlt {
            ctor: inner_ctor.clone(),
            body: Box::new(vdecl_ctor(2, inner_ctor.clone(), vec![], ret(2))),
        }],
        default: None,
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: outer_ctor.clone(),
            body: Box::new(vdecl_proj(1, 0, 0, inner_case)),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    // Outer: no compatible Ctor to reuse. Inner: yes.
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Default Case Branch ────────────────────────────────────────────────

#[test]
fn test_default_branch_gets_recursed() {
    let ctor = simple_ctor(0, 2, 0);
    // The default branch itself is not a Case alt (no source ctor to reset),
    // but if it contains a nested Case, that inner Case can still be optimized.
    let inner_case = IRBody::Case {
        scrutinee: var(1),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(2, ctor.clone(), vec![], ret(2))),
        }],
        default: None,
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![],
        default: Some(Box::new(vdecl_proj(1, 0, 0, inner_case))),
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Multiple Declarations ──────────────────────────────────────────────

#[test]
fn test_multiple_decls_each_transformed() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
        }],
        default: None,
    };
    let decl1 = make_decl(body.clone());
    let mut decl2 = make_decl(body);
    decl2.name = name("test_fn2");

    let (result, stats) = insert_reset_reuse(&[decl1, decl2], &default_config());
    assert_eq!(result.len(), 2);
    assert_eq!(stats.pairs_inserted, 2);
}

// ── Inc/Dec Before Ctor ────────────────────────────────────────────────

#[test]
fn test_inc_dec_before_ctor_still_finds_reuse() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(IRBody::Inc {
                var: var(3),
                n: 1,
                rest: Box::new(IRBody::Dec {
                    var: var(4),
                    rest: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
                }),
            }),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Erased Args ────────────────────────────────────────────────────────

#[test]
fn test_ctor_with_erased_args_can_reuse() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![IRArg::Erased], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Stats Tracking ─────────────────────────────────────────────────────

#[test]
fn test_stats_ctors_examined_counts_all() {
    let ctor_a = simple_ctor(0, 2, 0);
    let ctor_b = simple_ctor(1, 3, 0); // incompatible
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor_a.clone(),
            body: Box::new(vdecl_ctor(
                1,
                ctor_b,
                vec![],
                vdecl_ctor(2, ctor_a.clone(), vec![], ret(2)),
            )),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse(&[decl], &default_config());
    // First Ctor examined (size mismatch), second Ctor examined (compatible).
    assert_eq!(stats.ctors_examined, 2);
    assert_eq!(stats.size_mismatches, 1);
    assert_eq!(stats.pairs_inserted, 1);
}

// ── Single Declaration API ─────────────────────────────────────────────

#[test]
fn test_insert_reset_reuse_single_api() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
        }],
        default: None,
    };
    let decl = make_decl(body);
    let (_, stats) = insert_reset_reuse_single(&decl, &default_config());
    assert_eq!(stats.pairs_inserted, 1);
}

// ── find_max_var_id ────────────────────────────────────────────────────

#[test]
fn test_find_max_var_id_simple() {
    let body = IRBody::VDecl {
        var: var(5),
        ty: IRType::Object,
        value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(0)),
        rest: Box::new(IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(1)),
            rest: Box::new(ret(10)),
        }),
    };
    assert_eq!(find_max_var_id(&body), 10);
}

#[test]
fn test_find_max_var_id_in_case() {
    let ctor = simple_ctor(0, 1, 0);
    let body = IRBody::Case {
        scrutinee: var(3),
        alts: vec![IRAlt {
            ctor,
            body: Box::new(IRBody::VDecl {
                var: var(20),
                ty: IRType::Object,
                value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(0)),
                rest: Box::new(ret(20)),
            }),
        }],
        default: Some(Box::new(ret(3))),
    };
    assert_eq!(find_max_var_id(&body), 20);
}

// ── Collect Projection Vars ────────────────────────────────────────────

#[test]
fn test_collect_projection_vars_proj() {
    let body = vdecl_proj(1, 0, 0, vdecl_proj(2, 1, 0, ret(2)));
    let vars = collect_projection_vars(&body, var(0));
    assert!(vars.contains(&var(1)));
    assert!(vars.contains(&var(2)));
}

#[test]
fn test_collect_projection_vars_non_proj() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
        rest: Box::new(ret(1)),
    };
    let vars = collect_projection_vars(&body, var(0));
    assert!(vars.is_empty());
}
