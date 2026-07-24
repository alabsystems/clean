// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended reset/reuse memory optimization pass.

use crate::ir::{CtorInfo, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use crate::reset_reuse_ext::*;
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

fn vdecl_ctor(v: u32, info: CtorInfo, args: Vec<IRArg>, rest: IRBody) -> IRBody {
    IRBody::VDecl {
        var: var(v),
        ty: IRType::Object,
        value: IRExpr::Ctor { info, args },
        rest: Box::new(rest),
    }
}

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

fn default_config() -> ResetReuseExtConfig {
    ResetReuseExtConfig::default()
}

// ── ResetReuseExtConfig ────────────────────────────────────────────────

#[test]
fn test_config_default_values() {
    let cfg = ResetReuseExtConfig::default();
    assert_eq!(cfg.max_reuse_distance, 5);
    assert!(cfg.enable_multi_reset);
    assert!(cfg.enable_partial_reuse);
    assert!(cfg.track_field_liveness);
}

// ── ResetReuseExtStats ─────────────────────────────────────────────────

#[test]
fn test_stats_default_all_zero() {
    let stats = ResetReuseExtStats::default();
    assert_eq!(stats.resets_inserted, 0);
    assert_eq!(stats.reuses_inserted, 0);
    assert_eq!(stats.multi_resets, 0);
    assert_eq!(stats.partial_reuses, 0);
    assert_eq!(stats.candidates_rejected, 0);
}

// ── is_compatible_reuse ────────────────────────────────────────────────

fn make_cand(tag: u32, num_obj: u32, num_sc: u32, dist: usize) -> ReuseCandidate {
    let info = simple_ctor(tag, num_obj, num_sc);
    ReuseCandidate {
        source_var: var(0),
        ctor_tag: tag as u16,
        num_fields: info.field_types.len(),
        field_types: info.field_types.clone(),
        distance_to_use: dist,
        ctor_info: info,
    }
}

fn make_alloc(tag: u32, num_obj: u32, num_sc: u32) -> AllocationSite {
    let info = simple_ctor(tag, num_obj, num_sc);
    AllocationSite {
        var: var(1),
        ctor_tag: tag as u16,
        num_fields: info.field_types.len(),
        field_types: info.field_types.clone(),
        ctor_info: info,
    }
}

#[test]
fn test_compatible_exact_and_partial() {
    // Exact match: same layout
    let c = make_cand(0, 2, 0, 0);
    let a = make_alloc(1, 2, 0);
    assert!(is_compatible_reuse(&c, &a, false));
    assert!(is_compatible_reuse(&c, &a, true));
    // Partial: source larger
    let c_big = make_cand(0, 3, 0, 0);
    let a_small = make_alloc(1, 2, 0);
    assert!(!is_compatible_reuse(&c_big, &a_small, false));
    assert!(is_compatible_reuse(&c_big, &a_small, true));
    // Incompatible: source smaller
    let c_sm = make_cand(0, 1, 0, 0);
    let a_lg = make_alloc(0, 3, 0);
    assert!(!is_compatible_reuse(&c_sm, &a_lg, false));
    assert!(!is_compatible_reuse(&c_sm, &a_lg, true));
}

#[test]
fn test_compatible_scalar_variants() {
    // Exact scalar match
    let src = CtorInfo {
        name: name("A"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt64],
    };
    let tgt = CtorInfo {
        name: name("B"),
        tag: 1,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt64],
    };
    let c = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 2,
        field_types: src.field_types.clone(),
        distance_to_use: 0,
        ctor_info: src,
    };
    let a = AllocationSite {
        var: var(1),
        ctor_tag: 1,
        num_fields: 2,
        field_types: tgt.field_types.clone(),
        ctor_info: tgt,
    };
    assert!(is_compatible_reuse(&c, &a, false));
    // Different scalar size: UInt64(8) vs UInt8(1), partial allows
    let src2 = CtorInfo {
        name: name("A"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt64],
    };
    let tgt2 = CtorInfo {
        name: name("B"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt8],
    };
    let c2 = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 2,
        field_types: src2.field_types.clone(),
        distance_to_use: 0,
        ctor_info: src2,
    };
    let a2 = AllocationSite {
        var: var(1),
        ctor_tag: 0,
        num_fields: 2,
        field_types: tgt2.field_types.clone(),
        ctor_info: tgt2,
    };
    assert!(!is_compatible_reuse(&c2, &a2, false));
    assert!(is_compatible_reuse(&c2, &a2, true));
}

// ── find_reuse_candidates ──────────────────────────────────────────────

#[test]
fn test_find_candidates_simple_case() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(ret(0)),
        }],
        default: None,
    };
    let cands = find_reuse_candidates(&body);
    assert_eq!(cands.len(), 1);
    assert_eq!(cands[0].source_var, var(0));
    assert_eq!(cands[0].ctor_tag, 0);
    assert_eq!(cands[0].num_fields, 2);
}

#[test]
fn test_find_candidates_multiple_alts() {
    let ctor_a = simple_ctor(0, 2, 0);
    let ctor_b = simple_ctor(1, 3, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![
            IRAlt {
                ctor: ctor_a,
                body: Box::new(ret(0)),
            },
            IRAlt {
                ctor: ctor_b,
                body: Box::new(ret(0)),
            },
        ],
        default: None,
    };
    let cands = find_reuse_candidates(&body);
    assert_eq!(cands.len(), 2);
    assert_eq!(cands[0].ctor_tag, 0);
    assert_eq!(cands[1].ctor_tag, 1);
}

#[test]
fn test_find_candidates_nested_case() {
    let outer = simple_ctor(0, 1, 0);
    let inner = simple_ctor(1, 2, 0);
    let inner_case = IRBody::Case {
        scrutinee: var(1),
        alts: vec![IRAlt {
            ctor: inner,
            body: Box::new(ret(1)),
        }],
        default: None,
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: outer,
            body: Box::new(vdecl_proj(1, 0, 0, inner_case)),
        }],
        default: None,
    };
    let cands = find_reuse_candidates(&body);
    assert_eq!(cands.len(), 2);
}

#[test]
fn test_find_candidates_no_case_empty() {
    let body = ret(0);
    let cands = find_reuse_candidates(&body);
    assert!(cands.is_empty());
}

// ── find_allocation_sites ──────────────────────────────────────────────

#[test]
fn test_find_alloc_sites_simple() {
    let ctor = simple_ctor(0, 2, 0);
    let body = vdecl_ctor(1, ctor, vec![], ret(1));
    let sites = find_allocation_sites(&body);
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].var, var(1));
}

#[test]
fn test_find_alloc_sites_multiple() {
    let ctor_a = simple_ctor(0, 2, 0);
    let ctor_b = simple_ctor(1, 3, 0);
    let body = vdecl_ctor(1, ctor_a, vec![], vdecl_ctor(2, ctor_b, vec![], ret(2)));
    let sites = find_allocation_sites(&body);
    assert_eq!(sites.len(), 2);
}

#[test]
fn test_find_alloc_sites_in_case_alt() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor, vec![], ret(1))),
        }],
        default: None,
    };
    let sites = find_allocation_sites(&body);
    assert_eq!(sites.len(), 1);
}

#[test]
fn test_find_alloc_sites_none() {
    let body = ret(0);
    let sites = find_allocation_sites(&body);
    assert!(sites.is_empty());
}

// ── match_reuse_pairs ──────────────────────────────────────────────────

#[test]
fn test_match_pairs_exact_match() {
    let pairs = match_reuse_pairs(
        &[make_cand(0, 2, 0, 0)],
        &[make_alloc(1, 2, 0)],
        &default_config(),
    );
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0], (0, 0));
}

#[test]
fn test_match_pairs_distance_rejected() {
    let pairs = match_reuse_pairs(
        &[make_cand(0, 2, 0, 10)],
        &[make_alloc(0, 2, 0)],
        &default_config(),
    );
    assert!(pairs.is_empty(), "distance 10 > max 5");
}

#[test]
fn test_match_pairs_one_to_one() {
    let c1 = make_cand(0, 2, 0, 0);
    let c2 = make_cand(1, 3, 0, 0);
    let a1 = make_alloc(0, 3, 0);
    let pairs = match_reuse_pairs(&[c1, c2], &[a1], &default_config());
    assert_eq!(pairs.len(), 1);
    assert_eq!(pairs[0], (1, 0)); // c2 matches a1 exactly
}

#[test]
fn test_match_pairs_no_double_use() {
    let c = make_cand(0, 2, 0, 0);
    let a1 = make_alloc(0, 2, 0);
    let a2 = make_alloc(0, 2, 0);
    let pairs = match_reuse_pairs(&[c], &[a1, a2], &default_config());
    assert_eq!(pairs.len(), 1, "one candidate => one pairing");
}

// ── End-to-end: optimize_reset_reuse_ext ───────────────────────────────

fn case_with_ctor_alloc(source: CtorInfo, target: CtorInfo) -> IRBody {
    IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: source,
            body: Box::new(vdecl_ctor(1, target, vec![], ret(1))),
        }],
        default: None,
    }
}

#[test]
fn test_e2e_simple_case_inserts_reset_reuse() {
    let ctor = simple_ctor(0, 2, 0);
    let mut decls = vec![make_decl(case_with_ctor_alloc(ctor.clone(), ctor))];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
    assert_eq!(stats.reuses_inserted, 1);
    assert_eq!(stats.partial_reuses, 0);
    // Verify Reset -> Reuse structure
    if let IRBody::Case { alts, .. } = &decls[0].body {
        if let IRBody::VDecl {
            value: IRExpr::Reset(rv),
            rest,
            ..
        } = &*alts[0].body
        {
            assert_eq!(*rv, var(0));
            assert!(matches!(
                &**rest,
                IRBody::VDecl {
                    value: IRExpr::Reuse { .. },
                    ..
                }
            ));
        } else {
            panic!("expected Reset at alt body top");
        }
    } else {
        panic!("expected Case");
    }
}

#[test]
fn test_e2e_default_api() {
    let ctor = simple_ctor(0, 2, 0);
    let mut decls = vec![make_decl(case_with_ctor_alloc(ctor.clone(), ctor))];
    let stats = optimize_reset_reuse_ext_default(&mut decls);
    assert_eq!(stats.resets_inserted, 1);
    assert_eq!(stats.reuses_inserted, 1);
}

#[test]
fn test_e2e_incompatible_no_reuse() {
    let mut decls = vec![make_decl(case_with_ctor_alloc(
        simple_ctor(0, 2, 0),
        simple_ctor(0, 5, 0),
    ))];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 0);
    assert_eq!(stats.reuses_inserted, 0);
}

#[test]
fn test_e2e_partial_reuse_source_larger() {
    let mut decls = vec![make_decl(case_with_ctor_alloc(
        simple_ctor(0, 3, 0),
        simple_ctor(1, 2, 0),
    ))];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
    assert_eq!(stats.reuses_inserted, 1);
    assert_eq!(stats.partial_reuses, 1);
}

#[test]
fn test_e2e_partial_reuse_disabled() {
    let mut decls = vec![make_decl(case_with_ctor_alloc(
        simple_ctor(0, 3, 0),
        simple_ctor(1, 2, 0),
    ))];
    let config = ResetReuseExtConfig {
        enable_partial_reuse: false,
        ..default_config()
    };
    let stats = optimize_reset_reuse_ext(&mut decls, &config);
    assert_eq!(
        stats.resets_inserted, 0,
        "partial reuse disabled => no reuse"
    );
}

#[test]
fn test_e2e_reuse_distance_blocks_far_ctor() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(IRBody::Inc {
                var: var(3),
                n: 1,
                rest: Box::new(vdecl_ctor(1, ctor, vec![], ret(1))),
            }),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let config = ResetReuseExtConfig {
        max_reuse_distance: 0,
        ..default_config()
    };
    let stats = optimize_reset_reuse_ext(&mut decls, &config);
    assert_eq!(stats.resets_inserted, 0, "ctor is past distance budget");
    assert!(stats.candidates_rejected > 0);
}

// ── Multi-reset ────────────────────────────────────────────────────────

#[test]
fn test_multi_reset_two_alts() {
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 2);
    assert_eq!(stats.reuses_inserted, 2);
    assert_eq!(stats.multi_resets, 1);
}

#[test]
fn test_multi_reset_disabled_still_inserts_but_no_multi_stat() {
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
    let mut decls = vec![make_decl(body)];
    let config = ResetReuseExtConfig {
        enable_multi_reset: false,
        ..default_config()
    };
    let stats = optimize_reset_reuse_ext(&mut decls, &config);
    // Still inserts resets; multi_resets stat just doesn't count.
    assert_eq!(stats.resets_inserted, 2);
    assert_eq!(stats.multi_resets, 0);
}

// ── Field liveness ─────────────────────────────────────────────────────

#[test]
fn test_field_liveness_blocks_reuse() {
    // case v0 of Ctor0(2 obj) =>
    //   let v1 := proj 0 v0;
    //   let v2 := Ctor0(2 obj, [v1]);  // uses projected var
    //   ret v2
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(
        stats.resets_inserted, 0,
        "projected var in args blocks reuse"
    );
}

#[test]
fn test_field_liveness_disabled_allows_reuse() {
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
    let mut decls = vec![make_decl(body)];
    let config = ResetReuseExtConfig {
        track_field_liveness: false,
        ..default_config()
    };
    let stats = optimize_reset_reuse_ext(&mut decls, &config);
    assert_eq!(
        stats.resets_inserted, 1,
        "liveness disabled => reuse allowed"
    );
}

#[test]
fn test_non_projected_arg_allows_reuse() {
    // case v0 of Ctor0(2 obj) =>
    //   let v1 := proj 0 v0;
    //   let v2 := Ctor0(2 obj, [v3]);  // v3 not a projection from v0
    //   ret v2
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

// ── Edge cases ─────────────────────────────────────────────────────────

#[test]
fn test_empty_decls() {
    let mut decls: Vec<IRDecl> = vec![];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 0);
}

#[test]
fn test_no_case_body() {
    let ctor = simple_ctor(0, 2, 0);
    let body = vdecl_ctor(1, ctor, vec![], ret(1));
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 0);
}

#[test]
fn test_unreachable_body_no_crash() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor,
            body: Box::new(IRBody::Unreachable),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 0);
}

#[test]
fn test_ret_only_body_no_crash() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor,
            body: Box::new(ret(0)),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 0);
}

#[test]
fn test_default_branch_recursion() {
    let ctor = simple_ctor(0, 2, 0);
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_inc_dec_before_ctor() {
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_erased_args_reuse() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(
                1,
                ctor.clone(),
                vec![IRArg::Erased, IRArg::Erased],
                ret(1),
            )),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_multiple_decls() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor.clone(), vec![], ret(1))),
        }],
        default: None,
    };
    let d1 = make_decl(body.clone());
    let mut d2 = make_decl(body);
    d2.name = name("test_fn2");
    let mut decls = vec![d1, d2];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 2);
    assert_eq!(stats.reuses_inserted, 2);
}

#[test]
fn test_first_ctor_gets_reuse_second_unchanged() {
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
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1, "only first Ctor reused");
    assert_eq!(stats.reuses_inserted, 1);
}

#[test]
fn test_nested_case_inner_reuse() {
    let outer_ctor = simple_ctor(0, 1, 0);
    let inner_ctor = simple_ctor(1, 3, 0);
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
            ctor: outer_ctor,
            body: Box::new(vdecl_proj(1, 0, 0, inner_case)),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    // Outer: no compatible Ctor. Inner: yes.
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_zero_field_constructors() {
    let src = simple_ctor(0, 0, 0);
    let tgt = simple_ctor(1, 0, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: src,
            body: Box::new(vdecl_ctor(1, tgt, vec![], ret(1))),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_jdecl_body_recurses() {
    let ctor = simple_ctor(0, 2, 0);
    let jp_body = IRBody::Case {
        scrutinee: var(5),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(6, ctor.clone(), vec![], ret(6))),
        }],
        default: None,
    };
    let body = IRBody::JDecl {
        jp: crate::ir::JoinPointId(0),
        params: vec![(var(5), IRType::Object)],
        body: Box::new(jp_body),
        rest: Box::new(ret(0)),
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(stats.resets_inserted, 1);
}

#[test]
fn test_uproj_projection_tracked() {
    let ctor = CtorInfo {
        name: name("Ctor0"),
        tag: 0,
        num_scalars: 0,
        num_objects: 2,
        field_types: vec![IRType::Object, IRType::USize],
    };
    // let v1 := uproj 0 v0; let v2 := Ctor0([v1]); ret v2
    let uproj_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::USize,
        value: IRExpr::UProj {
            idx: 0,
            var: var(0),
        },
        rest: Box::new(vdecl_ctor(2, ctor.clone(), vec![arg_var(1)], ret(2))),
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(uproj_body),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(
        stats.resets_inserted, 0,
        "uproj var used in ctor args blocks reuse"
    );
}

#[test]
fn test_sproj_projection_tracked() {
    let ctor = CtorInfo {
        name: name("Ctor0"),
        tag: 0,
        num_scalars: 1,
        num_objects: 1,
        field_types: vec![IRType::Object, IRType::UInt64],
    };
    let sproj_body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt64,
        value: IRExpr::SProj {
            n: 0,
            offset: 0,
            var: var(0),
            ty: IRType::UInt64,
        },
        rest: Box::new(vdecl_ctor(2, ctor.clone(), vec![arg_var(1)], ret(2))),
    };
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(sproj_body),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(
        stats.resets_inserted, 0,
        "sproj var used in ctor args blocks reuse"
    );
}

// ── rank_candidates ───────────────────────────────────────────────────

#[test]
fn test_rank_candidates_exact_before_partial() {
    // c0: exact match (2 obj, 0 scalar), distance 0
    // c1: partial match (3 obj, 0 scalar), distance 0
    let c0 = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        distance_to_use: 0,
        ctor_info: simple_ctor(0, 2, 0),
    };
    let c1 = ReuseCandidate {
        source_var: var(1),
        ctor_tag: 1,
        num_fields: 3,
        field_types: vec![IRType::Object; 3],
        distance_to_use: 0,
        ctor_info: simple_ctor(1, 3, 0),
    };
    let alloc = AllocationSite {
        var: var(2),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        ctor_info: simple_ctor(0, 2, 0),
    };
    let ranked = rank_candidates(&[c0, c1], &alloc, &default_config());
    // c0 is exact match, should come first
    assert_eq!(ranked[0], 0, "exact match ranked first");
}

#[test]
fn test_rank_candidates_closer_distance_preferred() {
    // Both exact match, c0 distance 3, c1 distance 1
    let c0 = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        distance_to_use: 3,
        ctor_info: simple_ctor(0, 2, 0),
    };
    let c1 = ReuseCandidate {
        source_var: var(1),
        ctor_tag: 1,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        distance_to_use: 1,
        ctor_info: simple_ctor(1, 2, 0),
    };
    let alloc = AllocationSite {
        var: var(2),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        ctor_info: simple_ctor(0, 2, 0),
    };
    let ranked = rank_candidates(&[c0, c1], &alloc, &default_config());
    assert_eq!(ranked[0], 1, "closer distance ranked first");
}

#[test]
fn test_rank_candidates_filters_incompatible() {
    let c0 = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 1,
        field_types: vec![IRType::Object],
        distance_to_use: 0,
        ctor_info: simple_ctor(0, 1, 0), // too small
    };
    let alloc = AllocationSite {
        var: var(1),
        ctor_tag: 0,
        num_fields: 5,
        field_types: vec![IRType::Object; 5],
        ctor_info: simple_ctor(0, 5, 0),
    };
    let cfg = ResetReuseExtConfig {
        enable_partial_reuse: false,
        ..default_config()
    };
    let ranked = rank_candidates(&[c0], &alloc, &cfg);
    assert!(ranked.is_empty(), "incompatible candidate filtered out");
}

#[test]
fn test_rank_candidates_filters_over_distance() {
    let c0 = ReuseCandidate {
        source_var: var(0),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        distance_to_use: 100,
        ctor_info: simple_ctor(0, 2, 0),
    };
    let alloc = AllocationSite {
        var: var(1),
        ctor_tag: 0,
        num_fields: 2,
        field_types: vec![IRType::Object; 2],
        ctor_info: simple_ctor(0, 2, 0),
    };
    let ranked = rank_candidates(&[c0], &alloc, &default_config());
    assert!(ranked.is_empty(), "over-distance candidate filtered out");
}

// ── candidates_rejected stat ──────────────────────────────────────────

#[test]
fn test_candidates_rejected_on_incompatible() {
    // Source ctor: 2 objects. Target ctor: 5 objects (too big, no partial).
    let source = simple_ctor(0, 2, 0);
    let target = simple_ctor(0, 5, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: source,
            body: Box::new(vdecl_ctor(1, target, vec![], ret(1))),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let config = ResetReuseExtConfig {
        enable_partial_reuse: false,
        ..default_config()
    };
    let stats = optimize_reset_reuse_ext(&mut decls, &config);
    assert_eq!(stats.resets_inserted, 0);
    assert!(
        stats.candidates_rejected > 0,
        "should record rejected candidate"
    );
}

#[test]
fn test_candidates_rejected_zero_on_match() {
    let ctor = simple_ctor(0, 2, 0);
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: ctor.clone(),
            body: Box::new(vdecl_ctor(1, ctor, vec![], ret(1))),
        }],
        default: None,
    };
    let mut decls = vec![make_decl(body)];
    let stats = optimize_reset_reuse_ext(&mut decls, &default_config());
    assert_eq!(
        stats.candidates_rejected, 0,
        "no rejections when exact match"
    );
    assert_eq!(stats.resets_inserted, 1);
}
