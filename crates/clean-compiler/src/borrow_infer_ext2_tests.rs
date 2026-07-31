// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended borrow inference phase 2: field-sensitive borrowing,
//! uniqueness analysis, last-use detection, conflict detection, and
//! inter-procedural borrow summaries.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, JoinPointId, VarId};
use clean_kernel::Name;

fn var(n: u32) -> VarId {
    VarId(n)
}
fn arg_var(n: u32) -> IRArg {
    IRArg::Var(VarId(n))
}
fn name(s: &str) -> Name {
    Name::from_string(s)
}
fn fn_id(s: &str) -> FnId {
    FnId(Name::from_string(s))
}
fn jp(n: u32) -> JoinPointId {
    JoinPointId(n)
}

fn mk_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    }
}

fn identity_decl(fname: &str, pvar: u32) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(pvar), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(pvar)),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Config tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_config_defaults() {
    let config = BorrowExt2Config::default();
    assert_eq!(config.max_iterations, 20);
    assert!(config.enable_field_sensitive);
    assert!(config.enable_uniqueness);
    assert!(config.enable_last_use);
    assert!(config.enable_conflict_detection);
    assert!(config.conservative_extern);
}

#[test]
fn test_borrow_class_default_is_unknown() {
    assert_eq!(BorrowClass::default(), BorrowClass::Unknown);
}

// ═══════════════════════════════════════════════════════════════════════
// Escape analysis: EscapeKind variants
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_return_value() {
    let body = IRBody::Ret(arg_var(0));
    let escapes = collect_escapes_ext2(&body, &[var(0)]);
    assert_eq!(escapes.len(), 1);
    assert_eq!(escapes[0], (var(0), EscapeKind::ReturnValue));
}

#[test]
fn test_escape_stored_in_ctor() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: mk_ctor(0),
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = collect_escapes_ext2(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::StoredInCtor));
}

#[test]
fn test_escape_captured_by_closure() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::PartialApply {
            fn_id: fn_id("g"),
            arity: 2,
            args: vec![arg_var(0)],
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = collect_escapes_ext2(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::CapturedByClosure));
}

#[test]
fn test_escape_passed_to_extern() {
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: arg_var(0),
            args: vec![arg_var(1)],
        },
        rest: Box::new(IRBody::Ret(arg_var(2))),
    };
    let escapes = collect_escapes_ext2(&body, &[var(0), var(1)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::PassedToExtern));
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(1) && *k == EscapeKind::PassedToExtern));
}

#[test]
fn test_escape_mutably_modified_set() {
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let escapes = collect_escapes_ext2(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::MutablyModified));
}

#[test]
fn test_escape_mutably_modified_reset() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reset(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let escapes = collect_escapes_ext2(&body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::MutablyModified));
}

#[test]
fn test_no_escape_tag_read() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt32,
        value: IRExpr::Tag(arg_var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(collect_escapes_ext2(&body, &[var(0)]).is_empty());
}

#[test]
fn test_no_escape_is_shared() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(collect_escapes_ext2(&body, &[var(0)]).is_empty());
}

#[test]
fn test_no_escape_erased_return() {
    assert!(collect_escapes_ext2(&IRBody::Ret(IRArg::Erased), &[var(0)]).is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Last-use detection
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_last_use_simple_return() {
    let body = IRBody::Ret(arg_var(0));
    let lu = detect_last_uses(&body);
    assert_eq!(lu.get(&var(0)), Some(&0));
}

#[test]
fn test_last_use_multiple_uses() {
    // v1 = Tag(v0); v2 = Ctor(v0); ret v2
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt32,
        value: IRExpr::Tag(arg_var(0)),
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        }),
    };
    let lu = detect_last_uses(&body);
    // v0 used at depth 0 (Tag) and depth 1 (Ctor), last use is 1
    assert_eq!(lu.get(&var(0)), Some(&1));
}

#[test]
fn test_last_use_in_case_branch() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: mk_ctor(0),
            body: Box::new(IRBody::Ret(arg_var(0))),
        }],
        default: None,
    };
    let lu = detect_last_uses(&body);
    // scrutinee at depth 0, return in alt at depth 1
    assert_eq!(lu.get(&var(0)), Some(&1));
}

#[test]
fn test_last_use_inc_dec() {
    let body = IRBody::Inc {
        var: var(0),
        n: 1,
        rest: Box::new(IRBody::Dec {
            var: var(0),
            rest: Box::new(IRBody::Ret(IRArg::Erased)),
        }),
    };
    let lu = detect_last_uses(&body);
    assert_eq!(lu.get(&var(0)), Some(&1));
}

// ═══════════════════════════════════════════════════════════════════════
// Uniqueness analysis
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_uniqueness_no_shared_check() {
    let body = IRBody::Ret(arg_var(0));
    let unique = analyze_uniqueness(&body, &[var(0)]);
    assert!(unique.contains(&var(0)));
}

#[test]
fn test_uniqueness_with_shared_check() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let unique = analyze_uniqueness(&body, &[var(0)]);
    assert!(!unique.contains(&var(0)));
}

#[test]
fn test_uniqueness_partial_params() {
    // v0 checked for shared, v1 not checked
    let body = IRBody::VDecl {
        var: var(2),
        ty: IRType::UInt8,
        value: IRExpr::IsShared(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let unique = analyze_uniqueness(&body, &[var(0), var(1)]);
    assert!(!unique.contains(&var(0)));
    assert!(unique.contains(&var(1)));
}

// ═══════════════════════════════════════════════════════════════════════
// Field-sensitive borrowing
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_field_borrow_proj() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 2,
            ty: IRType::Object,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let fb = collect_field_borrows(&body);
    assert_eq!(fb.len(), 1);
    assert!(fb.contains(&FieldBorrow {
        var: var(0),
        field_idx: 2
    }));
}

#[test]
fn test_field_borrow_multiple_fields() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: arg_var(0),
        },
        rest: Box::new(IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 1,
                ty: IRType::Object,
                arg: arg_var(0),
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        }),
    };
    let fb = collect_field_borrows(&body);
    assert_eq!(fb.len(), 2);
    assert!(fb.contains(&FieldBorrow {
        var: var(0),
        field_idx: 0
    }));
    assert!(fb.contains(&FieldBorrow {
        var: var(0),
        field_idx: 1
    }));
}

#[test]
fn test_field_borrow_no_proj() {
    let body = IRBody::Ret(arg_var(0));
    assert!(collect_field_borrows(&body).is_empty());
}

#[test]
fn test_field_borrow_erased_proj_not_tracked() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Proj {
            idx: 0,
            ty: IRType::Object,
            arg: IRArg::Erased,
        },
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    assert!(collect_field_borrows(&body).is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Borrow conflict detection
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_conflict_set_on_param() {
    let body = IRBody::Set {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert_eq!(conflicts.len(), 1);
    assert_eq!(conflicts[0].var, var(0));
}

#[test]
fn test_conflict_uset_on_param() {
    let body = IRBody::USet {
        var: var(0),
        idx: 0,
        value: var(1),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_conflict_reset_on_param() {
    let body = IRBody::VDecl {
        var: var(1),
        ty: IRType::Object,
        value: IRExpr::Reset(var(0)),
        rest: Box::new(IRBody::Ret(arg_var(1))),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_no_conflict_on_non_param() {
    let body = IRBody::Set {
        var: var(5),
        idx: 0,
        value: var(6),
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert!(conflicts.is_empty());
}

#[test]
fn test_conflict_settag_on_param() {
    let body = IRBody::SetTag {
        var: var(0),
        tag: 1,
        rest: Box::new(IRBody::Ret(arg_var(0))),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert_eq!(conflicts.len(), 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Full analysis pipeline
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_full_analysis_empty_decls() {
    let result = analyze_borrows_ext2_default(&[]);
    assert!(result.summaries.is_empty());
    assert_eq!(result.stats.params_classified, 0);
}

#[test]
fn test_full_analysis_identity_owned() {
    let decl = identity_decl("id", 0);
    let result = analyze_borrows_ext2_default(&[decl]);
    let summary = result
        .summaries
        .get(&fn_id("id"))
        .expect("should have summary");
    assert_eq!(summary.fn_id, fn_id("id"));
    assert_eq!(summary.param_classes.len(), 1);
    assert_eq!(summary.param_classes[0], BorrowClass::Owned);
    assert_eq!(summary.escapes, vec![(var(0), EscapeKind::ReturnValue)]);
    assert!(summary.conflicts.is_empty());
    assert!(result.unique_vars.contains_key(&fn_id("id")));
    assert!(result.field_borrows.contains_key(&fn_id("id")));
}

#[test]
fn test_full_analysis_tag_only_borrowed() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt32,
            value: IRExpr::Tag(arg_var(0)),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    let summary = result
        .summaries
        .get(&fn_id("f"))
        .expect("should have summary");
    // Tag inspection is read-only and does not make the object escape.
    assert_eq!(summary.param_classes[0], BorrowClass::Borrowed);
}

#[test]
fn test_full_analysis_scalar_always_owned() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(arg_var(0)),
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    let summary = result
        .summaries
        .get(&fn_id("f"))
        .expect("should have summary");
    assert_eq!(summary.param_classes[0], BorrowClass::Owned);
}

#[test]
fn test_full_analysis_cross_function_propagation() {
    let wrap = IRDecl {
        name: name("wrap"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let caller = IRDecl {
        name: name("caller"),
        params: vec![(var(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("wrap"),
                args: vec![arg_var(10)],
            },
            rest: Box::new(IRBody::Ret(arg_var(11))),
        },
    };
    let result = analyze_borrows_ext2_default(&[wrap, caller]);
    let caller_sum = result
        .summaries
        .get(&fn_id("caller"))
        .expect("should have caller");
    assert_eq!(caller_sum.param_classes[0], BorrowClass::Owned);
}

#[test]
fn test_full_analysis_no_params() {
    let decl = IRDecl {
        name: name("unit"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    let summary = result
        .summaries
        .get(&fn_id("unit"))
        .expect("should have summary");
    assert!(summary.param_classes.is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Statistics
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_params_classified() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(0)),
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert_eq!(result.stats.params_classified, 2);
}

#[test]
fn test_stats_escapes_detected() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(0)),
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert_eq!(result.stats.escapes_detected, 1);
}

#[test]
fn test_stats_last_uses_found() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(0)),
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert!(result.stats.last_uses_found >= 1);
}

#[test]
fn test_stats_conflicts_found() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(0),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert!(result.stats.conflicts_found >= 1);
}

#[test]
fn test_stats_fields_tracked() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: arg_var(0),
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert_eq!(result.stats.fields_tracked, 1);
}

#[test]
fn test_stats_join_points_analyzed() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![(var(10), IRType::Object)],
            body: Box::new(IRBody::Ret(arg_var(10))),
            rest: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![arg_var(0)],
            }),
        },
    };
    let result = analyze_borrows_ext2_default(&[decl]);
    assert_eq!(result.stats.join_points_analyzed, 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Configuration options
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_config_disable_field_sensitive() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: arg_var(0),
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let config = BorrowExt2Config {
        enable_field_sensitive: false,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    assert_eq!(result.stats.fields_tracked, 0);
}

#[test]
fn test_config_disable_last_use() {
    let decl = identity_decl("id", 0);
    let config = BorrowExt2Config {
        enable_last_use: false,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    assert_eq!(result.stats.last_uses_found, 0);
    assert!(!result.last_uses.contains_key(&fn_id("id")));
}

#[test]
fn test_config_disable_conflict_detection() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(0),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    };
    let config = BorrowExt2Config {
        enable_conflict_detection: false,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    assert_eq!(result.stats.conflicts_found, 0);
}

#[test]
fn test_config_max_iterations_respected() {
    let decl = identity_decl("id", 0);
    let config = BorrowExt2Config {
        max_iterations: 1,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    assert!(result.summaries.contains_key(&fn_id("id")));
}

// ═══════════════════════════════════════════════════════════════════════
// Edge cases: join points, case, jmp
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_through_jmp() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: jp(0),
            params: vec![(var(10), IRType::Object)],
            body: Box::new(IRBody::Ret(arg_var(10))),
            rest: Box::new(IRBody::Jmp {
                jp: jp(0),
                args: vec![arg_var(0)],
            }),
        },
    };
    let escapes = collect_escapes_ext2(&decl.body, &[var(0)]);
    assert!(escapes
        .iter()
        .any(|(v, k)| *v == var(0) && *k == EscapeKind::PassedToExtern));
}

#[test]
fn test_field_borrow_in_case_branch() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: mk_ctor(0),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    idx: 3,
                    ty: IRType::Object,
                    arg: arg_var(0),
                },
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: None,
    };
    let fb = collect_field_borrows(&body);
    assert!(fb.contains(&FieldBorrow {
        var: var(0),
        field_idx: 3
    }));
}

#[test]
fn test_conflict_in_jdecl_body() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(10), IRType::Object)],
        body: Box::new(IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(10),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![arg_var(0)],
        }),
    };
    let conflicts = detect_conflicts(&body, &[var(0)]);
    assert_eq!(conflicts.len(), 1);
}

#[test]
fn test_uniqueness_shared_check_in_case() {
    let body = IRBody::Case {
        scrutinee: var(0),
        alts: vec![IRAlt {
            ctor: mk_ctor(0),
            body: Box::new(IRBody::VDecl {
                var: var(1),
                ty: IRType::UInt8,
                value: IRExpr::IsShared(var(0)),
                rest: Box::new(IRBody::Ret(arg_var(1))),
            }),
        }],
        default: None,
    };
    let unique = analyze_uniqueness(&body, &[var(0)]);
    assert!(!unique.contains(&var(0)));
}

#[test]
fn test_last_use_through_jdecl() {
    let body = IRBody::JDecl {
        jp: jp(0),
        params: vec![(var(10), IRType::Object)],
        body: Box::new(IRBody::VDecl {
            var: var(11),
            ty: IRType::UInt32,
            value: IRExpr::Tag(arg_var(10)),
            rest: Box::new(IRBody::Ret(arg_var(11))),
        }),
        rest: Box::new(IRBody::Jmp {
            jp: jp(0),
            args: vec![arg_var(0)],
        }),
    };
    let lu = detect_last_uses(&body);
    // v0 used at depth 1 in the Jmp, v10 used deeper in jp body
    assert!(lu.contains_key(&var(0)));
}

// ═══════════════════════════════════════════════════════════════════════
// Conservative extern handling
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_conservative_extern_true() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("unknown"),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let config = BorrowExt2Config {
        conservative_extern: true,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    let summary = result
        .summaries
        .get(&fn_id("f"))
        .expect("should have summary");
    assert_eq!(summary.param_classes[0], BorrowClass::Owned);
}

#[test]
fn test_conservative_extern_false() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("unknown"),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let config = BorrowExt2Config {
        conservative_extern: false,
        ..Default::default()
    };
    let result = analyze_borrows_ext2(&[decl], &config);
    let summary = result
        .summaries
        .get(&fn_id("f"))
        .expect("should have summary");
    // escape analysis still detects PassedToExtern
    assert_eq!(summary.param_classes[0], BorrowClass::Owned);
}
