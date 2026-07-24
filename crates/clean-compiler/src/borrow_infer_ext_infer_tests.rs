// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for extended borrow inference: full inference pipeline,
//! cross-function propagation, config options, and edge cases.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
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

fn mk_ctor(tag: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    }
}

fn mk_ctor_n(tag: u32, n_objs: u32) -> CtorInfo {
    CtorInfo {
        name: name("Ctor"),
        tag,
        num_scalars: 0,
        num_objects: n_objs,
        field_types: vec![IRType::Object; n_objs as usize],
    }
}

fn identity_decl(fname: &str, param_var: u32) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(param_var), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(param_var)),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Full inference: infer_borrows_ext
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_infer_identity_owned() {
    let decl = identity_decl("id", 0);
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership.len(), 1);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_infer_tag_only_borrowed() {
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
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Borrowed));
    assert_eq!(result.stats.params_borrowed, 1);
    assert_eq!(result.stats.params_owned, 0);
}

#[test]
fn test_infer_ctor_stores_owned() {
    let decl = IRDecl {
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
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_infer_empty_decls() {
    let result = infer_borrows_ext_default(&[]);
    assert!(result.param_ownership.is_empty());
    assert_eq!(result.stats.params_borrowed, 0);
    assert_eq!(result.stats.params_owned, 0);
}

#[test]
fn test_infer_no_params() {
    let decl = IRDecl {
        name: name("unit"),
        params: vec![],
        return_type: IRType::Void,
        body: IRBody::Unreachable,
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert!(result.param_ownership.is_empty());
}

// ═══════════════════════════════════════════════════════════════════════
// Cross-function propagation
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_cross_function_propagation() {
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
    let result = infer_borrows_ext_default(&[wrap, caller]);
    let caller_own = result.fn_ownership.get(&fn_id("caller")).unwrap();
    assert_eq!(caller_own[0], Ownership::Owned);
    assert!(result.stats.iterations >= 2);
}

#[test]
fn test_mutual_recursion_convergence() {
    let even = IRDecl {
        name: name("even"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("odd"),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let odd = IRDecl {
        name: name("odd"),
        params: vec![(var(5), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(6),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![arg_var(5)],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(7),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: fn_id("even"),
                    args: vec![arg_var(5)],
                },
                rest: Box::new(IRBody::Ret(arg_var(7))),
            }),
        },
    };
    let result = infer_borrows_ext_default(&[even, odd]);
    assert_eq!(
        result.fn_ownership.get(&fn_id("even")).unwrap()[0],
        Ownership::Owned
    );
    assert_eq!(
        result.fn_ownership.get(&fn_id("odd")).unwrap()[0],
        Ownership::Owned
    );
}

#[test]
fn test_three_function_chain_propagation() {
    let c = IRDecl {
        name: name("c"),
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
    let b = IRDecl {
        name: name("b"),
        params: vec![(var(5), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(6),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("c"),
                args: vec![arg_var(5)],
            },
            rest: Box::new(IRBody::Ret(arg_var(6))),
        },
    };
    let a = IRDecl {
        name: name("a"),
        params: vec![(var(10), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(11),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: fn_id("b"),
                args: vec![arg_var(10)],
            },
            rest: Box::new(IRBody::Ret(arg_var(11))),
        },
    };
    let result = infer_borrows_ext_default(&[c, b, a]);
    assert_eq!(
        result.fn_ownership.get(&fn_id("a")).unwrap()[0],
        Ownership::Owned
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Config options
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_analysis_disabled() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(0)),
    };
    let config = BorrowInferExtConfig {
        enable_escape_analysis: false,
        ..Default::default()
    };
    let result = infer_borrows_ext(&[decl], &config);
    assert_eq!(result.stats.escapes_detected, 0);
}

#[test]
fn test_alias_tracking_disabled() {
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
    let config = BorrowInferExtConfig {
        enable_alias_tracking: false,
        ..Default::default()
    };
    let result = infer_borrows_ext(&[decl], &config);
    assert_eq!(result.stats.aliases_tracked, 0);
}

#[test]
fn test_pessimistic_extern_true() {
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
    let config = BorrowInferExtConfig {
        pessimistic_extern: true,
        ..Default::default()
    };
    let result = infer_borrows_ext(&[decl], &config);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_pessimistic_extern_false() {
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
    let config = BorrowInferExtConfig {
        pessimistic_extern: false,
        ..Default::default()
    };
    let result = infer_borrows_ext(&[decl], &config);
    // Escape analysis still detects PassedOwned
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_max_iterations_respected() {
    let decl = identity_decl("id", 0);
    let config = BorrowInferExtConfig {
        max_iterations: 1,
        ..Default::default()
    };
    let result = infer_borrows_ext(&[decl], &config);
    assert!(result.stats.iterations <= 1);
}

// ═══════════════════════════════════════════════════════════════════════
// Statistics
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_accurate_mixed() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::UInt32,
            value: IRExpr::Tag(arg_var(0)),
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: mk_ctor(0),
                    args: vec![arg_var(1)],
                },
                rest: Box::new(IRBody::Ret(arg_var(11))),
            }),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.stats.params_borrowed, 1);
    assert_eq!(result.stats.params_owned, 1);
    assert!(result.stats.escapes_detected > 0);
}

#[test]
fn test_stats_aliases_counted() {
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
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.stats.aliases_tracked, 2);
}

// ═══════════════════════════════════════════════════════════════════════
// Edge cases
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_escape_through_case_branch() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Case {
            scrutinee: var(0),
            alts: vec![IRAlt {
                ctor: mk_ctor(0),
                body: Box::new(IRBody::VDecl {
                    var: var(1),
                    ty: IRType::Object,
                    value: IRExpr::Ctor {
                        info: mk_ctor(1),
                        args: vec![arg_var(0)],
                    },
                    rest: Box::new(IRBody::Ret(arg_var(1))),
                }),
            }],
            default: Some(Box::new(IRBody::Ret(arg_var(0)))),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_escape_through_jmp() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: crate::ir::JoinPointId(0),
            params: vec![(var(10), IRType::Object)],
            body: Box::new(IRBody::Ret(arg_var(10))),
            rest: Box::new(IRBody::Jmp {
                jp: crate::ir::JoinPointId(0),
                args: vec![arg_var(0)],
            }),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}

#[test]
fn test_escape_uset_sset_settag() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::USet {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::SSet {
                var: var(0),
                n: 0,
                offset: 0,
                value: var(2),
                ty: IRType::UInt8,
                rest: Box::new(IRBody::SetTag {
                    var: var(0),
                    tag: 1,
                    rest: Box::new(IRBody::Ret(arg_var(0))),
                }),
            }),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
    assert_eq!(result.param_ownership[1], (var(1), Ownership::Owned));
    assert_eq!(result.param_ownership[2], (var(2), Ownership::Owned));
}

#[test]
fn test_multi_arg_ctor_all_owned() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::Object),
            (var(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor_n(0, 3),
                args: vec![arg_var(0), arg_var(1), arg_var(2)],
            },
            rest: Box::new(IRBody::Ret(arg_var(10))),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
    assert_eq!(result.param_ownership[1], (var(1), Ownership::Owned));
    assert_eq!(result.param_ownership[2], (var(2), Ownership::Owned));
}

#[test]
fn test_fn_ownership_map_populated() {
    let decl = identity_decl("id", 0);
    let result = infer_borrows_ext_default(&[decl]);
    assert!(result.fn_ownership.contains_key(&fn_id("id")));
    assert_eq!(result.fn_ownership.get(&fn_id("id")).unwrap().len(), 1);
}

#[test]
fn test_alias_chain_ownership_propagation() {
    // f(x) := let p = proj 0 x; let c = Ctor(p); return c
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
            rest: Box::new(IRBody::VDecl {
                var: var(2),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: mk_ctor(0),
                    args: vec![arg_var(1)],
                },
                rest: Box::new(IRBody::Ret(arg_var(2))),
            }),
        },
    };
    let result = infer_borrows_ext_default(&[decl]);
    assert_eq!(result.param_ownership[0], (var(0), Ownership::Owned));
}
