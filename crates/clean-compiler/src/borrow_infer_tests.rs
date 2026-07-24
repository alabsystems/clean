// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for L5IR borrow inference pass.

use super::*;
use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

// ═══════════════════════════════════════════════════════════════════════
// Helpers
// ═══════════════════════════════════════════════════════════════════════

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

/// Build a simple function: one object param, body returns param directly.
fn identity_decl(fname: &str, param_var: u32) -> IRDecl {
    IRDecl {
        name: name(fname),
        params: vec![(var(param_var), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(arg_var(param_var)),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Unit tests for ParamOwnership and IRFnBorrow
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_param_ownership_default_is_borrowed() {
    assert_eq!(ParamOwnership::default(), ParamOwnership::Borrowed);
}

#[test]
fn test_fn_borrow_all_borrowed() {
    let borrow = IRFnBorrow::all_borrowed(3);
    assert_eq!(borrow.params.len(), 3);
    assert!(borrow.params.iter().all(|p| *p == ParamOwnership::Borrowed));
    assert_eq!(borrow.borrowed_count(), 3);
    assert_eq!(borrow.owned_count(), 0);
}

#[test]
fn test_fn_borrow_mark_owned_changes() {
    let mut borrow = IRFnBorrow::all_borrowed(3);
    assert!(borrow.mark_owned(1));
    assert_eq!(borrow.params[1], ParamOwnership::Owned);
    assert_eq!(borrow.borrowed_count(), 2);
    assert_eq!(borrow.owned_count(), 1);
}

#[test]
fn test_fn_borrow_mark_owned_idempotent() {
    let mut borrow = IRFnBorrow::all_borrowed(2);
    assert!(borrow.mark_owned(0));
    assert!(!borrow.mark_owned(0)); // already owned
}

#[test]
fn test_fn_borrow_mark_owned_out_of_bounds() {
    let mut borrow = IRFnBorrow::all_borrowed(2);
    assert!(!borrow.mark_owned(5)); // no panic, returns false
}

#[test]
fn test_borrow_map_operations() {
    let mut map = IRBorrowMap::new();
    let fid = fn_id("foo");
    map.insert(fid.clone(), IRFnBorrow::all_borrowed(2));

    assert!(map.get(&fn_id("foo")).is_some());
    assert!(map.get(&fn_id("bar")).is_none());
    assert_eq!(map.len(), 1);

    assert!(map.mark_owned(&fn_id("foo"), 0));
    assert_eq!(
        map.get(&fn_id("foo")).unwrap().params[0],
        ParamOwnership::Owned
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: identity function (all borrowed)
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_identity_all_borrowed() {
    // id(x: Object) -> Object := return x
    // x is only returned, never consumed -> Borrowed
    let decl = identity_decl("id", 0);
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params.len(), 1);
    // Return consumes the value (transfers ownership out), so it's Owned
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_scalar_param_always_owned() {
    // f(x: UInt64) -> UInt64 := return x
    // Scalars are always owned (no RC involved).
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(arg_var(0)),
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_erased_param_always_owned() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Erased)],
        return_type: IRType::Erased,
        body: IRBody::Unreachable,
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: constructor storage consumes args
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_ctor_args_owned() {
    // wrap(x: Object) := let y = Ctor(x); return y
    // x is stored in constructor -> must be Owned
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_tag_read_only() {
    // f(x: Object) := let t = tag(x); return Erased
    // Tag is read-only. x is not consumed by anything else.
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
    let borrow = infer_ir_borrow_single(&decl);
    // x is not consumed by tag, but not returned either -> Borrowed
    assert_eq!(borrow.params[0], ParamOwnership::Borrowed);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: projection backward propagation
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_projection_propagates_ownership() {
    // f(x: Object) := let p = proj 0 x; let y = Ctor(p); return y
    // p is consumed by Ctor -> p is owned -> x must be owned (backward through proj)
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_projection_not_consumed_stays_borrowed() {
    // f(x: Object) := let p = proj 0 x; let t = tag(p); return t
    // p is only used in tag (read-only). x not consumed -> Borrowed
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt32,
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
                ty: IRType::UInt32,
                value: IRExpr::Tag(arg_var(1)),
                rest: Box::new(IRBody::Ret(arg_var(2))),
            }),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Borrowed);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: reset requires ownership
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_reset_requires_owned() {
    // f(x: Object) := let r = reset x; return r
    // Reset checks RC==1 and potentially mutates -> x must be Owned
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Reset(var(0)),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: mutable set requires ownership
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_set_requires_owned() {
    // f(x: Object, y: Object) := set x[0] = y; return x
    // Mutable set -> both x and y must be Owned
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Set {
            var: var(0),
            idx: 0,
            value: var(1),
            rest: Box::new(IRBody::Ret(arg_var(0))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
    assert_eq!(borrow.params[1], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: closure capture consumes args
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_partial_apply_captures_owned() {
    // f(x: Object) := let c = papp g 2 [x]; return c
    // Captured args must be owned (stored in closure)
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: fn_id("g"),
                arity: 2,
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_closure_apply_consumes_all() {
    // f(c: Object, x: Object) := let r = capp c [x]; return r
    // Closure and all args consumed
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: arg_var(0),
                args: vec![arg_var(1)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
    assert_eq!(borrow.params[1], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: cross-function propagation
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_cross_function_propagation() {
    // wrap(x) := Ctor(x) -> x is owned
    // caller(y) := wrap(y) -> y must be owned (passed to owned param)
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

    let config = BorrowInferConfig::default();
    let (map, stats) = infer_ir_borrow(&[wrap, caller], &config);

    let wrap_borrow = map.get(&fn_id("wrap")).unwrap();
    assert_eq!(wrap_borrow.params[0], ParamOwnership::Owned);

    let caller_borrow = map.get(&fn_id("caller")).unwrap();
    assert_eq!(caller_borrow.params[0], ParamOwnership::Owned);

    assert!(
        stats.iterations >= 2,
        "should require at least 2 iterations"
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: mutual recursion
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_mutual_recursion_propagation() {
    // even(x) := odd(x) -> x owned because odd consumes it
    // odd(y) := let c = Ctor(y); let r = even(y); return r
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

    let config = BorrowInferConfig::default();
    let (map, _) = infer_ir_borrow(&[even, odd], &config);

    assert_eq!(
        map.get(&fn_id("odd")).unwrap().params[0],
        ParamOwnership::Owned,
    );
    assert_eq!(
        map.get(&fn_id("even")).unwrap().params[0],
        ParamOwnership::Owned,
    );
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: tail-call promotion
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_tail_call_promotes_owned() {
    // f(x, y) := let c = Ctor(x); let r = f(y, x); return r
    // x consumed by Ctor, tail call f(y, x): x at pos 1 is owned ->
    // param[1] promoted to owned, then param[0] via forward propagation
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(10),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![arg_var(0)],
            },
            rest: Box::new(IRBody::VDecl {
                var: var(11),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: fn_id("f"),
                    args: vec![arg_var(1), arg_var(0)],
                },
                rest: Box::new(IRBody::Ret(arg_var(11))),
            }),
        },
    };

    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
    assert_eq!(borrow.params[1], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: case/switch
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_case_branches_ownership() {
    // f(x) := case x of
    //   | 0 => Ctor(x)    -- consumes x
    //   | _ => return x
    // Since one branch consumes x, x must be Owned
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Inference: box consumes arg
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_box_consumes_arg() {
    // f(x: Object) := let b = box UInt64 x; return b
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: arg_var(0),
            },
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

// ═══════════════════════════════════════════════════════════════════════
// Configuration: disabled = all owned
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_disabled_all_owned() {
    let decl = identity_decl("id", 0);
    let config = BorrowInferConfig {
        enabled: false,
        ..Default::default()
    };
    let (map, stats) = infer_ir_borrow(std::slice::from_ref(&decl), &config);
    let borrow = map.get(&fn_id("id")).unwrap();
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
    assert_eq!(stats.iterations, 0);
}

// ═══════════════════════════════════════════════════════════════════════
// Statistics
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_stats_accurate() {
    // Two functions: id(x) and wrap(x) = Ctor(x)
    let id = identity_decl("id", 0);
    let wrap = IRDecl {
        name: name("wrap"),
        params: vec![(var(5), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(6),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: mk_ctor(0),
                args: vec![arg_var(5)],
            },
            rest: Box::new(IRBody::Ret(arg_var(6))),
        },
    };

    let config = BorrowInferConfig::default();
    let (_, stats) = infer_ir_borrow(&[id, wrap], &config);

    assert_eq!(stats.functions, 2);
    assert_eq!(stats.total_params, 2);
    // Both params are object-typed and consumed (return/ctor)
    assert_eq!(stats.owned, 2);
    assert_eq!(stats.borrowed, 0);
    assert_eq!(stats.scalar_skipped, 0);
}

#[test]
fn test_stats_scalar_skipped() {
    let decl = IRDecl {
        name: name("f"),
        params: vec![
            (var(0), IRType::Object),
            (var(1), IRType::UInt64),
            (var(2), IRType::Bool),
        ],
        return_type: IRType::Object,
        body: IRBody::Unreachable,
    };

    let config = BorrowInferConfig::default();
    let (_, stats) = infer_ir_borrow(std::slice::from_ref(&decl), &config);

    assert_eq!(stats.total_params, 3);
    assert_eq!(stats.scalar_skipped, 2); // UInt64 and Bool
}

// ═══════════════════════════════════════════════════════════════════════
// Edge cases
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_empty_decls() {
    let config = BorrowInferConfig::default();
    let (map, stats) = infer_ir_borrow(&[], &config);
    assert_eq!(map.len(), 0);
    assert_eq!(stats.functions, 0);
}

#[test]
fn test_no_params() {
    let decl = IRDecl {
        name: name("unit"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Unreachable,
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params.len(), 0);
}

#[test]
fn test_unknown_callee_conservative() {
    // f(x) := let r = unknown(x); return r
    // Unknown function -> all args conservatively owned
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_reuse_consumes_slot_and_args() {
    // f(x, y) := let r = reuse x { Ctor(y) }; return r
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object), (var(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: var(2),
            ty: IRType::Object,
            value: IRExpr::Reuse {
                var: var(0),
                ctor: mk_ctor(0),
                args: vec![arg_var(1)],
            },
            rest: Box::new(IRBody::Ret(arg_var(2))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned); // slot
    assert_eq!(borrow.params[1], ParamOwnership::Owned); // arg stored
}

#[test]
fn test_is_shared_read_only() {
    // f(x) := let s = isShared x; return s
    // isShared is a read-only check
    let decl = IRDecl {
        name: name("f"),
        params: vec![(var(0), IRType::Object)],
        return_type: IRType::UInt8,
        body: IRBody::VDecl {
            var: var(1),
            ty: IRType::UInt8,
            value: IRExpr::IsShared(var(0)),
            rest: Box::new(IRBody::Ret(arg_var(1))),
        },
    };
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Borrowed);
}

#[test]
fn test_multiple_params_mixed_ownership() {
    // f(a: Object, b: Object, c: Object) :=
    //   let t = tag(a);        // read-only
    //   let r = Ctor(b);       // consumes b
    //   return r               // c unused
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Borrowed); // a: only tag read
    assert_eq!(borrow.params[1], ParamOwnership::Owned); // b: stored in ctor
    assert_eq!(borrow.params[2], ParamOwnership::Borrowed); // c: unused
}

#[test]
fn test_jmp_args_conservatively_owned() {
    // f(x: Object) :=
    //   jdecl jp(a: Object) := return a
    //   jmp jp [x]
    // Jump args are conservatively owned since JP param ownership
    // is not tracked independently.
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned);
}

#[test]
fn test_max_iterations_bound() {
    // With max_iterations=1, the algorithm should still produce a valid result
    // (possibly less optimal).
    let decl = identity_decl("id", 0);
    let config = BorrowInferConfig {
        max_iterations: 1,
        enabled: true,
    };
    let (map, stats) = infer_ir_borrow(std::slice::from_ref(&decl), &config);
    assert!(stats.iterations <= 1);
    assert!(map.get(&fn_id("id")).is_some());
}

#[test]
fn test_uset_sset_set_tag_all_require_owned() {
    // f(x: Object, y: Object, z: Object) :=
    //   uset x[0] = y;
    //   sset x[0, 0] = z : UInt8;
    //   setTag x 1;
    //   return x
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
    let borrow = infer_ir_borrow_single(&decl);
    assert_eq!(borrow.params[0], ParamOwnership::Owned); // mutated
    assert_eq!(borrow.params[1], ParamOwnership::Owned); // uset value
    assert_eq!(borrow.params[2], ParamOwnership::Owned); // sset value
}
