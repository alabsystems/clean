// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the experimental L5IR -> trust-ir backend.
//!
//! These only build under the `trust-ir-backend` feature (the parent module is
//! itself feature-gated, so this file is only compiled then).

use super::*;
use crate::ir::{IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, VarId};
use clean_kernel::Name;

/// Build `fn const_add() -> u64` whose body is:
///   let x0 : u64 = 40;
///   let x1 : u64 = 2;
///   let x2 : u64 = clean_add(x0, x1);   // Apply to a runtime/intrinsic fn
///   ret x2
///
/// We model the arithmetic as `IRExpr::Apply` (L5IR has no dedicated arith
/// variant — arithmetic lowers to calls), with a sibling `clean_add` decl so
/// the call resolves to a real `FuncId`.
fn arith_decls() -> Vec<IRDecl> {
    // function 0: clean_add(a, b) -> u64  (just returns its first param)
    let add = IRDecl {
        name: Name::from_string("clean_add"),
        params: vec![(VarId(0), IRType::UInt64), (VarId(1), IRType::UInt64)],
        return_type: IRType::UInt64,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };

    // function 1: const_add() -> u64
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(40)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(2)),
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt64,
                value: IRExpr::Apply {
                    fn_id: crate::ir::FnId(Name::from_string("clean_add")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        }),
    };
    let const_add = IRDecl {
        name: Name::from_string("const_add"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    };

    vec![add, const_add]
}

#[test]
fn test_emit_trust_ir_arithmetic_validates() {
    let decls = arith_decls();
    let module = emit_trust_ir(&decls).expect("arithmetic IRDecls should lower to trust-ir");

    // Two functions, in declaration order.
    assert_eq!(module.functions.len(), 2);

    // Syntactic validity: validate_module must report no errors.
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "validate_module reported errors: {errors:?}"
    );
}

/// The P2 semantics-preservation corpus decl:
/// `fn tv_demo(x: u32) -> u32 { (x + 7) * 3 }`, with the arithmetic spelled as
/// `Apply`s to the fixed-width kernel primitives `UInt32.add` / `UInt32.mul`
/// (no sibling decls — the primitives are otherwise-undefined, so they take
/// the native-BinOp lowering path).
fn tv_demo_decl() -> IRDecl {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(7)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(2),
            ty: IRType::UInt32,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("UInt32.add")),
                args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(3),
                ty: IRType::UInt32,
                value: IRExpr::Lit(IRLiteral::UInt32(3)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(4),
                    ty: IRType::UInt32,
                    value: IRExpr::Apply {
                        fn_id: crate::ir::FnId(Name::from_string("UInt32.mul")),
                        args: vec![IRArg::Var(VarId(2)), IRArg::Var(VarId(3))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(4)))),
                }),
            }),
        }),
    };
    IRDecl {
        name: Name::from_string("tv_demo"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body,
    }
}

/// An otherwise-undefined `UInt{8,16,32,64}.{add,sub,mul}` Apply lowers to a
/// NATIVE trust-ir `BinOp` (wrapping, per the ratified numerics policy) — not
/// a call, not `UndefinedFunction`. This is the emission half of the P2
/// semantics-preservation fragment.
#[test]
fn test_uint_arith_apply_lowers_to_native_binop() {
    use trust_ir::inst::{BinOp, Inst};
    use trust_ir::ty::Ty;

    let module = emit_trust_ir(&[tv_demo_decl()]).expect("UInt32 arithmetic should lower natively");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");

    let func = &module.functions[0];
    assert_eq!(func.name, "tv_demo");
    assert_eq!(func.blocks.len(), 1, "straight-line body: single block");
    let insts: Vec<&Inst> = func.blocks[0].body.iter().map(|n| &n.inst).collect();
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                ..
            }
        )),
        "UInt32.add must be a native U32 Add BinOp, got: {insts:?}"
    );
    assert!(
        insts.iter().any(|i| matches!(
            i,
            Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U32,
                ..
            }
        )),
        "UInt32.mul must be a native U32 Mul BinOp, got: {insts:?}"
    );
    assert!(
        !insts.iter().any(|i| matches!(i, Inst::Call { .. })),
        "native arithmetic must not emit calls, got: {insts:?}"
    );
}

/// A USER declaration named like a primitive shadows the native lowering —
/// the existing call path is preserved verbatim (the primitive arm is only
/// reached for otherwise-undefined names).
#[test]
fn test_user_decl_shadows_uint_arith_primitive() {
    use trust_ir::inst::Inst;

    // A user-defined `UInt32.add` (just returns its first param).
    let user_add = IRDecl {
        name: Name::from_string("UInt32.add"),
        params: vec![(VarId(0), IRType::UInt32), (VarId(1), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let module = emit_trust_ir(&[user_add, tv_demo_decl()])
        .expect("user-shadowed primitive should lower as a call");
    let func = module
        .functions
        .iter()
        .find(|f| f.name == "tv_demo")
        .expect("tv_demo emitted");
    let insts: Vec<&Inst> = func.blocks[0].body.iter().map(|n| &n.inst).collect();
    assert!(
        insts.iter().any(|i| matches!(i, Inst::Call { .. })),
        "a user decl named UInt32.add must win (call, not BinOp), got: {insts:?}"
    );
}

/// The primitive arm is defensive about type consistency: a declared result
/// type that disagrees with the primitive's width is refused fail-closed.
#[test]
fn test_uint_arith_declared_type_mismatch_is_unsupported() {
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::UInt64, // disagrees with UInt32.add
        value: IRExpr::Apply {
            fn_id: crate::ir::FnId(Name::from_string("UInt32.add")),
            args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = IRDecl {
        name: Name::from_string("bad_width"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt64,
        body,
    };
    let err = emit_trust_ir(&[decl]).expect_err("width mismatch must be refused");
    assert!(
        matches!(err, TrustIrError::Unsupported(_)),
        "expected Unsupported, got: {err:?}"
    );
}

/// The primitive table: exactly `UInt{8,16,32,64}.{add,sub,mul}` — `Nat.*`,
/// `USize.*`, and `div`/`mod` are deliberately excluded (fail-closed).
#[test]
fn test_uint_arith_binop_table_boundaries() {
    use trust_ir::inst::BinOp;
    use trust_ir::ty::Ty;

    assert_eq!(uint_arith_binop("UInt8.add"), Some((BinOp::Add, Ty::U8)));
    assert_eq!(uint_arith_binop("UInt16.sub"), Some((BinOp::Sub, Ty::U16)));
    assert_eq!(uint_arith_binop("UInt32.mul"), Some((BinOp::Mul, Ty::U32)));
    assert_eq!(uint_arith_binop("UInt64.add"), Some((BinOp::Add, Ty::U64)));
    assert_eq!(
        uint_arith_binop("Nat.add"),
        None,
        "Nat is bignum — never native"
    );
    assert_eq!(
        uint_arith_binop("USize.add"),
        None,
        "USize is host-dependent"
    );
    assert_eq!(
        uint_arith_binop("UInt32.div"),
        None,
        "div has panic semantics"
    );
    assert_eq!(
        uint_arith_binop("UInt32.mod"),
        None,
        "mod has panic semantics"
    );
    assert_eq!(uint_arith_binop("UInt32"), None);
    assert_eq!(uint_arith_binop("add"), None);
}

/// A fixed-width UInt arithmetic primitive referenced as a function VALUE — a
/// `PartialApply { UInt32.add, 2, [] }`, exactly the `instHAddUInt32 =
/// HAdd.mk UInt32.add` shape — has no in-slice body and is deliberately kept
/// out of the certified extern boundary (`uint_arith_binop` names are native
/// BinOps, not link-time symbols), so it previously failed `UndefinedFunction`
/// (the 12 `instH{Add,Mul,Sub}UInt{8,16,32,64}` census stage-3 residue). The
/// emit now synthesizes a native boxed-entry wrapper (unbox → native wrapping
/// `BinOp` → box) and the closure closes over it: the module validates and
/// carries the wrapper's `Add/U32` BinOp — a real, executable native function.
#[test]
fn test_uint_arith_value_reference_synthesizes_native_wrapper() {
    use trust_ir::inst::{BinOp, Inst};
    use trust_ir::ty::Ty;

    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: crate::ir::FnId(Name::from_string("UInt32.add")),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect("UInt32.add closure value must synthesize a native wrapper, not UndefinedFunction");
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "synthesized-wrapper module must validate"
    );
    let wrapper = module
        .functions
        .iter()
        .find(|f| f.name == "UInt32.add.__clean_uint_arith_boxed")
        .expect("native boxed wrapper must be emitted");
    assert!(
        wrapper.instructions().any(|n| matches!(
            n.inst,
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                ..
            }
        )),
        "wrapper body must contain a native U32 Add BinOp"
    );
    // PERCEUS (CAUSE 5, 2026-07-12): the wrapper's two OWNED boxed operands are
    // consumed by `dec` (trust-ir `Release`) after being unboxed — else a
    // heap-boxed arg leaks +1 block per operand per call. Guard the two decs.
    assert_eq!(
        wrapper
            .instructions()
            .filter(|n| matches!(n.inst, Inst::Release { .. }))
            .count(),
        2,
        "wrapper must Release (dec) both owned boxed operands"
    );
}

/// An in-slice USER decl named like a primitive still wins for a VALUE
/// reference: the closure closes over the real user body, and NO synthetic
/// wrapper is generated (the primitive is in-slice, so the synthesizer skips
/// it — fail-closed, no double-definition).
#[test]
fn test_user_decl_shadows_uint_value_reference() {
    let user_add = IRDecl {
        name: Name::from_string("UInt32.add"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: crate::ir::FnId(Name::from_string("UInt32.add")),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[user_add, root], &c1_config())
        .expect("user-shadowed primitive value must lower over the user body");
    assert!(
        module
            .functions
            .iter()
            .all(|f| f.name != "UInt32.add.__clean_uint_arith_boxed"),
        "no synthetic wrapper when the primitive is an in-slice user decl"
    );
}

/// SOUNDNESS FIX (2026-07-12): the target-pinned USize/UInt64 decision
/// procedures (`.decEq`/`.decLt`/`.decLe`) lower to a DIRECT native trust-ir
/// `ICmp` on the two u64 operands — NOT the generic tagged-immediate boxing
/// body (`clean_box((v<<1)|1)`, which truncates at bit 63 so e.g.
/// `decEq(2^63, 0)` would wrongly compute `true`). Each decl carries a decoy
/// generic body (`let b = false; ret b`) that would surface if the native
/// intercept failed to fire. See `native_uint_decision_op`.
#[test]
fn test_usize_uint64_decision_ops_lower_to_native_icmp() {
    use trust_ir::inst::{ICmpOp, Inst};
    use trust_ir::ty::Ty;

    fn dec_decl(name: &str, operand: IRType) -> IRDecl {
        let body = IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Bool,
            value: IRExpr::Lit(IRLiteral::Bool(false)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        };
        IRDecl {
            name: Name::from_string(name),
            params: vec![(VarId(0), operand.clone()), (VarId(1), operand)],
            return_type: IRType::Bool,
            body,
        }
    }

    let cases = [
        ("USize.decEq", IRType::USize, ICmpOp::Eq),
        ("USize.decLt", IRType::USize, ICmpOp::Ult),
        ("USize.decLe", IRType::USize, ICmpOp::Ule),
        ("UInt64.decEq", IRType::UInt64, ICmpOp::Eq),
        ("UInt64.decLt", IRType::UInt64, ICmpOp::Ult),
        ("UInt64.decLe", IRType::UInt64, ICmpOp::Ule),
    ];
    for (name, operand, want_op) in cases {
        let module = emit_trust_ir(&[dec_decl(name, operand)])
            .unwrap_or_else(|e| panic!("{name} should lower to trust-ir: {e:?}"));
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{name}: validation errors: {errors:?}");

        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 1, "{name}: single straight-line block");
        let insts: Vec<&Inst> = func.blocks[0].body.iter().map(|n| &n.inst).collect();
        // The whole body is exactly `icmp <op> u64` then `ret` — no boxing
        // `clean_box`/`clean_unbox` Call and no decoy `ret false` (a `Const` +
        // `Return`) leak from the bypassed generic body.
        match insts.as_slice() {
            [Inst::ICmp {
                op, ty: Ty::U64, ..
            }, Inst::Return { .. }] => {
                assert_eq!(*op, want_op, "{name}: wrong ICmp op")
            }
            other => {
                panic!("{name}: expected `icmp {want_op:?} u64` + `ret`, got: {other:?}")
            }
        }
    }
}

/// `native_uint_decision_op` is FAIL-CLOSED: it fires only for the exact
/// 2×{USize|UInt64} -> Bool decision-procedure shape. A wrong/near-miss name,
/// wrong arity, non-`Bool` result, or boxed/other-width operand keeps the
/// generic body (returns `None`), so no other declaration changes shape.
#[test]
fn test_native_uint_decision_op_fail_closed() {
    use trust_ir::inst::ICmpOp;
    use IRType::{Bool, Object, UInt32, UInt64, USize};

    fn decl(name: &str, params: Vec<IRType>, ret: IRType) -> IRDecl {
        IRDecl {
            name: Name::from_string(name),
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, t)| (VarId(i as u32), t))
                .collect(),
            return_type: ret,
            body: IRBody::Ret(IRArg::Erased),
        }
    }
    let fire = |n: &str, p: Vec<IRType>, r: IRType| native_uint_decision_op(&decl(n, p, r));

    // Fires: all six names on both carriers, plus a mixed USize/UInt64 pair
    // (both are Ty::U64, so the ICmp is sound either way).
    assert_eq!(
        fire("USize.decEq", vec![USize, USize], Bool),
        Some(ICmpOp::Eq)
    );
    assert_eq!(
        fire("USize.decLt", vec![USize, USize], Bool),
        Some(ICmpOp::Ult)
    );
    assert_eq!(
        fire("USize.decLe", vec![USize, USize], Bool),
        Some(ICmpOp::Ule)
    );
    assert_eq!(
        fire("UInt64.decEq", vec![UInt64, UInt64], Bool),
        Some(ICmpOp::Eq)
    );
    assert_eq!(
        fire("UInt64.decLt", vec![UInt64, UInt64], Bool),
        Some(ICmpOp::Ult)
    );
    assert_eq!(
        fire("UInt64.decLe", vec![UInt64, UInt64], Bool),
        Some(ICmpOp::Ule)
    );
    assert_eq!(
        fire("USize.decEq", vec![USize, UInt64], Bool),
        Some(ICmpOp::Eq)
    );

    // Fail-closed on every off-shape input.
    assert_eq!(fire("USize.decEq", vec![USize], Bool), None, "arity 1");
    assert_eq!(
        fire("USize.decEq", vec![USize, USize, USize], Bool),
        None,
        "arity 3"
    );
    assert_eq!(
        fire("USize.decEq", vec![USize, USize], UInt64),
        None,
        "non-Bool result"
    );
    assert_eq!(
        fire("USize.decEq", vec![Object, Object], Bool),
        None,
        "boxed operands"
    );
    assert_eq!(
        fire("UInt32.decEq", vec![UInt32, UInt32], Bool),
        None,
        "UInt32 out of scope"
    );
    assert_eq!(
        fire("USize.decEqZ", vec![USize, USize], Bool),
        None,
        "near-miss name"
    );
    assert_eq!(
        fire("Nat.decEq", vec![Object, Object], Bool),
        None,
        "Nat.decEq excluded"
    );
}

#[test]
fn test_emit_trust_ir_forward_reference_call() {
    // const_add (function index 1) calls clean_add (index 0). Even if we put
    // the caller FIRST, the predicted FuncId must still resolve.
    let mut decls = arith_decls();
    decls.swap(0, 1); // now caller is index 0, callee is index 1
    let module = emit_trust_ir(&decls).expect("forward-referenced call should lower and validate");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
}

#[test]
fn test_emit_trust_ir_binary_round_trips() {
    let decls = arith_decls();
    let module = emit_trust_ir(&decls).expect("lowering should succeed");

    // Binary serialize -> deserialize -> structural equality.
    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded =
        trust_ir::binary::deserialize_module(&bytes).expect("binary round-trip should decode");
    assert_eq!(module, decoded, "binary round-trip changed the module");
}

#[test]
fn test_emit_trust_ir_closure_apply_is_unsupported() {
    // ClosureApply is deliberately rejected in phase 1.
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::ClosureApply {
            closure: IRArg::Var(VarId(0)),
            args: vec![],
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
    };
    let decl = IRDecl {
        name: Name::from_string("uses_closure"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };
    let err = emit_trust_ir(&[decl]).expect_err("ClosureApply must be unsupported");
    assert!(
        matches!(err, TrustIrError::Unsupported(_)),
        "expected Unsupported, got {err:?}"
    );
}

/// Build `fn branch(x : Object) -> u64` exercising a join point reached from
/// the arms of a `Case`:
///
///   jp r : u64 => ret r
///   case x of
///     | C0 => let v1 : u64 = 40; jmp jp(v1)
///     | C1 => let v2 : u64 = 2;  jmp jp(v2)
///
/// This is the control-flow shape (a `JDecl` whose predecessor falls through to
/// `rest`, plus `Case`/`Jmp` with block-argument passing) that a naive lowering
/// leaves with a non-terminated predecessor block. It is a regression guard for
/// exactly that: the predecessor must branch to the `rest` continuation.
fn join_point_decl() -> IRDecl {
    use crate::ir::{CtorInfo, IRAlt, JoinPointId};

    let jp = JoinPointId(0);
    let ctor = |name: &str, tag: u32| CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars: 0,
        num_objects: 0,
        field_types: vec![],
    };
    let arm = |val: u64, lit_var: VarId| {
        Box::new(IRBody::VDecl {
            var: lit_var,
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(val)),
            rest: Box::new(IRBody::Jmp {
                jp,
                args: vec![IRArg::Var(lit_var)],
            }),
        })
    };

    let case = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![
            IRAlt {
                ctor: ctor("C0", 0),
                body: arm(40, VarId(1)),
            },
            IRAlt {
                ctor: ctor("C1", 1),
                body: arm(2, VarId(2)),
            },
        ],
        default: None,
    };

    IRDecl {
        name: Name::from_string("branch"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt64,
        body: IRBody::JDecl {
            jp,
            params: vec![(VarId(10), IRType::UInt64)],
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(10)))),
            rest: Box::new(case),
        },
    }
}

#[test]
fn test_emit_trust_ir_join_point_and_case_validate() {
    let module = emit_trust_ir(&[join_point_decl()])
        .expect("join-point + case IRDecl should lower to trust-ir");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "join-point lowering must terminate every block; validate_module said: {errors:?}"
    );
}

#[test]
fn test_emit_trust_ir_join_point_round_trips() {
    let module = emit_trust_ir(&[join_point_decl()]).expect("lowering should succeed");
    let bytes = trust_ir::binary::serialize_module(&module);
    let decoded =
        trust_ir::binary::deserialize_module(&bytes).expect("binary round-trip should decode");
    assert_eq!(module, decoded, "binary round-trip changed the module");
}

#[test]
fn test_emit_trust_ir_rc_inc_emits_native_retain() {
    // Native ARC (P1): `inc x n` lowers to n core `Inst::Retain`s (each is
    // the +1 operational step) in EVERY mode — even the default Dialect
    // config emits no `clean.rc.*` node for RC ops.
    let body = IRBody::Inc {
        var: VarId(0),
        n: 3,
        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
    };
    let decl = IRDecl {
        name: Name::from_string("bump"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };
    let module = emit_trust_ir(&[decl]).expect("inc should lower natively");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
    let retains = module
        .functions
        .iter()
        .flat_map(|f| f.instructions())
        .filter(|n| matches!(n.inst, trust_ir::inst::Inst::Retain { .. }))
        .count();
    assert_eq!(retains, 3, "`inc x 3` must unroll to exactly 3 Retains");
    assert!(
        module
            .functions
            .iter()
            .flat_map(|f| f.instructions())
            .all(|n| !matches!(n.inst, trust_ir::inst::Inst::DialectOp(_))),
        "native ARC emission must not fall back to clean.rc.* dialect nodes"
    );
}

#[test]
fn test_emit_trust_ir_extern_calls_managed_runtime_validates() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::ir::CtorInfo;

    // fn build(x : Object) -> Object {
    //   let c = Ctor C0 [x];   // -> clean_alloc_ctor (variadic)
    //   inc c;                 // -> native Inst::Retain (P1 native ARC)
    //   let f = Proj 0 c;      // -> clean_ctor_get
    //   ret f
    // }
    let ctor = CtorInfo {
        name: Name::from_string("C0"),
        tag: 0,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    };
    let body = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor,
            args: vec![IRArg::Var(VarId(0))],
        },
        rest: Box::new(IRBody::Inc {
            var: VarId(1),
            n: 1,
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    idx: 0,
                    ty: IRType::Object,
                    arg: IRArg::Var(VarId(1)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        }),
    };
    let decl = IRDecl {
        name: Name::from_string("build"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body,
    };

    let config = TrustIrConfig {
        module_name: "extern_test".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &config)
        .expect("managed-runtime program should lower in ExternCalls mode");

    // Valid trust-ir: variadic clean_alloc_ctor + fixed-arity clean_inc /
    // clean_ctor_get calls all type/arity-check against their declared imports.
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "ExternCalls validation errors: {errors:?}"
    );

    // The runtime symbols are declared as imports and the user fn is present.
    // `clean_inc` is declared but never CALLED: it is the RC-runtime
    // provenance triple trust-cg's ARC lowering routes `Retain` by.
    let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
    for sym in ["clean_alloc_ctor", "clean_inc", "clean_ctor_get", "build"] {
        assert!(
            names.contains(&sym),
            "module missing function `{sym}`: {names:?}"
        );
    }
    // The `inc` is a native Retain, not a clean_inc call.
    assert_eq!(
        module
            .functions
            .iter()
            .flat_map(|f| f.instructions())
            .filter(|n| matches!(n.inst, trust_ir::inst::Inst::Retain { .. }))
            .count(),
        1,
        "`inc c` must lower to exactly one native Retain"
    );
    // No `clean.*` dialect node should remain for these ops (they all lowered to
    // calls or native ARC); the module is pure core trust-ir + external calls.
}

// ────────────────────── C1: dropped-callee extern boundary ──────────────────
//
// The clean-cli #14 dependency boundary drops non-compilable dependencies from
// the emitted slice; `emit_c` still calls their mangled symbols and the linker
// resolves them (runtime shims for the denylisted names). These tests pin the
// trust-ir parity mechanism: `declare_extern_fallbacks` forward-declares such
// `Apply` targets as bodyless `Linkage::External` all-Ptr imports, fail-closed.

/// `ExternCalls` config shared by the C1 boundary tests.
fn c1_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "c1_test".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// `fn root(x : Object) -> Object { let y = <callee>(args); ret y }` — the
/// minimal boxed call site for a dropped callee.
fn c1_root_decl(callee: &str, args: Vec<IRArg>) -> IRDecl {
    IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string(callee)),
                args,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

/// A dropped callee (here `Nat.add`, a PRIMITIVE_DENYLIST shim symbol) is
/// forward-declared as a bodyless `Linkage::External` import with the mangled
/// name and the boxed all-Ptr signature, the module validates with zero
/// errors, and the call site targets the declared import — so the emitted
/// object resolves `l_Nat_add` at link time against the C shim, exactly like
/// `emit_c` output does.
#[test]
fn test_c1_dropped_callee_forward_declared_as_bodyless_extern() {
    use trust_ir::inst::Inst;
    use trust_ir::ty::Ty;

    let root = c1_root_decl("Nat.add", vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))]);
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect("dropped-callee call site must lower via the extern boundary");

    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");

    // The mangled import: bodyless, External linkage, 2×Ptr -> Ptr.
    let ext = module
        .functions
        .iter()
        .find(|f| f.name == "l_Nat_add")
        .expect("dropped callee must be declared under its mangled symbol");
    assert!(ext.blocks.is_empty(), "extern import must be bodyless");
    assert_eq!(ext.linkage, trust_ir::Linkage::External);
    let sig = module.func_type(ext.ty).expect("extern signature interned");
    assert_eq!(sig.params, vec![Ty::Ptr, Ty::Ptr], "boxed all-Ptr params");
    assert_eq!(sig.returns, vec![Ty::Ptr], "boxed Ptr return");
    assert!(!sig.is_vararg);

    // The call site targets the declared import with both args.
    let root_fn = module
        .functions
        .iter()
        .find(|f| f.name == "root")
        .expect("root emitted");
    let call = root_fn
        .instructions()
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == ext.id => Some(args.len()),
            _ => None,
        })
        .expect("root must call the forward-declared extern");
    assert_eq!(call, 2);
}

/// Erased args at a dropped-callee call site are materialized as boxed units
/// (`emit_c` passes `clean_box(0)`), so the declared arity matches the linked
/// C shim's REAL signature — pinned on `toString`, whose `l_toString` shim
/// takes `(ty, inst, x)` with the first two erased at L5IR.
#[test]
fn test_c1_dropped_callee_erased_args_keep_c_shim_arity() {
    use trust_ir::inst::Inst;
    use trust_ir::ty::Ty;

    let root = c1_root_decl(
        "toString",
        vec![IRArg::Erased, IRArg::Erased, IRArg::Var(VarId(0))],
    );
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect("erased-arg dropped-callee call site must lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let ext = module
        .functions
        .iter()
        .find(|f| f.name == "l_toString")
        .expect("l_toString declared");
    let sig = module.func_type(ext.ty).expect("signature interned");
    assert_eq!(
        sig.params,
        vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
        "arity counts erased args (C shim parity)"
    );

    let root_fn = module.functions.iter().find(|f| f.name == "root").unwrap();
    let n_args = root_fn
        .instructions()
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == ext.id => Some(args.len()),
            _ => None,
        })
        .expect("root must call l_toString");
    assert_eq!(n_args, 3, "erased args materialized as boxed units");
}

/// CORRECTNESS GUARD: the boundary applies ONLY to genuinely dropped callees.
/// A callee present in the emitted slice keeps its body — it is never demoted
/// to a mangled extern — and the call still targets the in-slice function.
#[test]
fn test_c1_same_slice_callee_is_never_demoted_to_extern() {
    use trust_ir::inst::Inst;

    let helper = IRDecl {
        name: Name::from_string("helper"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let root = c1_root_decl("helper", vec![IRArg::Var(VarId(0))]);
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[helper, root], &c1_config())
        .expect("in-slice callee must lower as a plain call");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let helper_fn = module
        .functions
        .iter()
        .find(|f| f.name == "helper")
        .expect("in-slice callee emitted under its verbatim name");
    assert!(
        !helper_fn.blocks.is_empty(),
        "in-slice callee must keep its body"
    );
    assert!(
        !module.functions.iter().any(|f| f.name == "l_helper"),
        "in-slice callee must not also be declared as a mangled extern"
    );
    let root_fn = module.functions.iter().find(|f| f.name == "root").unwrap();
    assert!(
        root_fn
            .instructions()
            .any(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == helper_fn.id)),
        "call must target the in-slice body, not an extern"
    );
}

/// FAIL-CLOSED: a dropped callee whose call site does not certify the boxed
/// all-Ptr ABI (scalar result binding or scalar argument) is NOT declared —
/// the existing `UndefinedFunction` refusal is preserved, never a guessed
/// signature.
#[test]
fn test_c1_unfaithful_signature_keeps_undefined_function() {
    // (a) Scalar result binding.
    let scalar_result = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(&[scalar_result], &c1_config())
        .expect_err("scalar result binding must be refused");
    assert!(
        matches!(&err, TrustIrError::UndefinedFunction(n) if n == "Foo.bar"),
        "expected UndefinedFunction(Foo.bar), got: {err:?}"
    );

    // (b) Scalar argument.
    let scalar_arg = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(&[scalar_arg], &c1_config())
        .expect_err("scalar argument must be refused");
    assert!(
        matches!(&err, TrustIrError::UndefinedFunction(n) if n == "Foo.bar"),
        "expected UndefinedFunction(Foo.bar), got: {err:?}"
    );
}

/// Differing arities across call sites of the same dropped callee resolve
/// to the MINIMUM (C5a): an `Apply` with n args asserts the callee's true
/// arity is <= n, so the minimum is the largest signature consistent with
/// every site, and larger sites lower as over-applications
/// (saturated call + `clean_apply_N` extras — the `emit_apply_user`
/// discipline). Here `Foo.bar` is declared with arity 1 and the 2-arg site
/// becomes `clean_apply_1(l_Foo_bar(x), y)`.
#[test]
fn test_c1_arity_conflict_resolves_to_minimum_with_over_application() {
    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect("differing arities resolve to the minimum declaration");
    let foo = module
        .functions
        .iter()
        .find(|f| f.name == "l_Foo_bar")
        .expect("l_Foo_bar must be declared as an extern");
    let foo_ty = &module.func_types[foo.ty.0 as usize];
    assert_eq!(
        foo_ty.params.len(),
        1,
        "declared arity must be the minimum call-site arity"
    );
    // The 2-arg site must route its extra argument through clean_apply_1.
    let apply1 = module
        .functions
        .iter()
        .find(|f| f.name == "clean_apply_1")
        .expect("runtime apply helper present");
    let root_fn = module.functions.iter().find(|f| f.name == "root").unwrap();
    let calls_apply1 = root_fn.blocks.iter().any(|b| {
        b.body
            .iter()
            .any(|n| matches!(&n.inst, trust_ir::Inst::Call { callee, .. } if *callee == apply1.id))
    });
    assert!(
        calls_apply1,
        "over-applied site must lower as saturated call + clean_apply_1"
    );
}

/// FAIL-CLOSED (unchanged by C5a): a call site UNDER a `PartialApply`-
/// certified full arity is an under-application with no faithful lowering —
/// the callee is not declared and keeps the `UndefinedFunction` refusal.
#[test]
fn test_c1_call_under_certified_full_arity_keeps_undefined_function() {
    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            // Certifies Foo.bar's FULL arity as 3.
            value: IRExpr::PartialApply {
                fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                arity: 3,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                // 2-arg CALL site: under the certified full arity of 3.
                value: IRExpr::Apply {
                    fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect_err("under-application of a certified full arity must be refused");
    assert!(
        matches!(&err, TrustIrError::UndefinedFunction(n) if n == "Foo.bar"),
        "expected UndefinedFunction(Foo.bar), got: {err:?}"
    );
}

/// The boundary is `ExternCalls`-only: `Dialect` mode has no runtime and no
/// link story, so a dropped callee keeps the `UndefinedFunction` refusal.
#[test]
fn test_c1_dialect_mode_dropped_callee_still_undefined() {
    let root = c1_root_decl("Nat.add", vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))]);
    let err = emit_trust_ir(&[root]).expect_err("Dialect mode must not forward-declare");
    assert!(
        matches!(&err, TrustIrError::UndefinedFunction(n) if n == "Nat.add"),
        "expected UndefinedFunction(Nat.add), got: {err:?}"
    );
}

/// v23 producer provenance: every function this backend creates — user decls,
/// runtime-ABI imports, dropped-callee externs — is stamped `Producer::Clean`.
#[test]
fn test_producer_provenance_stamped_clean_on_every_function() {
    // ExternCalls: user fn + runtime imports + a dropped-callee extern.
    let root = c1_root_decl("Nat.add", vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))]);
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[root], &c1_config())
        .expect("module should emit");
    for f in &module.functions {
        assert_eq!(
            f.producer,
            Some(trust_ir::Producer::Clean),
            "function `{}` missing Producer::Clean provenance",
            f.name
        );
    }
    // Dialect mode too (provenance is producer-, not mode-, scoped).
    let module = emit_trust_ir(&arith_decls()).expect("dialect module should emit");
    for f in &module.functions {
        assert_eq!(f.producer, Some(trust_ir::Producer::Clean));
    }
}

// ─────────────────────────────────────────────────────────────────────────
// C2 — scalar-representation lowering correctness.
//
// The census's only real-miscompile bucket: (i) an unboxed `Bool`/integer
// scalar `Case` scrutinee dispatched through `clean_obj_tag` (a call on a
// non-pointer, plus the invalid `zext bool -> u32` from `Box{Bool}`); (ii) a
// `clean_ctor_get*` projection out of an unboxed scalar carrier; (iii)
// in-slice call sites whose erased args were DROPPED instead of aligned with
// the callee's parameter list. trust-ir's `validate_module` refused all
// three fail-closed; these tests pin the corrected LOWERED IR shape and —
// for the Bool/scalar dispatch — its behavior under the trust-ir reference
// interpreter (polarity is behavior-tested, not just validator-tested).
// ─────────────────────────────────────────────────────────────────────────

fn c2_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "c2_test".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// A nullary-ctor `IRAlt` (the `Bool.false`/`Bool.true` shape).
fn c2_alt(name: &str, tag: u32, body: IRBody) -> crate::ir::IRAlt {
    crate::ir::IRAlt {
        ctor: crate::ir::CtorInfo {
            name: Name::from_string(name),
            tag,
            num_scalars: 0,
            num_objects: 0,
            field_types: vec![],
        },
        body: Box::new(body),
    }
}

/// `let v : Bool = <lit>; ret v` — a literal case arm (extern-free, so the
/// trust-ir reference interpreter can execute the emitted function).
fn c2_ret_bool_lit(var: VarId, b: bool) -> IRBody {
    IRBody::VDecl {
        var,
        ty: IRType::Bool,
        value: IRExpr::Lit(IRLiteral::Bool(b)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var))),
    }
}

/// `fn not(b: Bool) -> Bool { case b { false => true | true => false } }`.
fn c2_bool_not_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("not"),
        params: vec![(VarId(0), IRType::Bool)],
        return_type: IRType::Bool,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                c2_alt("Bool.false", 0, c2_ret_bool_lit(VarId(1), true)),
                c2_alt("Bool.true", 1, c2_ret_bool_lit(VarId(2), false)),
            ],
            default: None,
        },
    }
}

/// `fn and(x: Bool, y: Bool) -> Bool { case x { false => false | true => y } }`.
fn c2_bool_and_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("and"),
        params: vec![(VarId(0), IRType::Bool), (VarId(1), IRType::Bool)],
        return_type: IRType::Bool,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                c2_alt("Bool.false", 0, c2_ret_bool_lit(VarId(2), false)),
                c2_alt("Bool.true", 1, IRBody::Ret(IRArg::Var(VarId(1)))),
            ],
            default: None,
        },
    }
}

/// `fn xor(x: Bool, y: Bool) -> Bool` with the outer alts DELIBERATELY listed
/// true-first: polarity must key on the ctor TAG, not the alt position.
fn c2_bool_xor_decl() -> IRDecl {
    let not_y = IRBody::Case {
        scrutinee: VarId(1),
        alts: vec![
            c2_alt("Bool.true", 1, c2_ret_bool_lit(VarId(2), false)),
            c2_alt("Bool.false", 0, c2_ret_bool_lit(VarId(3), true)),
        ],
        default: None,
    };
    IRDecl {
        name: Name::from_string("xor"),
        params: vec![(VarId(0), IRType::Bool), (VarId(1), IRType::Bool)],
        return_type: IRType::Bool,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                c2_alt("Bool.true", 1, not_y),
                c2_alt("Bool.false", 0, IRBody::Ret(IRArg::Var(VarId(1)))),
            ],
            default: None,
        },
    }
}

/// Execute `name` in `module` on Bool args via the trust-ir reference
/// interpreter, returning its Bool result.
fn c2_run_bool(module: &trust_ir::Module, name: &str, args: &[bool]) -> bool {
    use trust_ir::interpret::{InterpretValue, Interpreter};
    let f = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("function `{name}` not in module"));
    let out = Interpreter::with_module(module)
        .execute_function(f, args.iter().map(|b| InterpretValue::bool(*b)))
        .unwrap_or_else(|e| panic!("interpreting `{name}`{args:?}: {e}"));
    out.returns
        .first()
        .and_then(InterpretValue::as_bool)
        .unwrap_or_else(|| panic!("`{name}` must return a Bool"))
}

/// Count the `Inst::Call`s in `func` whose callee is the module function
/// named `sym` (0 if `sym` is not even declared).
fn c2_calls_to(module: &trust_ir::Module, func: &trust_ir::Function, sym: &str) -> usize {
    use trust_ir::inst::Inst;
    let Some(target) = module.functions.iter().find(|f| f.name == sym) else {
        return 0;
    };
    func.instructions()
        .filter(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == target.id))
        .count()
}

/// Shape pin (i): a `Bool` scrutinee dispatches on the VALUE via `CondBr` —
/// no `clean_obj_tag` call, no `clean.obj.tag` dialect node — in BOTH modes
/// (the lowering is core trust-ir, mode-independent).
#[test]
fn test_c2_bool_case_lowers_to_condbr_not_obj_tag() {
    use trust_ir::inst::Inst;
    for mode in [RuntimeLowering::ExternCalls, RuntimeLowering::Dialect] {
        let config = TrustIrConfig {
            runtime_lowering: mode,
            ..c2_config()
        };
        let module =
            crate::emit_trust_ir::emit_trust_ir_with_config(&[c2_bool_not_decl()], &config)
                .unwrap_or_else(|e| panic!("bool case must lower in {mode:?}: {e}"));
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let f = module.functions.iter().find(|f| f.name == "not").unwrap();
        assert_eq!(
            f.instructions()
                .filter(|n| matches!(n.inst, Inst::CondBr { .. }))
                .count(),
            1,
            "{mode:?}: bool case must be one CondBr"
        );
        assert_eq!(
            c2_calls_to(&module, f, "clean_obj_tag"),
            0,
            "{mode:?}: no tag read on an unboxed Bool"
        );
        assert!(
            f.instructions()
                .all(|n| !matches!(n.inst, Inst::DialectOp(_))),
            "{mode:?}: bool case needs no dialect node"
        );
    }
}

/// BEHAVIOR guard (i): full truth tables for `not`/`and`/`xor` through the
/// trust-ir reference interpreter over the EMITTED module — a branch-polarity
/// flip (tag 0/1 mapped to the wrong `CondBr` edge) fails here even though
/// the flipped module would still validate.
#[test]
fn test_c2_bool_case_polarity_truth_tables() {
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[c2_bool_not_decl(), c2_bool_and_decl(), c2_bool_xor_decl()],
        &c2_config(),
    )
    .expect("bool truth-table module must lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    for b in [false, true] {
        assert_eq!(c2_run_bool(&module, "not", &[b]), !b, "not({b})");
    }
    for x in [false, true] {
        for y in [false, true] {
            assert_eq!(c2_run_bool(&module, "and", &[x, y]), x && y, "and({x},{y})");
            assert_eq!(c2_run_bool(&module, "xor", &[x, y]), x ^ y, "xor({x},{y})");
        }
    }
}

/// Shape + behavior pin (i): an unboxed INTEGER scalar scrutinee (the
/// `Nat.max` shape — a `USize`/`UInt64` holding a Bool tag after `Unbox`)
/// switches on the value directly; case tags select arms, anything else
/// falls to the default.
#[test]
fn test_c2_scalar_case_switches_on_value_directly() {
    use trust_ir::interpret::{InterpretValue, Interpreter};

    let ret_u32 = |var: VarId, v: u32| IRBody::VDecl {
        var,
        ty: IRType::UInt32,
        value: IRExpr::Lit(IRLiteral::UInt32(v)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var))),
    };
    let decl = IRDecl {
        name: Name::from_string("dispatch"),
        params: vec![(VarId(0), IRType::UInt64)],
        return_type: IRType::UInt32,
        body: IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                c2_alt("C0", 0, ret_u32(VarId(1), 10)),
                c2_alt("C1", 1, ret_u32(VarId(2), 20)),
            ],
            default: Some(Box::new(ret_u32(VarId(3), 99))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &c2_config())
        .expect("scalar case must lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let f = module
        .functions
        .iter()
        .find(|f| f.name == "dispatch")
        .unwrap();
    assert_eq!(
        c2_calls_to(&module, f, "clean_obj_tag"),
        0,
        "no tag read on an unboxed scalar"
    );

    let interp = Interpreter::with_module(&module);
    for (input, expected) in [(0u64, 10u128), (1, 20), (7, 99)] {
        let out = interp
            .execute_function(
                f,
                [InterpretValue::int(trust_ir::ty::Ty::U64, input as i128).unwrap()],
            )
            .unwrap_or_else(|e| panic!("dispatch({input}): {e}"));
        let got = out
            .returns
            .first()
            .and_then(InterpretValue::as_int)
            .expect("u32 return")
            .as_unsigned();
        assert_eq!(got, expected, "dispatch({input})");
    }
}

/// Shape + behavior pin (ii): a same-width `SProj` out of an unboxed scalar
/// carrier (the `Char.val` shape: `sproj` on a `U32`) is the IDENTITY — no
/// runtime call at all.
#[test]
fn test_c2_scalar_carrier_sproj_is_identity() {
    use trust_ir::inst::Inst;
    use trust_ir::interpret::{InterpretValue, Interpreter};

    let decl = IRDecl {
        name: Name::from_string("char_val"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::SProj {
                n: 1,
                offset: 0,
                var: VarId(0),
                ty: IRType::UInt32,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &c2_config())
        .expect("scalar-carrier sproj must lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let f = module
        .functions
        .iter()
        .find(|f| f.name == "char_val")
        .unwrap();
    assert!(
        f.instructions()
            .all(|n| !matches!(n.inst, Inst::Call { .. })),
        "identity projection must emit no runtime call"
    );
    let out = Interpreter::with_module(&module)
        .execute_function(f, [InterpretValue::int(trust_ir::ty::Ty::U32, 65).unwrap()])
        .expect("char_val(65)");
    assert_eq!(
        out.returns
            .first()
            .and_then(InterpretValue::as_int)
            .map(|i| i.as_unsigned()),
        Some(65),
        "Char.val is the identity on the carrier"
    );
}

/// Shape pin (ii): an OBJECT-typed `Proj` out of a scalar carrier (the
/// `UInt8.toBitVec` / `Char.valid` / `dite` shapes) re-boxes the carrier with
/// the runtime's tagged `clean_box` convention — never `clean_ctor_get` on a
/// non-pointer. The Bool carrier widens through a `Select` (no Bool zext
/// exists in trust-ir).
#[test]
fn test_c2_scalar_carrier_proj_object_reboxes() {
    use trust_ir::inst::Inst;

    let proj_decl = |name: &str, carrier: IRType| IRDecl {
        name: Name::from_string(name),
        params: vec![(VarId(0), carrier)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::Object,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[
            proj_decl("to_bitvec", IRType::UInt8),
            proj_decl("decidable_proof", IRType::Bool),
        ],
        &c2_config(),
    )
    .expect("scalar-carrier object proj must lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    for name in ["to_bitvec", "decidable_proof"] {
        let f = module.functions.iter().find(|f| f.name == name).unwrap();
        assert_eq!(
            c2_calls_to(&module, f, "clean_box"),
            1,
            "`{name}`: carrier re-boxed with the tagged clean_box convention"
        );
        assert_eq!(
            c2_calls_to(&module, f, "clean_ctor_get"),
            0,
            "`{name}`: no field read on a non-pointer"
        );
    }
    let bool_proj = module
        .functions
        .iter()
        .find(|f| f.name == "decidable_proof")
        .unwrap();
    assert!(
        bool_proj
            .instructions()
            .any(|n| matches!(n.inst, Inst::Select { .. })),
        "Bool carrier must widen via Select (trust-ir has no Bool zext)"
    );
}

/// Fail-closed pin (ii): a WIDTH-CHANGING scalar projection out of a scalar
/// carrier has no faithful lowering and is refused as `Unsupported` — never
/// emitted as the invalid `clean_ctor_get*`-on-scalar call.
#[test]
fn test_c2_scalar_carrier_proj_width_mismatch_refused() {
    let decl = IRDecl {
        name: Name::from_string("bad_narrow"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::UInt8,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt8,
            value: IRExpr::Proj {
                idx: 0,
                ty: IRType::UInt8,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &c2_config())
        .expect_err("width-changing scalar-carrier projection must be refused");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m) if m.contains("scalar carrier")),
        "expected the scalar-carrier refusal, got: {err:?}"
    );
}

/// Shape pin (iii): erased args at an IN-SLICE call site are materialized
/// positionally (boxed unit in `ExternCalls`, null in `Dialect`), never
/// dropped — the `And.symm` shape: `And.right [Erased, Erased, self]` calls
/// the 3-param decl with THREE args.
#[test]
fn test_c2_in_slice_erased_args_materialized_not_dropped() {
    use trust_ir::inst::Inst;

    let callee = IRDecl {
        name: Name::from_string("And.right"),
        params: vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::Object),
            (VarId(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(2))),
    };
    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("And.right")),
                args: vec![IRArg::Erased, IRArg::Erased, IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };

    for mode in [RuntimeLowering::ExternCalls, RuntimeLowering::Dialect] {
        let config = TrustIrConfig {
            runtime_lowering: mode,
            ..c2_config()
        };
        let module = crate::emit_trust_ir::emit_trust_ir_with_config(
            &[callee.clone(), root.clone()],
            &config,
        )
        .unwrap_or_else(|e| panic!("erased-arg in-slice call must lower in {mode:?}: {e}"));
        assert!(trust_ir_build::validate_module(&module).is_empty());

        let target = module
            .functions
            .iter()
            .find(|f| f.name == "And.right")
            .unwrap();
        let root_fn = module.functions.iter().find(|f| f.name == "root").unwrap();
        let n_args = root_fn
            .instructions()
            .find_map(|n| match &n.inst {
                Inst::Call { callee, args } if *callee == target.id => Some(args.len()),
                _ => None,
            })
            .expect("root must call And.right directly");
        assert_eq!(n_args, 3, "{mode:?}: erased args aligned, not dropped");

        match mode {
            RuntimeLowering::ExternCalls => assert_eq!(
                c2_calls_to(&module, root_fn, "clean_box_uint64"),
                2,
                "ExternCalls materializes erased slots as boxed units"
            ),
            RuntimeLowering::Dialect => assert_eq!(
                root_fn
                    .instructions()
                    .filter(|n| matches!(n.inst, Inst::NullPtr))
                    .count(),
                2,
                "Dialect (no runtime) materializes erased slots as nulls"
            ),
        }
    }
}

/// Shape pin (iii): OVER-application — the `Functor.mapRev` shape: the full
/// 6-arg spine against a 2-param projection decl becomes the saturated
/// 2-arg call, then `clean_apply_4` on its result (the Lean/`emit_c`
/// discipline). `Dialect` mode (no closure runtime) refuses fail-closed.
#[test]
fn test_c2_over_application_lowers_via_clean_apply() {
    use trust_ir::inst::Inst;

    let callee = IRDecl {
        name: Name::from_string("Functor.map"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(1))),
    };
    let root = IRDecl {
        name: Name::from_string("root"),
        params: vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::Object),
            (VarId(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(3),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("Functor.map")),
                args: vec![
                    IRArg::Erased,
                    IRArg::Var(VarId(0)),
                    IRArg::Erased,
                    IRArg::Erased,
                    IRArg::Var(VarId(1)),
                    IRArg::Var(VarId(2)),
                ],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
        },
    };

    let module = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[callee.clone(), root.clone()],
        &c2_config(),
    )
    .expect("over-applied in-slice call must lower via clean_apply");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let target = module
        .functions
        .iter()
        .find(|f| f.name == "Functor.map")
        .unwrap();
    let root_fn = module.functions.iter().find(|f| f.name == "root").unwrap();
    let direct_args = root_fn
        .instructions()
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == target.id => Some(args.len()),
            _ => None,
        })
        .expect("saturated call to Functor.map");
    assert_eq!(direct_args, 2, "saturated call takes exactly the params");
    assert_eq!(
        c2_calls_to(&module, root_fn, "clean_apply_4"),
        1,
        "the 4 extra spine args apply to the result via clean_apply_4"
    );

    // Dialect mode has no closure runtime: refuse, never emit a wrong-arity call.
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(
        &[callee, root],
        &TrustIrConfig {
            runtime_lowering: RuntimeLowering::Dialect,
            ..c2_config()
        },
    )
    .expect_err("Dialect mode must refuse over-application");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m) if m.contains("over-applies")),
        "expected the over-application refusal, got: {err:?}"
    );
}

/// Fail-closed pin (iii): UNDER-application of an in-slice callee (no
/// `PartialApply` node) is refused as `Unsupported` — never emitted as a
/// wrong-arity call for the validator to catch.
#[test]
fn test_c2_under_application_refused() {
    let callee = IRDecl {
        name: Name::from_string("three"),
        params: vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::Object),
            (VarId(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let root = c1_root_decl("three", vec![IRArg::Var(VarId(0))]);
    let err = crate::emit_trust_ir::emit_trust_ir_with_config(&[callee, root], &c2_config())
        .expect_err("under-application must be refused");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m) if m.contains("under-applies")),
        "expected the under-application refusal, got: {err:?}"
    );
}

/// Shape pin (i, Box half): `Box{Bool}` widens through `Select` over `U32`
/// constants and calls `clean_box_uint32` — the old `zext bool -> u32` was
/// invalid IR (`decide`/`decEq` census bucket).
#[test]
fn test_c2_box_bool_widens_via_select() {
    use trust_ir::inst::Inst;

    let decl = IRDecl {
        name: Name::from_string("box_bool"),
        params: vec![(VarId(0), IRType::Bool)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::Bool,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &c2_config())
        .expect("Box{Bool} must lower validly");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let f = module
        .functions
        .iter()
        .find(|f| f.name == "box_bool")
        .unwrap();
    assert!(
        f.instructions()
            .any(|n| matches!(n.inst, Inst::Select { .. })),
        "Bool widening must go through Select"
    );
    assert_eq!(c2_calls_to(&module, f, "clean_box_uint32"), 1);
    assert!(
        f.instructions()
            .all(|n| !matches!(n.inst, Inst::Cast { .. })),
        "no cast may touch the Bool (zext bool -> u32 is invalid IR)"
    );
}

/// BEHAVIOR guard (i), native: Bool-case polarity through trust-cg to a
/// running binary. `main` cases on `true` (must take the tag-1 arm), then on
/// `false` inside it (must take the tag-0 arm) → exit 42; a polarity flip on
/// either edge exits 13/7 instead. Pure scalar body — no runtime to link.
/// Skips (like every native e2e here) when no trust-cg binary is found.
#[test]
fn test_c2_e2e_bool_case_native_returns_42() {
    let target = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found (set CLEAN_TRUST_CG_BIN)");
            return;
        }
    };

    let ret_u64 = |var: VarId, v: u64| IRBody::VDecl {
        var,
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(v)),
        rest: Box::new(IRBody::Ret(IRArg::Var(var))),
    };
    let inner = IRBody::VDecl {
        var: VarId(1),
        ty: IRType::Bool,
        value: IRExpr::Lit(IRLiteral::Bool(false)),
        rest: Box::new(IRBody::Case {
            scrutinee: VarId(1),
            alts: vec![
                c2_alt("Bool.false", 0, ret_u64(VarId(2), 42)),
                c2_alt("Bool.true", 1, ret_u64(VarId(3), 7)),
            ],
            default: None,
        }),
    };
    let decls = vec![IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Bool,
            value: IRExpr::Lit(IRLiteral::Bool(true)),
            rest: Box::new(IRBody::Case {
                scrutinee: VarId(0),
                alts: vec![
                    c2_alt("Bool.false", 0, ret_u64(VarId(4), 13)),
                    c2_alt("Bool.true", 1, inner),
                ],
                default: None,
            }),
        },
    }];

    let module = emit_trust_ir(&decls).expect("bool-case e2e decls should lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("bool_case.tmbc");
    let bin = dir.path().join("bool_case");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    let out = std::process::Command::new(&trust_cg)
        .args(["-O0", "--target", target, "-o"])
        .arg(&bin)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        out.status.success(),
        "trust-cg failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );

    let run = std::process::Command::new(&bin)
        .output()
        .expect("run bool_case");
    assert_eq!(
        run.status.code(),
        Some(42),
        "bool-case polarity flipped in native code; stderr: {}",
        String::from_utf8_lossy(&run.stderr),
    );
}

/// Build the `ExternCalls` `build(x)` module (ctor + inc + proj) used by the
/// object-compile e2e.
fn extern_build_module() -> trust_ir::Module {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::ir::CtorInfo;
    let ctor = CtorInfo {
        name: Name::from_string("C0"),
        tag: 0,
        num_scalars: 0,
        num_objects: 1,
        field_types: vec![IRType::Object],
    };
    let decl = IRDecl {
        name: Name::from_string("build"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Inc {
                var: VarId(1),
                n: 1,
                rest: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::Object,
                    value: IRExpr::Proj {
                        idx: 0,
                        ty: IRType::Object,
                        arg: IRArg::Var(VarId(1)),
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                }),
            }),
        },
    };
    let config = TrustIrConfig {
        module_name: "extern_obj".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    crate::emit_trust_ir::emit_trust_ir_with_config(&[decl], &config)
        .expect("ExternCalls build module should lower")
}

#[test]
fn test_emit_trust_ir_extern_calls_closures_validate() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::ir::FnId;

    // fn add2(a, b) -> Object { ret a }
    let add2 = IRDecl {
        name: Name::from_string("add2"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    // fn make() -> Object { let c = PartialApply add2 /arity 2/ []; ret c }
    let make = IRDecl {
        name: Name::from_string("make"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(Name::from_string("add2")),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    // fn apply_it(c, x) -> Object { let r = ClosureApply c [x]; ret r }
    let apply_it = IRDecl {
        name: Name::from_string("apply_it"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(2),
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args: vec![IRArg::Var(VarId(1))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
        },
    };

    let config = TrustIrConfig {
        module_name: "closures".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&[add2, make, apply_it], &config)
        .expect("closures should lower in ExternCalls mode (no longer Unsupported)");

    // The fn-pointer (fn_addr -> bitcast to Ptr) and clean_alloc_closure /
    // clean_apply_1 calls all type/arity-check against their imports.
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "closure validation errors: {errors:?}");

    let names: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
    for sym in [
        "clean_alloc_closure",
        "clean_apply_1",
        "add2",
        "make",
        "apply_it",
    ] {
        assert!(names.contains(&sym), "missing `{sym}`: {names:?}");
    }
}

fn wide_closure_apply_decl(arity: u32) -> IRDecl {
    let mut params = vec![(VarId(0), IRType::Object)];
    let mut args = Vec::with_capacity(arity as usize);
    for index in 1..=arity {
        params.push((VarId(index), IRType::Object));
        args.push(IRArg::Var(VarId(index)));
    }
    let result = VarId(arity + 1);
    IRDecl {
        name: Name::from_string(&format!("apply_{arity}")),
        params,
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: result,
            ty: IRType::Object,
            value: IRExpr::ClosureApply {
                closure: IRArg::Var(VarId(0)),
                args,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(result))),
        },
    }
}

/// Direct Clean/L5IR -> Trust-IR boundary pin: the ExternCalls backend lowers
/// the exact runtime ceiling to `clean_apply_32`, while arity 33 is refused
/// before an artifact can reach `clean_invoke` and panic. This path is the
/// native Clean frontend handoff and does not pass through Rust MIR.
#[test]
fn test_emit_trust_ir_extern_calls_closure_apply_frontier_32_33() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};

    let config = TrustIrConfig {
        module_name: "closure_frontier".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module =
        crate::emit_trust_ir::emit_trust_ir_with_config(&[wide_closure_apply_decl(32)], &config)
            .expect("arity 32 must lower at the exact clean_invoke ceiling");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "closure validation errors: {errors:?}");
    assert!(
        module
            .functions
            .iter()
            .any(|function| function.name == "clean_apply_32"),
        "arity 32 must route to the positional runtime ABI"
    );

    let error =
        crate::emit_trust_ir::emit_trust_ir_with_config(&[wide_closure_apply_decl(33)], &config)
            .expect_err("arity 33 must be refused beyond the clean_invoke ceiling");
    assert!(
        matches!(&error, TrustIrError::Unsupported(message) if message.contains("33") && message.contains("32")),
        "expected the structured 33 > 32 refusal, got: {error:?}"
    );
}

/// `fn main() -> u64 { let x = box(42); let c = Ctor C0 [x]; dec c; ret 7 }` —
/// a managed-runtime program that allocates a boxed value + a constructor and
/// frees it, then returns 7. Uses only OUT-OF-LINE runtime symbols
/// (clean_box_uint64, clean_alloc_ctor, clean_dec) so it links against the
/// Clean runtime without inline-forwarder shims.
fn e2e_managed_main_decls() -> Vec<IRDecl> {
    use crate::ir::CtorInfo;
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: CtorInfo {
                        name: Name::from_string("C0"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 1,
                        field_types: vec![IRType::Object],
                    },
                    args: vec![IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Dec {
                    var: VarId(2),
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(3),
                        ty: IRType::UInt64,
                        value: IRExpr::Lit(IRLiteral::UInt64(7)),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                    }),
                }),
            }),
        }),
    };
    vec![IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }]
}

/// Higher-order: `fn id(x)->Object { ret x }` and
/// `fn main()->u64 { let c = closure(id); let r = c(box 42); dec r; ret 9 }`.
/// Exercises the closure ABI: `fn_addr` (reified function pointer) →
/// `clean_alloc_closure` → `clean_apply_1`.
///
/// NOTE: this currently asserts only that trust-cg COMPILES the closure module
/// to an object. The full link+run path SEGFAULTs at the indirect call — the
/// reified function-pointer (`Const{Ty::Func, FnDef}` → bitcast → `Ptr` →
/// `clean_alloc_closure` → `clean_invoke`) does not yet produce a callable
/// address at runtime (suspected function-symbol relocation issue in the
/// fn-pointer path). Tracked as the remaining closure-runtime gap; the lowering
/// itself is valid trust-ir (see `test_emit_trust_ir_extern_calls_closures_validate`).
fn e2e_closure_main_decls() -> Vec<IRDecl> {
    use crate::ir::FnId;
    let id = IRDecl {
        name: Name::from_string("id"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let main = IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: IRType::UInt64,
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::Object,
                    value: IRExpr::PartialApply {
                        fn_id: FnId(Name::from_string("id")),
                        arity: 1,
                        args: vec![],
                    },
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(3),
                        ty: IRType::Object,
                        value: IRExpr::ClosureApply {
                            closure: IRArg::Var(VarId(2)),
                            args: vec![IRArg::Var(VarId(1))],
                        },
                        rest: Box::new(IRBody::Dec {
                            var: VarId(3),
                            rest: Box::new(IRBody::VDecl {
                                var: VarId(4),
                                ty: IRType::UInt64,
                                value: IRExpr::Lit(IRLiteral::UInt64(9)),
                                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(4)))),
                            }),
                        }),
                    }),
                }),
            }),
        },
    };
    vec![id, main]
}

#[test]
fn test_emit_trust_ir_e2e_closure_invocation_links_and_runs() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    if !std::path::Path::new(rt_src).is_file() {
        eprintln!("e2e skipped: clean_runtime.c not found");
        return;
    }

    let config = TrustIrConfig {
        module_name: "closure_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module =
        crate::emit_trust_ir::emit_trust_ir_with_config(&e2e_closure_main_decls(), &config)
            .expect("closure main should lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("c.tmbc");
    let mobj = dir.path().join("c.o");
    let rtobj = dir.path().join("rt.o");
    let bin = dir.path().join("cprog");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    // trust-cg compiles the closure module (fn_addr -> clean_alloc_closure ->
    // clean_apply_1, which invokes `id` through the reified pointer). All runtime
    // symbols are out-of-line, so it links against the runtime with no shims.
    let cg = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&mobj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let rt = std::process::Command::new("cc")
        .args(["-c", "-O0", "-I", rt_inc, rt_src, "-o"])
        .arg(&rtobj)
        .output()
        .expect("spawn cc");
    assert!(
        rt.status.success(),
        "cc runtime: {}",
        String::from_utf8_lossy(&rt.stderr)
    );
    let mut link_command = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link_command, arch);
    let link = link_command
        .arg("-o")
        .arg(&bin)
        .arg(&mobj)
        .arg(&rtobj)
        .output()
        .expect("spawn cc link");
    assert!(
        link.status.success(),
        "cc link: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    // The closure invocation calls `id(box 42)` through the function pointer;
    // a correct exit code proves the reified indirect call actually worked.
    // (Requires the trust-cg call-arg round-trip fix, eliminate_redundant_copy_roundtrips.)
    let prog = std::process::Command::new(&bin)
        .output()
        .expect("run closure binary");
    assert_eq!(
        prog.status.code(),
        Some(9),
        "closure program exit mismatch (indirect call worked?); stderr: {}",
        String::from_utf8_lossy(&prog.stderr)
    );
}

/// `fn main() -> u64 { let s = "Clean strings run!"; dec s; ret 7 }` — builds a
/// managed string from a read-only byte global, frees it, then returns 7. Uses
/// only OUT-OF-LINE runtime symbols (clean_mk_string, clean_dec), so it links
/// against the Clean runtime with no inline-forwarder shims.
fn e2e_string_main_decls() -> Vec<IRDecl> {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::String("Clean strings run!".to_string()),
        rest: Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(7)),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            }),
        }),
    };
    vec![IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }]
}

#[test]
fn test_emit_trust_ir_string_literal_emits_byte_global() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let config = TrustIrConfig {
        module_name: "strconst".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&e2e_string_main_decls(), &config)
        .expect("string program should lower in ExternCalls mode");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "string module should validate: {errors:?}"
    );

    // Exactly one read-only byte global, holding the literal + NUL terminator.
    assert_eq!(
        module.globals.len(),
        1,
        "one global per distinct string literal"
    );
    let g = &module.globals[0];
    assert!(!g.mutable, "string data is read-only");
    let expected: Vec<u8> = b"Clean strings run!\0".to_vec();
    match &g.initializer {
        Some(trust_ir::constant::Constant::Aggregate(elems)) => {
            let bytes: Vec<u8> = elems
                .iter()
                .map(|c| match c {
                    trust_ir::constant::Constant::Int(b) => *b as u8,
                    other => panic!("non-byte string global element: {other:?}"),
                })
                .collect();
            assert_eq!(bytes, expected, "global bytes = literal + NUL");
        }
        other => panic!("string global initializer should be a byte Aggregate: {other:?}"),
    }
    match g.ty {
        trust_ir::ty::Ty::Array(_, len) => {
            assert_eq!(len, expected.len() as u64, "Array length = byte count");
        }
        ref other => panic!("string global type should be Ty::Array: {other:?}"),
    }

    // The body takes the global's address and hands it to clean_mk_string.
    let mk = module
        .functions
        .iter()
        .find(|f| f.name == "clean_mk_string")
        .map(|f| f.id)
        .expect("clean_mk_string declared in ExternCalls ABI");
    let main = module
        .functions
        .iter()
        .find(|f| f.name == "main")
        .expect("main function");
    let mut saw_global_addr = false;
    let mut saw_mk_call = false;
    for node in main.instructions() {
        match &node.inst {
            trust_ir::inst::Inst::GlobalAddr { .. } => saw_global_addr = true,
            trust_ir::inst::Inst::Call { callee, .. } if *callee == mk => saw_mk_call = true,
            _ => {}
        }
    }
    assert!(
        saw_global_addr,
        "main should take the string global's address"
    );
    assert!(
        saw_mk_call,
        "main should call clean_mk_string on the global address"
    );
}

#[test]
fn test_emit_trust_ir_e2e_string_links_and_runs() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    if !std::path::Path::new(rt_src).is_file() {
        eprintln!("e2e skipped: clean_runtime.c not found");
        return;
    }

    let config = TrustIrConfig {
        module_name: "string_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(&e2e_string_main_decls(), &config)
        .expect("string main should lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("s.tmbc");
    let mobj = dir.path().join("s.o");
    let rtobj = dir.path().join("rt.o");
    let bin = dir.path().join("sprog");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    let cg = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&mobj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let rt = std::process::Command::new("cc")
        .args(["-c", "-O0", "-I", rt_inc, rt_src, "-o"])
        .arg(&rtobj)
        .output()
        .expect("spawn cc");
    assert!(
        rt.status.success(),
        "cc runtime: {}",
        String::from_utf8_lossy(&rt.stderr)
    );
    let mut link_command = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link_command, arch);
    let link = link_command
        .arg("-o")
        .arg(&bin)
        .arg(&mobj)
        .arg(&rtobj)
        .output()
        .expect("spawn cc link");
    assert!(
        link.status.success(),
        "cc link: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    // clean_mk_string strlen+malloc+memcpy's the read-only byte global, then
    // clean_dec frees it; reaching `ret 7` proves the data global, its
    // GlobalAddr relocation, and the native runtime call all work end to end.
    let prog = std::process::Command::new(&bin)
        .output()
        .expect("run string binary");
    assert_eq!(
        prog.status.code(),
        Some(7),
        "string program exit mismatch (mk_string/global ran?); stderr: {}",
        String::from_utf8_lossy(&prog.stderr)
    );
}

/// Out-of-line forwarders for clean_runtime.h's `static inline` ops, so a
/// trust-cg object that calls them links. `#define static` turns each
/// `static inline` into a plain `inline` definition and the `extern`
/// declarations force the out-of-line definition to be emitted (C99 6.7.4p7).
const CLEAN_RUNTIME_SHIMS_C: &str = r#"
#define static
#include "clean_runtime.h"
#undef static
extern uint16_t clean_num_child_fields(clean_obj*);
extern bool clean_is_scalar(clean_obj*);
extern void clean_inc(clean_obj*);
extern void clean_inc_n(clean_obj*, uint32_t);
extern bool clean_is_exclusive(clean_obj*);
extern clean_obj* clean_box(size_t);
extern size_t clean_unbox(clean_obj*);
extern uint64_t clean_unbox_uint64(clean_obj*);
extern uint32_t clean_unbox_uint32(clean_obj*);
extern double clean_unbox_float(clean_obj*);
extern uint8_t clean_obj_tag(clean_obj*);
extern clean_obj* clean_ctor_get(clean_obj*, size_t);
extern size_t clean_ctor_get_usize(clean_obj*, unsigned);
extern void clean_ctor_set(clean_obj*, size_t, clean_obj*);
extern void clean_ctor_set_tag(clean_obj*, uint8_t);
extern uint8_t clean_ctor_get_uint8(clean_obj*, unsigned);
extern uint16_t clean_ctor_get_uint16(clean_obj*, unsigned);
extern uint32_t clean_ctor_get_uint32(clean_obj*, unsigned);
extern uint64_t clean_ctor_get_uint64(clean_obj*, unsigned);
extern double clean_ctor_get_float(clean_obj*, unsigned);
extern float clean_ctor_get_float32(clean_obj*, unsigned);
extern void clean_ctor_set_uint8(clean_obj*, unsigned, uint8_t);
extern void clean_ctor_set_uint16(clean_obj*, unsigned, uint16_t);
extern void clean_ctor_set_uint32(clean_obj*, unsigned, uint32_t);
extern void clean_ctor_set_uint64(clean_obj*, unsigned, uint64_t);
extern void clean_ctor_set_usize(clean_obj*, unsigned, size_t);
extern void clean_ctor_set_float(clean_obj*, unsigned, double);
extern void clean_ctor_set_float32(clean_obj*, unsigned, float);
extern clean_obj* clean_reset(clean_obj*);
"#;

/// `fn main()->u64 { let x=box(42); let c=Ctor C0[x]; let f=proj0 c;
///   let v=unbox(f); dec c; ret v }` — a full managed program that uses the
/// INLINE runtime ops (clean_ctor_get / clean_unbox_uint64), linked via the
/// out-of-line forwarder shim. Returns the round-tripped 42.
fn e2e_inline_managed_decls() -> Vec<IRDecl> {
    use crate::ir::CtorInfo;
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(42)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: CtorInfo {
                        name: Name::from_string("C0"),
                        tag: 0,
                        num_scalars: 0,
                        num_objects: 1,
                        field_types: vec![IRType::Object],
                    },
                    args: vec![IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::VDecl {
                    var: VarId(3),
                    ty: IRType::Object,
                    value: IRExpr::Proj {
                        idx: 0,
                        ty: IRType::Object,
                        arg: IRArg::Var(VarId(2)),
                    },
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(4),
                        ty: IRType::UInt64,
                        value: IRExpr::Unbox {
                            ty: IRType::UInt64,
                            arg: IRArg::Var(VarId(3)),
                        },
                        rest: Box::new(IRBody::Dec {
                            var: VarId(2),
                            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(4)))),
                        }),
                    }),
                }),
            }),
        }),
    };
    vec![IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body,
    }]
}

#[test]
fn test_emit_trust_ir_e2e_inline_ops_link_and_run() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg not found");
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    if !std::path::Path::new(rt_src).is_file() {
        eprintln!("e2e skipped: clean_runtime.c not found");
        return;
    }

    let config = TrustIrConfig {
        module_name: "inline_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module =
        crate::emit_trust_ir::emit_trust_ir_with_config(&e2e_inline_managed_decls(), &config)
            .expect("inline managed program should lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("m.tmbc");
    let mobj = dir.path().join("m.o");
    let rtobj = dir.path().join("rt.o");
    let shim_c = dir.path().join("shims.c");
    let shimobj = dir.path().join("shims.o");
    let bin = dir.path().join("prog");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");
    std::fs::write(&shim_c, CLEAN_RUNTIME_SHIMS_C).expect("write shims.c");

    let run_cc = |args: &[&std::ffi::OsStr]| -> std::process::Output {
        std::process::Command::new("cc")
            .args(args)
            .output()
            .expect("spawn cc")
    };
    use std::ffi::OsStr;

    let cg = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&mobj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg: {}",
        String::from_utf8_lossy(&cg.stderr)
    );

    let rt = run_cc(&[
        OsStr::new("-c"),
        OsStr::new("-O0"),
        OsStr::new("-I"),
        OsStr::new(rt_inc),
        OsStr::new(rt_src),
        OsStr::new("-o"),
        rtobj.as_os_str(),
    ]);
    assert!(
        rt.status.success(),
        "cc runtime: {}",
        String::from_utf8_lossy(&rt.stderr)
    );

    let sh = run_cc(&[
        OsStr::new("-c"),
        OsStr::new("-O0"),
        OsStr::new("-I"),
        OsStr::new(rt_inc),
        shim_c.as_os_str(),
        OsStr::new("-o"),
        shimobj.as_os_str(),
    ]);
    assert!(
        sh.status.success(),
        "cc shim: {}",
        String::from_utf8_lossy(&sh.stderr)
    );

    let mut link_command = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link_command, arch);
    let link = link_command
        .arg("-o")
        .arg(&bin)
        .arg(&mobj)
        .arg(&rtobj)
        .arg(&shimobj)
        .output()
        .expect("spawn cc link");
    assert!(
        link.status.success(),
        "cc link: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    let prog = std::process::Command::new(&bin)
        .output()
        .expect("run inline managed binary");
    assert_eq!(
        prog.status.code(),
        Some(42),
        "inline managed program exit mismatch (box/ctor/proj/unbox ran?); stderr: {}",
        String::from_utf8_lossy(&prog.stderr)
    );
}

#[test]
fn test_emit_trust_ir_e2e_managed_runtime_links_and_runs() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    if !std::path::Path::new(rt_src).is_file() {
        eprintln!("e2e skipped: clean_runtime.c not found at {rt_src}");
        return;
    }

    // Lower the managed program in ExternCalls mode and validate.
    let config = TrustIrConfig {
        module_name: "managed_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module =
        crate::emit_trust_ir::emit_trust_ir_with_config(&e2e_managed_main_decls(), &config)
            .expect("managed main should lower");
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "validate errors: {:?}",
        trust_ir_build::validate_module(&module)
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("m.tmbc");
    let mobj = dir.path().join("m.o");
    let rtobj = dir.path().join("clean_runtime.o");
    let bin = dir.path().join("prog");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    // trust-cg: managed trust-ir -> object (undefined runtime externals).
    let out = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&mobj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        out.status.success(),
        "trust-cg -c failed:\nstderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    // cc: build the Clean runtime object.
    let rt = std::process::Command::new("cc")
        .args(["-c", "-O0", "-I", rt_inc, rt_src, "-o"])
        .arg(&rtobj)
        .output()
        .expect("spawn cc (runtime)");
    assert!(
        rt.status.success(),
        "cc runtime build failed:\nstderr: {}",
        String::from_utf8_lossy(&rt.stderr)
    );

    // cc: link the trust-cg object against the runtime into an executable.
    let mut link_command = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link_command, arch);
    let link = link_command
        .arg("-o")
        .arg(&bin)
        .arg(&mobj)
        .arg(&rtobj)
        .output()
        .expect("spawn cc (link)");
    assert!(
        link.status.success(),
        "cc link failed:\nstderr: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    // Run: the program allocates a boxed value + ctor, frees it, returns 7.
    let run = std::process::Command::new(&bin)
        .output()
        .expect("run managed binary");
    assert_eq!(
        run.status.code(),
        Some(7),
        "managed program exit mismatch (alloc/box/dec ran?); stderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
fn test_emit_trust_ir_extern_calls_compiles_to_object() {
    let target = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            return;
        }
    };

    let module = extern_build_module();
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("build.tmbc");
    let obj = dir.path().join("build.o");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    // Compile to an OBJECT only (`-c`): no link, so the unresolved Clean-runtime
    // symbols stay as undefined externals (resolved when linked against the
    // Clean runtime). This proves trust-cg lowers the managed-runtime trust-ir,
    // including the variadic `clean_alloc_ctor` call, to real machine code.
    let out = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        out.status.success(),
        "trust-cg -c failed on ExternCalls module:\nstderr: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    assert!(obj.is_file(), "trust-cg produced no object file");

    // The object should reference the runtime symbol as an undefined external.
    if let Ok(nm) = std::process::Command::new("nm").arg(&obj).output() {
        let syms = String::from_utf8_lossy(&nm.stdout);
        assert!(
            syms.contains("clean_alloc_ctor"),
            "object does not reference clean_alloc_ctor:\n{syms}"
        );
    }
}

// ---------------------------------------------------------------------------
// End-to-end: Clean L5IR -> trust-ir -> .tmbc -> trust-cg -> native binary.
//
// This proves the trust-ir backend produces a module that the trust-cg verified
// backend compiles and links into a working executable. It uses the pure subset
// (literals + intra-module call + return) that needs no Clean runtime, no clean
// dialect, and no external symbols.
//
// It SHELLS OUT to the `trust-cg` binary and `cc`, so it is guarded: it locates
// trust-cg via $CLEAN_TRUST_CG_BIN or the sibling debug build and, if neither is
// present/executable, returns early (a trivial pass — not #[ignore]). Host arch
// drives `--target`; only arm64/x86_64 are attempted.
// ---------------------------------------------------------------------------

/// `fn forty_two() -> u64 { ret 42 }` and `fn main() -> u64 { ret forty_two() }`.
fn e2e_main_decls() -> Vec<IRDecl> {
    let forty_two = IRDecl {
        name: Name::from_string("forty_two"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let main = IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("forty_two")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    vec![forty_two, main]
}

/// Wrap a serialized trust-ir module in the `.tmbc` envelope trust-cg reads:
/// `b"tMBC" ++ 1u32_le ++ serialize_module(module)`.
fn tmbc_envelope(module: &trust_ir::Module) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"tMBC");
    bytes.extend_from_slice(&1u32.to_le_bytes());
    bytes.extend_from_slice(&trust_ir::binary::serialize_module(module));
    bytes
}

/// Locate the trust-cg binary, or `None` to skip (tool not available).
fn find_trust_cg() -> Option<std::path::PathBuf> {
    if let Ok(p) = std::env::var("CLEAN_TRUST_CG_BIN") {
        let pb = std::path::PathBuf::from(p);
        if pb.is_file() {
            return Some(pb);
        }
    }
    let sibling = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../trust-cg");
    for profile in ["debug", "release"] {
        let pb = sibling.join("target").join(profile).join("trust-cg");
        if pb.is_file() {
            return Some(pb);
        }
    }
    std::env::var_os("PATH").and_then(|path| {
        std::env::split_paths(&path)
            .map(|dir| dir.join("trust-cg"))
            .find(|candidate| candidate.is_file())
    })
}

/// Add the host-architecture selector understood by Apple's linker driver.
/// ELF toolchains already infer the host architecture and reject `-arch`.
fn add_host_arch_link_arg(command: &mut std::process::Command, arch: &str) {
    if cfg!(target_os = "macos") {
        command.args(["-arch", arch]);
    }
}

#[test]
fn test_emit_trust_ir_e2e_native_binary_returns_42() {
    let target = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!(
                "e2e skipped: trust-cg binary not found (set CLEAN_TRUST_CG_BIN or build \
                 ../trust-cg). The lowering itself is covered by the validate tests."
            );
            return;
        }
    };

    // 1. Lower + validate.
    let module = emit_trust_ir(&e2e_main_decls()).expect("e2e decls should lower");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module errors: {errors:?}");

    // 2. Write the .tmbc envelope.
    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("e2e.tmbc");
    let bin = dir.path().join("e2e");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    // 3. Compile + link via trust-cg (which invokes cc).
    let out = std::process::Command::new(&trust_cg)
        .args(["-O0", "--target", target, "-o"])
        .arg(&bin)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        out.status.success(),
        "trust-cg failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );

    // 4. Run the native binary; its `main` return becomes the exit code.
    let run = std::process::Command::new(&bin)
        .output()
        .expect("run e2e binary");
    assert_eq!(
        run.status.code(),
        Some(42),
        "native binary exit code mismatch; stderr: {}",
        String::from_utf8_lossy(&run.stderr),
    );
}

/// `fn main() -> u64 { jp r => ret r;  let v=7; jmp jp(v) }` — exercises trust-cg
/// codegen for join-point lowering (block params + `br` with arguments) all the
/// way to a running binary. Still pure (no runtime / dialect / externs).
fn e2e_join_point_decls() -> Vec<IRDecl> {
    use crate::ir::JoinPointId;
    let jp = JoinPointId(0);
    let main = IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::JDecl {
            jp,
            params: vec![(VarId(10), IRType::UInt64)],
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(10)))),
            rest: Box::new(IRBody::VDecl {
                var: VarId(0),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(7)),
                rest: Box::new(IRBody::Jmp {
                    jp,
                    args: vec![IRArg::Var(VarId(0))],
                }),
            }),
        },
    };
    vec![main]
}

#[test]
fn test_emit_trust_ir_e2e_join_point_native_returns_7() {
    let target = match std::env::consts::ARCH {
        "aarch64" => "aarch64",
        "x86_64" => "x86_64",
        other => {
            eprintln!("e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            return;
        }
    };

    let module = emit_trust_ir(&e2e_join_point_decls()).expect("join-point main should lower");
    assert!(trust_ir_build::validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("jp.tmbc");
    let bin = dir.path().join("jp");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write .tmbc");

    let out = std::process::Command::new(&trust_cg)
        .args(["-O0", "--target", target, "-o"])
        .arg(&bin)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        out.status.success(),
        "trust-cg failed:\nstderr: {}",
        String::from_utf8_lossy(&out.stderr),
    );

    let run = std::process::Command::new(&bin)
        .output()
        .expect("run jp binary");
    assert_eq!(
        run.status.code(),
        Some(7),
        "join-point binary exit code mismatch; stderr: {}",
        String::from_utf8_lossy(&run.stderr),
    );
}

// ===========================================================================
// Wave A: op-complete differential programs.
//
// Each builds a no-arg `main` returning a scalar whose value is STATICALLY
// KNOWN, exercising L5IR ops that previously had no native-run differential
// coverage (Tag, SetTag, SSet, SProj, USet, UProj, Set, Reset, Reuse,
// IsShared, Case dispatch, Unreachable, JDecl/Jmp, recursive Apply). The
// differential test asserts emit_c and trust-ir agree; because each value is
// known, both must also equal the documented exit code (mod 256).
// ===========================================================================

fn ctor_info(
    name: &str,
    tag: u32,
    num_scalars: u32,
    num_objects: u32,
    field_types: Vec<IRType>,
) -> crate::ir::CtorInfo {
    crate::ir::CtorInfo {
        name: Name::from_string(name),
        tag,
        num_scalars,
        num_objects,
        field_types,
    }
}

fn single_main(body: IRBody, ret: IRType) -> Vec<IRDecl> {
    vec![IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: ret,
        body,
    }]
}

/// Box `u64` 0 into `obj_dst`, then continue with `rest`. Yields a heap object
/// so a constructor holding it is genuinely heap-allocated — a NULLARY ctor is a
/// tagged immediate, on which SetTag/Reset/Reuse/Proj dereference a non-pointer.
/// Uses `scratch` for the scalar literal and `obj_dst` for the boxed object.
fn box_zero(scratch: VarId, obj_dst: VarId, rest: Box<IRBody>) -> IRBody {
    IRBody::VDecl {
        var: scratch,
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(0)),
        rest: Box::new(IRBody::VDecl {
            var: obj_dst,
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(scratch),
            },
            rest,
        }),
    }
}

/// `let f = box 0; let c = Ctor C0[f] tag0 (heap); SetTag c 5; let t = Tag c;
///  dec c; ret t` → 5.
fn e2e_tag_settag_decls() -> Vec<IRDecl> {
    let body = box_zero(
        VarId(10),
        VarId(11),
        Box::new(IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_info("C0", 0, 0, 1, vec![IRType::Object]),
                args: vec![IRArg::Var(VarId(11))],
            },
            rest: Box::new(IRBody::SetTag {
                var: VarId(0),
                tag: 5,
                rest: Box::new(IRBody::VDecl {
                    var: VarId(1),
                    ty: IRType::UInt32,
                    value: IRExpr::Tag(IRArg::Var(VarId(0))),
                    rest: Box::new(IRBody::Dec {
                        var: VarId(0),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    }),
                }),
            }),
        }),
    );
    single_main(body, IRType::UInt32)
}

/// `let c = Ctor C0[u64 slot]; SSet c 0 0 = 42; let s = SProj 0 0 c; dec c; ret s` → 42.
fn e2e_scalar_field_decls() -> Vec<IRDecl> {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("C0", 0, 1, 0, vec![IRType::UInt64]),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(42)),
            rest: Box::new(IRBody::SSet {
                var: VarId(0),
                n: 0,
                offset: 0,
                value: VarId(1),
                ty: IRType::UInt64,
                rest: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::UInt64,
                    value: IRExpr::SProj {
                        n: 0,
                        offset: 0,
                        var: VarId(0),
                        ty: IRType::UInt64,
                    },
                    rest: Box::new(IRBody::Dec {
                        var: VarId(0),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                    }),
                }),
            }),
        }),
    };
    single_main(body, IRType::UInt64)
}

/// `let c = Ctor C0[usize slot]; USet c 0 = 7; let u = UProj 0 c; dec c; ret u` → 7.
fn e2e_usize_field_decls() -> Vec<IRDecl> {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("C0", 0, 1, 0, vec![IRType::USize]),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::USize,
            value: IRExpr::Lit(IRLiteral::USize(7)),
            rest: Box::new(IRBody::USet {
                var: VarId(0),
                idx: 0,
                value: VarId(1),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::USize,
                    value: IRExpr::UProj {
                        idx: 0,
                        var: VarId(0),
                    },
                    rest: Box::new(IRBody::Dec {
                        var: VarId(0),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                    }),
                }),
            }),
        }),
    };
    single_main(body, IRType::USize)
}

/// `let a=box 1; let b=box 2; let c=Ctor C0[a]; Set c 0 b; let f=Proj 0 c;
///  let v=Unbox f; dec c; ret v` → 2. (Set replaces object field 0 in-place.)
fn e2e_set_field_decls() -> Vec<IRDecl> {
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::UInt64,
        value: IRExpr::Lit(IRLiteral::UInt64(1)),
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Box {
                ty: IRType::UInt64,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::UInt64,
                value: IRExpr::Lit(IRLiteral::UInt64(2)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(3),
                    ty: IRType::Object,
                    value: IRExpr::Box {
                        ty: IRType::UInt64,
                        arg: IRArg::Var(VarId(2)),
                    },
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(4),
                        ty: IRType::Object,
                        value: IRExpr::Ctor {
                            info: ctor_info("C0", 0, 0, 1, vec![IRType::Object]),
                            args: vec![IRArg::Var(VarId(1))],
                        },
                        rest: Box::new(IRBody::Set {
                            var: VarId(4),
                            idx: 0,
                            value: VarId(3),
                            rest: Box::new(IRBody::VDecl {
                                var: VarId(5),
                                ty: IRType::Object,
                                value: IRExpr::Proj {
                                    idx: 0,
                                    ty: IRType::Object,
                                    arg: IRArg::Var(VarId(4)),
                                },
                                rest: Box::new(IRBody::VDecl {
                                    var: VarId(6),
                                    ty: IRType::UInt64,
                                    value: IRExpr::Unbox {
                                        ty: IRType::UInt64,
                                        arg: IRArg::Var(VarId(5)),
                                    },
                                    rest: Box::new(IRBody::Dec {
                                        var: VarId(4),
                                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(6)))),
                                    }),
                                }),
                            }),
                        }),
                    }),
                }),
            }),
        }),
    };
    single_main(body, IRType::UInt64)
}

/// `let f = box 0; let c = Ctor C0[f] tag0 (heap); let r = Reset c;
///  let g = box 0; let x = Reuse r as C1[g] tag1; let t = Tag x; dec x; ret t` → 1.
fn e2e_reset_reuse_decls() -> Vec<IRDecl> {
    let body = box_zero(
        VarId(10),
        VarId(11),
        Box::new(IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_info("C0", 0, 0, 1, vec![IRType::Object]),
                args: vec![IRArg::Var(VarId(11))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Reset(VarId(0)),
                rest: Box::new(box_zero(
                    VarId(12),
                    VarId(13),
                    Box::new(IRBody::VDecl {
                        var: VarId(2),
                        ty: IRType::Object,
                        value: IRExpr::Reuse {
                            var: VarId(1),
                            ctor: ctor_info("C1", 1, 0, 1, vec![IRType::Object]),
                            args: vec![IRArg::Var(VarId(13))],
                        },
                        rest: Box::new(IRBody::VDecl {
                            var: VarId(3),
                            ty: IRType::UInt32,
                            value: IRExpr::Tag(IRArg::Var(VarId(2))),
                            rest: Box::new(IRBody::Dec {
                                var: VarId(2),
                                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                            }),
                        }),
                    }),
                )),
            }),
        }),
    );
    single_main(body, IRType::UInt32)
}

/// `let c = Ctor C0[] tag0; let s = IsShared c; (s=0); inc c; let s2 = IsShared c;
///  (s2=1); dec c; dec c; ret s2` → 1.
fn e2e_isshared_decls() -> Vec<IRDecl> {
    // Heap ctor (Inc/Dec are no-ops on tagged immediates, so a nullary ctor
    // would report not-shared even after inc).
    let body = box_zero(
        VarId(10),
        VarId(11),
        Box::new(IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_info("C0", 0, 0, 1, vec![IRType::Object]),
                args: vec![IRArg::Var(VarId(11))],
            },
            rest: Box::new(IRBody::Inc {
                var: VarId(0),
                n: 1,
                rest: Box::new(IRBody::VDecl {
                    var: VarId(1),
                    ty: IRType::Bool,
                    value: IRExpr::IsShared(VarId(0)),
                    rest: Box::new(IRBody::Dec {
                        var: VarId(0),
                        rest: Box::new(IRBody::Dec {
                            var: VarId(0),
                            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                        }),
                    }),
                }),
            }),
        }),
    );
    single_main(body, IRType::Bool)
}

/// `let x = box 0; let c = Ctor C0[x]; let s = IsShared c; (s=0 — a fresh
/// cell's refcount is 1, i.e. IsUnique); dec c; ret s` → 0. The polarity
/// complement of [`e2e_isshared_decls`]: a flipped IsUnique/IsShared boolean
/// sense would return 1 here and 0 there, so the PAIR pins the native-ARC
/// `IsUnique` polarity end-to-end through trust-cg and the runtime (Perceus
/// reuse decisions ride on this bit — a silent flip is wrong-code).
fn e2e_isshared_fresh_decls() -> Vec<IRDecl> {
    let body = box_zero(
        VarId(10),
        VarId(11),
        Box::new(IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_info("C0", 0, 0, 1, vec![IRType::Object]),
                args: vec![IRArg::Var(VarId(11))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Bool,
                value: IRExpr::IsShared(VarId(0)),
                rest: Box::new(IRBody::Dec {
                    var: VarId(0),
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                }),
            }),
        }),
    );
    single_main(body, IRType::Bool)
}

/// `let c = Ctor C1[] tag1; case c { C0 => ret 10 | C1 => ret 20 }` → 20.
fn e2e_case_dispatch_decls() -> Vec<IRDecl> {
    use crate::ir::IRAlt;
    let arm = |val: u32, lit_var: VarId| {
        Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::VDecl {
                var: lit_var,
                ty: IRType::UInt32,
                value: IRExpr::Lit(IRLiteral::UInt32(val)),
                rest: Box::new(IRBody::Ret(IRArg::Var(lit_var))),
            }),
        })
    };
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("C1", 1, 0, 0, vec![]),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                IRAlt {
                    ctor: ctor_info("C0", 0, 0, 0, vec![]),
                    body: arm(10, VarId(1)),
                },
                IRAlt {
                    ctor: ctor_info("C1", 1, 0, 0, vec![]),
                    body: arm(20, VarId(2)),
                },
            ],
            default: None,
        }),
    };
    single_main(body, IRType::UInt32)
}

/// `let c = Ctor C0[] tag0; case c { C0 => ret 7 } default => Unreachable` → 7.
fn e2e_unreachable_decls() -> Vec<IRDecl> {
    use crate::ir::IRAlt;
    let body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("C0", 0, 0, 0, vec![]),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![IRAlt {
                ctor: ctor_info("C0", 0, 0, 0, vec![]),
                body: Box::new(IRBody::Dec {
                    var: VarId(0),
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(1),
                        ty: IRType::UInt32,
                        value: IRExpr::Lit(IRLiteral::UInt32(7)),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    }),
                }),
            }],
            default: Some(Box::new(IRBody::Unreachable)),
        }),
    };
    single_main(body, IRType::UInt32)
}

/// Join point reached from both arms of a `Case`:
/// `jp k(r) => ret r; let c = Ctor C1[]; case c { C0 => jmp k(10) | C1 => jmp k(20) }` → 20.
fn e2e_join_point_main_decls() -> Vec<IRDecl> {
    use crate::ir::{IRAlt, JoinPointId};
    let jp = JoinPointId(0);
    let arm = |val: u32, lit_var: VarId| {
        Box::new(IRBody::Dec {
            var: VarId(0),
            rest: Box::new(IRBody::VDecl {
                var: lit_var,
                ty: IRType::UInt32,
                value: IRExpr::Lit(IRLiteral::UInt32(val)),
                rest: Box::new(IRBody::Jmp {
                    jp,
                    args: vec![IRArg::Var(lit_var)],
                }),
            }),
        })
    };
    let case = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("C1", 1, 0, 0, vec![]),
            args: vec![],
        },
        rest: Box::new(IRBody::Case {
            scrutinee: VarId(0),
            alts: vec![
                IRAlt {
                    ctor: ctor_info("C0", 0, 0, 0, vec![]),
                    body: arm(10, VarId(1)),
                },
                IRAlt {
                    ctor: ctor_info("C1", 1, 0, 0, vec![]),
                    body: arm(20, VarId(2)),
                },
            ],
            default: None,
        }),
    };
    let body = IRBody::JDecl {
        jp,
        params: vec![(VarId(10), IRType::UInt32)],
        body: Box::new(IRBody::Ret(IRArg::Var(VarId(10)))),
        rest: Box::new(case),
    };
    single_main(body, IRType::UInt32)
}

/// Recursion over a ctor-encoded Nat: `f(n) = case n { Z => 42 | S m => f(m) }`,
/// applied to `S(S(Z))` → 42. Exercises self-recursive `Apply`, `Case`, `Proj`,
/// `Inc`/`Dec`.
fn e2e_recursion_decls() -> Vec<IRDecl> {
    use crate::ir::{FnId, IRAlt};
    // f(n: Object) -> u32
    let f_body = IRBody::Case {
        scrutinee: VarId(0),
        alts: vec![
            IRAlt {
                ctor: ctor_info("Z", 0, 0, 0, vec![]),
                body: Box::new(IRBody::Dec {
                    var: VarId(0),
                    rest: Box::new(IRBody::VDecl {
                        var: VarId(1),
                        ty: IRType::UInt32,
                        value: IRExpr::Lit(IRLiteral::UInt32(42)),
                        rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                    }),
                }),
            },
            IRAlt {
                ctor: ctor_info("S", 1, 0, 1, vec![IRType::Object]),
                body: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::Object,
                    value: IRExpr::Proj {
                        idx: 0,
                        ty: IRType::Object,
                        arg: IRArg::Var(VarId(0)),
                    },
                    rest: Box::new(IRBody::Inc {
                        var: VarId(2),
                        n: 1,
                        rest: Box::new(IRBody::Dec {
                            var: VarId(0),
                            rest: Box::new(IRBody::VDecl {
                                var: VarId(3),
                                ty: IRType::UInt32,
                                value: IRExpr::Apply {
                                    fn_id: FnId(Name::from_string("f")),
                                    args: vec![IRArg::Var(VarId(2))],
                                },
                                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                            }),
                        }),
                    }),
                }),
            },
        ],
        default: None,
    };
    let f = IRDecl {
        name: Name::from_string("f"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt32,
        body: f_body,
    };
    // main() -> u32 { let z = Z; let s1 = S[z]; let s2 = S[s1]; ret f(s2) }
    let main_body = IRBody::VDecl {
        var: VarId(0),
        ty: IRType::Object,
        value: IRExpr::Ctor {
            info: ctor_info("Z", 0, 0, 0, vec![]),
            args: vec![],
        },
        rest: Box::new(IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Ctor {
                info: ctor_info("S", 1, 0, 1, vec![IRType::Object]),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Ctor {
                    info: ctor_info("S", 1, 0, 1, vec![IRType::Object]),
                    args: vec![IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::VDecl {
                    var: VarId(3),
                    ty: IRType::UInt32,
                    value: IRExpr::Apply {
                        fn_id: FnId(Name::from_string("f")),
                        args: vec![IRArg::Var(VarId(2))],
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
                }),
            }),
        }),
    };
    let main = IRDecl {
        name: Name::from_string("main"),
        params: vec![],
        return_type: IRType::UInt32,
        body: main_body,
    };
    vec![f, main]
}

/// Rename the `main` entry decl to `clean_entry` so a shared C `main` wrapper
/// can invoke it as an ordinary function (its `u64` return becomes the process
/// exit code). Only the entry is renamed; callees keep their names.
fn rename_main_to_entry(mut decls: Vec<IRDecl>) -> Vec<IRDecl> {
    for d in &mut decls {
        if d.name.to_string() == "main" {
            d.name = Name::from_string("clean_entry");
        }
    }
    decls
}

/// Compile a program through `emit_c`, link it with a C `main` wrapper that
/// returns `clean_entry()`'s low byte, run it, and return the exit code.
fn diff_emit_c_exit(decls: &[IRDecl], rt_src: &str, rt_inc: &str, dir: &std::path::Path) -> i32 {
    let mut c = crate::emit_c::emit_c(decls).expect("differential program should lower to C");
    // emit_c mangles declaration names (`clean_entry` -> `l_clean__entry`); the
    // trust-ir backend keeps them verbatim. Call the mangled symbol here.
    let entry = crate::mangle::mangle_name(&Name::from_string("clean_entry"));
    c.push_str(&format!(
        "\nint main(void) {{ return (int)({entry}() & 0xFFu); }}\n"
    ));
    let cfile = dir.join("ec.c");
    std::fs::write(&cfile, &c).expect("write emit_c source");
    let bin = dir.join("ec_bin");
    let out = std::process::Command::new("cc")
        .args(["-O0", "-I", rt_inc, "-o"])
        .arg(&bin)
        .arg(&cfile)
        .arg(rt_src)
        .output()
        .expect("spawn cc for emit_c");
    assert!(
        out.status.success(),
        "emit_c compile failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = std::process::Command::new(&bin)
        .output()
        .expect("run emit_c binary");
    run.status.code().expect("emit_c binary exit code")
}

/// Compile the same program through the trust-ir → trust-cg backend, link it
/// with the same kind of C `main` wrapper (plus the inline-op forwarder shim
/// and the runtime), run it, and return the exit code.
fn diff_trust_ir_exit(
    decls: &[IRDecl],
    trust_cg: &std::path::Path,
    target: &str,
    arch: &str,
    rt_src: &str,
    rt_inc: &str,
    dir: &std::path::Path,
) -> i32 {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let config = TrustIrConfig {
        module_name: "diff".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = crate::emit_trust_ir::emit_trust_ir_with_config(decls, &config)
        .expect("differential program should lower to trust-ir");
    assert!(
        trust_ir_build::validate_module(&module).is_empty(),
        "trust-ir module should validate"
    );

    let tmbc = dir.join("ti.tmbc");
    let mobj = dir.join("ti.o");
    let wrap_c = dir.join("ti_wrap.c");
    let wrapobj = dir.join("ti_wrap.o");
    let rtobj = dir.join("ti_rt.o");
    let shim_c = dir.join("ti_shim.c");
    let shimobj = dir.join("ti_shim.o");
    let bin = dir.join("ti_bin");
    std::fs::write(&tmbc, tmbc_envelope(&module)).expect("write tmbc");
    std::fs::write(
        &wrap_c,
        "#include <stdint.h>\nextern uint64_t clean_entry(void);\n\
         int main(void) { return (int)(clean_entry() & 0xFFu); }\n",
    )
    .expect("write trust-ir wrapper");
    std::fs::write(&shim_c, CLEAN_RUNTIME_SHIMS_C).expect("write shim");

    let cg = std::process::Command::new(trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&mobj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );

    let cc_compile = |src: &std::path::Path, obj: &std::path::Path| {
        let out = std::process::Command::new("cc")
            .args(["-c", "-O0", "-I", rt_inc])
            .arg(src)
            .arg("-o")
            .arg(obj)
            .output()
            .expect("spawn cc -c");
        assert!(
            out.status.success(),
            "cc -c {src:?}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    };
    cc_compile(std::path::Path::new(rt_src), &rtobj);
    cc_compile(&wrap_c, &wrapobj);
    cc_compile(&shim_c, &shimobj);

    let mut link_command = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link_command, arch);
    let link = link_command
        .arg("-o")
        .arg(&bin)
        .arg(&mobj)
        .arg(&wrapobj)
        .arg(&rtobj)
        .arg(&shimobj)
        .output()
        .expect("spawn cc link");
    assert!(
        link.status.success(),
        "cc link: {}",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = std::process::Command::new(&bin)
        .output()
        .expect("run trust-ir binary");
    run.status.code().expect("trust-ir binary exit code")
}

/// Differential test: for a representative set of L5IR programs (managed
/// box/ctor/dec, inline box/ctor/proj/unbox, closure partial-apply, and string
/// construction), compile each through BOTH `emit_c` and the trust-ir/trust-cg
/// backend, run both native binaries, and assert the process exit codes agree.
/// This pins the trust-ir backend as observably equivalent to the mature C
/// backend across the managed-runtime ABI.
#[test]
fn test_emit_trust_ir_differential_matches_emit_c() {
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => {
            eprintln!("differential e2e skipped: unsupported host arch {other}");
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("differential e2e skipped: trust-cg binary not found");
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    if !std::path::Path::new(rt_src).is_file() {
        eprintln!("differential e2e skipped: clean_runtime.c not found");
        return;
    }

    // (label, program, expected exit code). The expected value pins each
    // program's semantics so a divergence cannot hide behind "both backends
    // agree on garbage": emit_c == trust-ir == expected (all mod 256).
    let programs: Vec<(&str, Vec<IRDecl>, i32)> = vec![
        (
            "managed_box_ctor_dec",
            rename_main_to_entry(e2e_managed_main_decls()),
            7,
        ),
        (
            "inline_box_ctor_proj_unbox",
            rename_main_to_entry(e2e_inline_managed_decls()),
            42,
        ),
        (
            "closure_partial_apply",
            rename_main_to_entry(e2e_closure_main_decls()),
            9,
        ),
        (
            "string_mk_dec",
            rename_main_to_entry(e2e_string_main_decls()),
            7,
        ),
        // Wave A: op-complete coverage (Tag, SetTag, Set, Proj, Reset, Reuse,
        // IsShared, Case dispatch, Unreachable, JDecl/Jmp, recursive Apply).
        (
            "tag_settag",
            rename_main_to_entry(e2e_tag_settag_decls()),
            5,
        ),
        (
            "set_object_field",
            rename_main_to_entry(e2e_set_field_decls()),
            2,
        ),
        (
            "reset_reuse",
            rename_main_to_entry(e2e_reset_reuse_decls()),
            1,
        ),
        ("isshared", rename_main_to_entry(e2e_isshared_decls()), 1),
        // Polarity complement: fresh (unique) cell reports NOT shared.
        (
            "isshared_fresh",
            rename_main_to_entry(e2e_isshared_fresh_decls()),
            0,
        ),
        (
            "case_dispatch",
            rename_main_to_entry(e2e_case_dispatch_decls()),
            20,
        ),
        (
            "unreachable_default",
            rename_main_to_entry(e2e_unreachable_decls()),
            7,
        ),
        (
            "join_point",
            rename_main_to_entry(e2e_join_point_main_decls()),
            20,
        ),
        (
            "recursion_nat",
            rename_main_to_entry(e2e_recursion_decls()),
            42,
        ),
        // Scalar/usize field writes — formerly blocked by a trust-cg
        // register-allocator bug (a constant materialized into the arg register
        // holding the live ctor pointer was never reloaded before the call);
        // fixed in trust-cg `aarch64_call_arg_implicit_preserves`, so they now
        // run end-to-end.
        (
            "scalar_sset_sproj",
            rename_main_to_entry(e2e_scalar_field_decls()),
            42,
        ),
        (
            "usize_uset_uproj",
            rename_main_to_entry(e2e_usize_field_decls()),
            7,
        ),
    ];

    for (label, decls, expected) in &programs {
        let dir = tempfile::tempdir().expect("tempdir");
        let c_exit = diff_emit_c_exit(decls, rt_src, rt_inc, dir.path());
        let t_exit = diff_trust_ir_exit(decls, &trust_cg, target, arch, rt_src, rt_inc, dir.path());
        assert_eq!(
            c_exit, *expected,
            "emit_c exit for `{label}` should be the known value {expected}, got {c_exit}"
        );
        assert_eq!(
            t_exit, *expected,
            "trust-ir exit for `{label}` should be the known value {expected}, got {t_exit} \
             (emit_c gave {c_exit})"
        );
    }
}

/// Trust-cg-independent lowering check for the scalar-field ops (SSet/SProj)
/// and usize-field ops (USet/UProj): they lower to VALID trust-ir that calls
/// the expected runtime symbol. Complements the end-to-end differential above
/// (which also runs them) by validating the lowering without needing the
/// trust-cg binary — so it still guards against lowering regressions in
/// environments where trust-cg is absent.
#[test]
fn test_emit_trust_ir_scalar_field_ops_lower_and_validate() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    let cfg = TrustIrConfig {
        module_name: "scalar_ops".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let cases: [(&str, Vec<IRDecl>, &str); 2] = [
        ("sset", e2e_scalar_field_decls(), "clean_ctor_set_uint64"),
        ("uset", e2e_usize_field_decls(), "clean_ctor_set_usize"),
    ];
    for (label, decls, expected_call) in cases {
        let module = crate::emit_trust_ir::emit_trust_ir_with_config(&decls, &cfg)
            .unwrap_or_else(|e| panic!("`{label}` should lower: {e:?}"));
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "`{label}` should validate: {errors:?}");
        // The expected runtime symbol must be declared and called.
        let called: std::collections::HashSet<&str> = module
            .functions
            .iter()
            .flat_map(|f| f.instructions())
            .filter_map(|n| match &n.inst {
                trust_ir::inst::Inst::Call { callee, .. } => Some(callee.index()),
                _ => None,
            })
            .filter_map(|idx| {
                module
                    .functions
                    .iter()
                    .find(|f| f.id.index() == idx)
                    .map(|f| f.name.as_str())
            })
            .collect();
        assert!(
            called.contains(expected_call),
            "`{label}` should call `{expected_call}`; called: {called:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// ExternCalls is dialect-free by contract (trust-ir lowering-target subset v2
// producer notes): forms the runtime ABI cannot express are refused
// fail-closed, never silently degraded to out-of-subset `clean.*` DialectOps.
// ---------------------------------------------------------------------------

/// `fn f(o: Object) -> Object { let x = SProj[n=0,off=0,ty=Object](o); ret x }`
/// — a scalar-projection of a NON-scalar (object-typed) field. The width-typed
/// `clean_ctor_get_*` family has no symbol for it.
fn nonscalar_sproj_decls() -> Vec<IRDecl> {
    vec![IRDecl {
        name: Name::from_string("f"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::SProj {
                n: 0,
                offset: 0,
                var: VarId(0),
                ty: IRType::Object,
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }]
}

/// `fn g(o: Object, v: Object) { SSet[n=0,off=0,ty=Object](o) = v; ret }` —
/// the store-side twin of [`nonscalar_sproj_decls`].
fn nonscalar_sset_decls() -> Vec<IRDecl> {
    vec![IRDecl {
        name: Name::from_string("g"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Void,
        body: IRBody::SSet {
            var: VarId(0),
            n: 0,
            offset: 0,
            value: VarId(1),
            ty: IRType::Object,
            rest: Box::new(IRBody::Ret(IRArg::Erased)),
        },
    }]
}

#[test]
fn test_emit_trust_ir_extern_calls_refuses_nonscalar_sproj_sset_fail_closed() {
    // Pre-audit, object-typed sproj/sset fell through to `clean.obj.sproj` /
    // `clean.obj.sset` DialectOps even in ExternCalls mode — the mode's one
    // out-of-subset leak, named (and this refusal sanctioned) by the trust-ir
    // producer notes. They must now fail closed with a structured error.
    let config = TrustIrConfig {
        module_name: "nonscalar_fields".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    for (label, decls) in [
        ("sproj", nonscalar_sproj_decls()),
        ("sset", nonscalar_sset_decls()),
    ] {
        let err = emit_trust_ir_with_config(&decls, &config).expect_err(&format!(
            "non-scalar {label} must be refused in ExternCalls mode, not dialect-emitted"
        ));
        match err {
            TrustIrError::Unsupported(msg) => assert!(
                msg.contains("dialect-free by contract"),
                "`{label}` refusal should name the ExternCalls contract: {msg}"
            ),
            other => panic!("expected TrustIrError::Unsupported for `{label}`, got: {other}"),
        }
    }

    // Dialect mode (the debug/round-trip surface) keeps the fallback: the
    // same programs still lower to opaque `clean.*` nodes there.
    let dialect = TrustIrConfig {
        module_name: "nonscalar_fields_dialect".to_string(),
        runtime_lowering: RuntimeLowering::Dialect,
        ..TrustIrConfig::default()
    };
    for (label, decls) in [
        ("sproj", nonscalar_sproj_decls()),
        ("sset", nonscalar_sset_decls()),
    ] {
        emit_trust_ir_with_config(&decls, &dialect)
            .unwrap_or_else(|e| panic!("Dialect mode must keep lowering `{label}`: {e:?}"));
    }
}

#[test]
fn test_emit_trust_ir_extern_calls_lowers_without_the_clean_dialect() {
    // ExternCalls never consults the dialect, so the `use_clean_dialect:
    // false` pure-core knob must not matter: ctor/reuse/inc/proj programs
    // lower through the runtime ABI alone. (Previously Ctor/Reuse checked
    // `ensure_dialect` before mode dispatch and were wrongly rejected.)
    let config = TrustIrConfig {
        module_name: "no_dialect_extern".to_string(),
        use_clean_dialect: false,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    for (label, decls) in [
        ("managed_box_ctor_dec", e2e_managed_main_decls()),
        ("reset_reuse", e2e_reset_reuse_decls()),
        ("string_mk_dec", e2e_string_main_decls()),
    ] {
        let module = emit_trust_ir_with_config(&decls, &config).unwrap_or_else(|e| {
            panic!("`{label}` must lower in ExternCalls mode with the dialect disabled: {e:?}")
        });
        assert!(
            module
                .functions
                .iter()
                .flat_map(|f| f.instructions())
                .all(|n| !matches!(n.inst, trust_ir::inst::Inst::DialectOp(_))),
            "`{label}` must contain no DialectOp in ExternCalls mode"
        );
    }
}

// ---------------------------------------------------------------------------
// Finalization gating: fail-closed validate_module + opt-in handoff subset.
// ---------------------------------------------------------------------------

/// `fn tag_of(o: Object) -> u32 { let t = Tag(o); ret t }` — the smallest
/// managed-runtime program: `Tag` is a `clean.obj.tag` `DialectInst` in
/// Dialect mode and a `clean_obj_tag` call (+ zext) in ExternCalls mode.
fn tag_decls() -> Vec<IRDecl> {
    vec![IRDecl {
        name: Name::from_string("tag_of"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt32,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::Tag(IRArg::Var(VarId(0))),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }]
}

#[test]
fn test_emit_trust_ir_default_config_pins_host_target() {
    // Every finalized module carries a pinned target by default: the emitted
    // IR is host-targeted by construction (USize -> U64) and ABI pinning
    // requires `target_info` on any module with an FFI boundary.
    let module = emit_trust_ir(&arith_decls()).expect("arith should lower");
    let ti = module
        .target_info
        .as_ref()
        .expect("default config must pin Module::target_info");
    assert!(!ti.triple.is_empty(), "pinned triple must be non-empty");
    assert_eq!(
        ti.pointer_size, 8,
        "the backend lowers USize to U64, so the pinned host must be 64-bit"
    );
    assert_eq!(*ti, host_target_info());
}

#[test]
fn test_emit_trust_ir_missing_target_info_is_rejected_fail_closed() {
    // ExternCalls declares bodyless Clean-runtime imports, so a module with no
    // `target_info` is invalid (`TargetInfoRequired`). The finalization gate
    // must reject it with a structured error — not return an Ok module the
    // caller would have to remember to validate.
    let config = TrustIrConfig {
        module_name: "no_target".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        target_info: None,
        ..TrustIrConfig::default()
    };
    let err = emit_trust_ir_with_config(&arith_decls(), &config)
        .expect_err("an FFI-boundary module without target_info must be rejected");
    match err {
        TrustIrError::Invalid(errors) => {
            assert!(
                errors.iter().any(|e| matches!(
                    e,
                    trust_ir_build::ValidationError::TargetInfoRequired { .. }
                )),
                "expected TargetInfoRequired among: {errors:?}"
            );
        }
        other => panic!("expected TrustIrError::Invalid, got: {other}"),
    }
}

#[test]
fn test_emit_trust_ir_invalid_module_construction_is_rejected() {
    // A deliberate producer bug the lowering forwards blindly: a binding whose
    // DECLARED type (`Object`) diverges from the value the callee actually
    // returns (`UInt64`) — the emitter trusts declared types, so the raw u64
    // flows into the `ptr` return slot. The resulting module is structurally
    // invalid — the finalization gate (validate_module) must catch it and
    // refuse to hand the module out. (Two historical probes were obsoleted as
    // rungs made the shapes lowerable: an under-applied in-slice call — C2's
    // call/parameter alignment refuses it as `Unsupported`, pinned by
    // `test_c2_under_application_refused` — and a scalar-DECLARED binding
    // returned under an Object signature, which C2b's return alignment now
    // legally re-boxes, pinned by
    // `test_c2b_scalar_return_into_object_signature_reboxed`.)
    let scalar_callee = IRDecl {
        name: Name::from_string("gives_u64"),
        params: vec![],
        return_type: IRType::UInt64,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::UInt64,
            value: IRExpr::Lit(IRLiteral::UInt64(7)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let decl = IRDecl {
        name: Name::from_string("bad_ret"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            // Declared Object, but `gives_u64` actually produces a u64: the
            // return alignment (keyed on DECLARED types) sees Object == Object
            // and forwards the raw scalar into the ptr slot.
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("gives_u64")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };

    let err = emit_trust_ir(&[scalar_callee, decl])
        .expect_err("a return-type-mismatched module must not survive finalization");
    match err {
        TrustIrError::Invalid(errors) => {
            assert!(
                errors.iter().any(|e| matches!(
                    e,
                    trust_ir_build::ValidationError::ReturnTypeMismatch { .. }
                )),
                "expected ReturnTypeMismatch among: {errors:?}"
            );
        }
        other => panic!("expected TrustIrError::Invalid, got: {other}"),
    }
}

#[test]
fn test_emit_trust_ir_dialect_mode_fails_handoff_subset_gate() {
    // Dialect mode is structurally out-of-subset: every managed op is an
    // unallowlisted `clean.*` DialectOp. With the opt-in handoff gate on, the
    // backend must reject the module — Dialect is a debug/round-trip mode,
    // not a handoff mode. The versioned lowering-target check (the producer
    // contract) runs before the stricter bridge gate, so the failure
    // surfaces as `OutOfLoweringSubset`.
    let config = TrustIrConfig {
        module_name: "dialect_handoff".to_string(),
        runtime_lowering: RuntimeLowering::Dialect,
        enforce_handoff_subset: true,
        ..TrustIrConfig::default()
    };
    let err = emit_trust_ir_with_config(&tag_decls(), &config)
        .expect_err("a clean.* DialectOp module must fail the handoff subset gate");
    match err {
        TrustIrError::OutOfLoweringSubset {
            version,
            violations,
        } => {
            assert_eq!(version, 2, "checked against the ratified subset v2");
            assert!(!violations.is_empty(), "expected at least one violation");
        }
        other => panic!("expected TrustIrError::OutOfLoweringSubset, got: {other}"),
    }
}

#[test]
fn test_emit_trust_ir_extern_calls_passes_handoff_subset_gate() {
    // ExternCalls emissions stay inside the pinned conformance subset (plain
    // calls + scalar core ops), so the same program passes with the handoff
    // gate enforced.
    let config = TrustIrConfig {
        module_name: "extern_handoff".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        enforce_handoff_subset: true,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&tag_decls(), &config)
        .expect("ExternCalls lowering must be subset-clean");
    assert!(
        module.target_info.is_some(),
        "handoff modules must carry a pinned target"
    );
}

// ---------------------------------------------------------------------------
// Lowering-target conformance subset self-gate (trust-ir
// `docs/lowering-target-subset.md` v2, `trust_ir_conformance::subset`).
//
// Mirrors trust-ir's own `lowering_subset.rs` gate, two-sided:
//   1. every ExternCalls (handoff-mode) emission is subset-CLEAN — zero
//      violations from `module_subset_violations`;
//   2. Dialect-mode emissions carry EXACTLY the known `clean.*` violation
//      set — no more (an emission leak), no fewer (a stale expectation) —
//      so drift on either repo's side is caught here.
// ---------------------------------------------------------------------------

use trust_ir_conformance::subset::{module_subset_violations, SUBSET_VERSION};

#[test]
fn test_trust_ir_lowering_subset_version_is_the_audited_v2() {
    // Audit trail: the 2026-07-04 promotion audit ratified subset v1
    // (`clean.*` ops refused admission; ExternCalls self-gates on the
    // versioned subset). 2026-07-21 re-audit: trust-ir bumped to v2
    // (ae2ded7, "certify fat pointers") — a strictly ADDITIVE expansion
    // (fat-pointer certification joins the allowlists; nothing was removed),
    // so Clean's v1-conformant ExternCalls emissions conform to v2 unchanged
    // (the corpus gate below stays green) and `clean.*` dialect ops remain
    // excluded. A future bump invalidates THIS audit — the pin makes it loud
    // so the producer audit is re-run.
    assert_eq!(
        SUBSET_VERSION, 2,
        "trust-ir bumped its lowering-target subset version: re-run the Clean \
         producer audit (docs/lowering-target-subset.md Producer notes) and \
         update this suite's known-violation expectations"
    );
}

/// Every ExternCalls corpus program (the full lowering surface this suite
/// exercises: pure arith/control, managed RC/ctor/proj, scalar+usize fields,
/// reset/reuse, closures, strings) must emit a subset-clean module.
///
/// `finalize_module` already enforces this unconditionally in ExternCalls
/// mode, so `emit_trust_ir_with_config` returning `Ok` is itself evidence;
/// the direct `module_subset_violations` call here keeps the gate honest
/// against a future relaxation of the finalization gate, and the DialectOp
/// scan pins the mode's dialect-free promise even for ops trust-ir itself
/// allowlists (`vector.*`).
#[test]
fn test_emit_trust_ir_extern_calls_corpus_is_subset_clean() {
    let corpus: Vec<(&str, Vec<IRDecl>)> = vec![
        ("arith", arith_decls()),
        ("join_point_case", vec![join_point_decl()]),
        ("tag", tag_decls()),
        ("pure_main", e2e_main_decls()),
        ("join_point_main", e2e_join_point_decls()),
        ("managed_box_ctor_dec", e2e_managed_main_decls()),
        ("inline_box_ctor_proj_unbox", e2e_inline_managed_decls()),
        ("closure_partial_apply", e2e_closure_main_decls()),
        ("string_mk_dec", e2e_string_main_decls()),
        ("tag_settag", e2e_tag_settag_decls()),
        ("scalar_sset_sproj", e2e_scalar_field_decls()),
        ("usize_uset_uproj", e2e_usize_field_decls()),
        ("set_object_field", e2e_set_field_decls()),
        ("reset_reuse", e2e_reset_reuse_decls()),
        ("isshared", e2e_isshared_decls()),
        ("isshared_fresh", e2e_isshared_fresh_decls()),
        ("case_dispatch", e2e_case_dispatch_decls()),
        ("unreachable_default", e2e_unreachable_decls()),
        ("join_point_case_main", e2e_join_point_main_decls()),
        ("recursion_nat", e2e_recursion_decls()),
    ];
    for (label, decls) in &corpus {
        let config = TrustIrConfig {
            module_name: format!("subset_{label}"),
            runtime_lowering: RuntimeLowering::ExternCalls,
            ..TrustIrConfig::default()
        };
        let module = emit_trust_ir_with_config(decls, &config).unwrap_or_else(|e| {
            panic!("ExternCalls corpus program `{label}` must lower and pass finalization: {e}")
        });
        let violations = module_subset_violations(&module);
        assert!(
            violations.is_empty(),
            "ExternCalls emission for `{label}` is outside lowering-target subset \
             v{SUBSET_VERSION}:\n  {}",
            violations.join("\n  ")
        );
        assert!(
            module
                .functions
                .iter()
                .flat_map(|f| f.instructions())
                .all(|n| !matches!(n.inst, trust_ir::inst::Inst::DialectOp(_))),
            "`{label}` must contain no DialectOp in ExternCalls mode (dialect-free \
             by contract)"
        );
    }
}

/// Native ARC (P1), pinned in BOTH directions over both modes: the RC ops
/// are core `Retain`/`Release`/`IsUnique` instructions (present with the
/// program's exact multiplicity), and the rc externs are never CALLED. In
/// ExternCalls mode the RC-runtime import triple stays DECLARED — that is
/// trust-cg's ARC routing contract — while `clean_inc_n` (subsumed by the
/// Retain unroll) is gone entirely.
#[test]
fn test_emit_trust_ir_native_arc_replaces_rc_extern_calls() {
    use trust_ir::inst::Inst;
    let rc_syms = [
        "clean_inc",
        "clean_inc_n",
        "clean_dec",
        "clean_is_exclusive",
    ];
    for mode in [RuntimeLowering::ExternCalls, RuntimeLowering::Dialect] {
        let config = TrustIrConfig {
            module_name: "native_arc".to_string(),
            runtime_lowering: mode,
            ..TrustIrConfig::default()
        };
        // e2e_isshared_decls: one `inc`, one `IsShared`, two `dec`s.
        let module = emit_trust_ir_with_config(&e2e_isshared_decls(), &config)
            .unwrap_or_else(|e| panic!("isshared program must lower in {mode:?}: {e}"));

        let count = |pred: fn(&Inst) -> bool| {
            module
                .functions
                .iter()
                .flat_map(|f| f.instructions())
                .filter(|n| pred(&n.inst))
                .count()
        };
        assert_eq!(
            count(|i| matches!(i, Inst::Retain { .. })),
            1,
            "{mode:?}: one native Retain"
        );
        assert_eq!(
            count(|i| matches!(i, Inst::Release { .. })),
            2,
            "{mode:?}: two native Releases"
        );
        assert_eq!(
            count(|i| matches!(i, Inst::IsUnique { .. })),
            1,
            "{mode:?}: one native IsUnique (IsShared = !IsUnique via select)"
        );

        // Opposite direction: no rc extern is ever CALLED (declared != called).
        let called_rc: Vec<&str> = module
            .functions
            .iter()
            .flat_map(|f| f.instructions())
            .filter_map(|n| match &n.inst {
                Inst::Call { callee, .. } => Some(*callee),
                _ => None,
            })
            .filter_map(|id| {
                module
                    .functions
                    .iter()
                    .find(|f| f.id == id)
                    .map(|f| f.name.as_str())
            })
            .filter(|name| rc_syms.contains(name))
            .collect();
        assert!(
            called_rc.is_empty(),
            "{mode:?}: rc externs must never be CALLED, got {called_rc:?}"
        );

        match mode {
            RuntimeLowering::ExternCalls => {
                for sym in ["clean_inc", "clean_dec", "clean_is_exclusive"] {
                    assert!(
                        module
                            .functions
                            .iter()
                            .any(|f| f.name == sym && !f.has_body()),
                        "ExternCalls must keep the RC triple `{sym}` declared \
                         (trust-cg's ARC routing contract)"
                    );
                }
                assert!(
                    !module.functions.iter().any(|f| f.name == "clean_inc_n"),
                    "clean_inc_n is subsumed by the Retain unroll"
                );
            }
            // Dialect mode declares no runtime ABI at all; native ARC ops
            // still appear (asserted above) with no triple to route by —
            // fine, Dialect mode is not a handoff surface.
            RuntimeLowering::Dialect => {}
        }
    }
}

/// `fn dialect_probe(o: Object) -> u32 { SetTag o 1; let s = "s"; let t = Tag(o);
/// ret t }` — one void managed op (`clean.obj.set_tag`), one string literal
/// (`clean.str.const`), one value managed op (`clean.obj.tag`): the three
/// dialect-emission shapes, each an audited-and-refused `clean.*` op. (RC ops
/// stopped being a dialect shape with P1 native ARC — `inc`/`dec`/`IsShared`
/// emit core `Retain`/`Release`/`IsUnique` even in Dialect mode — so the void
/// shape is carried by `SetTag` here.)
fn dialect_probe_decls() -> Vec<IRDecl> {
    vec![IRDecl {
        name: Name::from_string("dialect_probe"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt32,
        body: IRBody::SetTag {
            var: VarId(0),
            tag: 1,
            rest: Box::new(IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::String("s".to_string()),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(2),
                    ty: IRType::UInt32,
                    value: IRExpr::Tag(IRArg::Var(VarId(0))),
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
                }),
            }),
        },
    }]
}

#[test]
fn test_emit_trust_ir_dialect_mode_has_exactly_the_known_violations() {
    // Two-sided (like trust-ir's own corpus gate): the Dialect probe must
    // produce EXACTLY these violations. A new violation means an emission
    // path leaked a new out-of-subset construct; a missing one means the
    // expectation (or trust-ir's checker) drifted — both must be looked at.
    // The strings deliberately pin trust-ir's v2 message format; they break
    // loudly (together with the SUBSET_VERSION pin) on any subset revision.
    let expected = vec![
        "fn `dialect_probe` bb0 inst #0: dialect op `clean.obj.set_tag` is outside \
         lowering-target subset v2 (no proven lowering)"
            .to_string(),
        "fn `dialect_probe` bb0 inst #1: dialect op `clean.str.const` is outside \
         lowering-target subset v2 (no proven lowering)"
            .to_string(),
        "fn `dialect_probe` bb0 inst #2: dialect op `clean.obj.tag` is outside \
         lowering-target subset v2 (no proven lowering)"
            .to_string(),
    ];

    // Flag off: Dialect mode stays usable as a debug/round-trip surface, and
    // the direct checker reports the exact known set.
    let config = TrustIrConfig {
        module_name: "dialect_probe".to_string(),
        runtime_lowering: RuntimeLowering::Dialect,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&dialect_probe_decls(), &config)
        .expect("Dialect mode emits without subset enforcement by default");
    assert_eq!(
        module_subset_violations(&module),
        expected,
        "Dialect-mode violation set drifted from the audited known set"
    );

    // Flag on: the production gate carries the same exact set, fail-closed.
    let enforced = TrustIrConfig {
        enforce_handoff_subset: true,
        ..config
    };
    match emit_trust_ir_with_config(&dialect_probe_decls(), &enforced) {
        Err(TrustIrError::OutOfLoweringSubset {
            version,
            violations,
        }) => {
            assert_eq!(version, SUBSET_VERSION);
            assert_eq!(violations, expected);
        }
        other => panic!("expected OutOfLoweringSubset, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Span provenance (debug info): file table + file-granular instruction spans.
// ---------------------------------------------------------------------------

/// Assert FULL span coverage over every function body in `module` (the
/// SPAN-PROVENANCE gate, after trust-ir's `real_lowering_acceptance`):
/// * the debug-info file table is exactly `[expected_file]`;
/// * every emitted `InstrNode` in every body carries a span (`spanned ==
///   total > 0` per function — a partially-spanned body means an emission
///   path lost the thread), and each span points at file-table entry 0 with
///   `line`/`col` 0 (file granularity: L5IR carries no positions).
fn assert_span_provenance(module: &trust_ir::Module, expected_file: &str) {
    assert_eq!(
        module.files,
        vec![expected_file.to_string()],
        "debug-info file table must hold exactly the configured source file"
    );
    for func in module.functions.iter().filter(|f| f.has_body()) {
        let mut total = 0usize;
        let mut spanned = 0usize;
        for block in &func.blocks {
            for node in &block.body {
                total += 1;
                if let Some(span) = node.span {
                    assert_eq!(
                        (span.file, span.line, span.col),
                        (0, 0, 0),
                        "`{}` carries a span outside the decl's file-granular span",
                        func.name
                    );
                    spanned += 1;
                }
            }
        }
        assert!(total > 0, "`{}` lowered to an empty body", func.name);
        assert_eq!(
            spanned, total,
            "`{}` is only PARTIALLY spanned ({spanned}/{total}) — an emission path \
             dropped the span thread",
            func.name
        );
    }
}

#[test]
fn test_emit_trust_ir_extern_calls_spans_cover_every_instruction() {
    // ExternCalls over the string corpus: calls, globals (GlobalAddr),
    // casts, and terminators must ALL carry the decl's file-granular span.
    let config = TrustIrConfig {
        module_name: "spanned_extern".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        source_file: Some("demo/Strings.lean".to_string()),
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&e2e_string_main_decls(), &config)
        .expect("string corpus should lower in ExternCalls mode");
    assert_span_provenance(&module, "demo/Strings.lean");
    // End-to-end resolution: the span points back at the interned path.
    let span = module
        .functions
        .iter()
        .filter(|f| f.has_body())
        .flat_map(|f| f.instructions())
        .find_map(|n| n.span)
        .expect("at least one spanned instruction");
    assert_eq!(
        module.resolve_span(&span),
        Some(("demo/Strings.lean", 0, 0)),
        "SourceSpan::file must resolve through Module::files"
    );
}

#[test]
fn test_emit_trust_ir_dialect_spans_cover_every_instruction() {
    // Dialect mode: `clean.*` DialectInst nodes ride the same span thread.
    let config = TrustIrConfig {
        module_name: "spanned_dialect".to_string(),
        runtime_lowering: RuntimeLowering::Dialect,
        source_file: Some("demo/Tag.lean".to_string()),
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&tag_decls(), &config)
        .expect("tag program should lower in Dialect mode");
    assert_span_provenance(&module, "demo/Tag.lean");
}

#[test]
fn test_emit_trust_ir_no_source_file_emits_spanless_module() {
    // Missing provenance degrades cleanly: no file table, no spans, no panic —
    // byte-identical behavior to the pre-span backend.
    let module = emit_trust_ir(&arith_decls()).expect("arith should lower");
    assert!(
        module.files.is_empty(),
        "no source_file configured, so the file table must stay empty"
    );
    assert!(
        module
            .functions
            .iter()
            .flat_map(|f| f.instructions())
            .all(|n| n.span.is_none()),
        "no source_file configured, so every instruction must be span-less"
    );
}

// ─────────────────────────────────────────────────────────────────────────
// C2b — return-representation alignment — and C4's extern-fallback widening
// (function-VALUE references and `PartialApply` of dropped callees).
// ─────────────────────────────────────────────────────────────────────────

/// `ExternCalls` config shared by the C2b/C4 tests.
fn c4_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "c4_test".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// PEmpty.elim's lifted motive lambda (the last pre-C2b `validate_module`
/// refusal): `Box { ty: Erased }` of a `USize` literal must produce a managed
/// POINTER (the boxed erased unit), never pass the raw u64 through into the
/// `ptr` return slot.
#[test]
fn test_c2b_box_erased_produces_managed_pointer() {
    let decl = IRDecl {
        name: Name::from_string("pempty_motive_lambda"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Erased,
            value: IRExpr::Lit(IRLiteral::USize(0)),
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: IRType::Erased,
                    arg: IRArg::Var(VarId(1)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect("Box{Erased} must lower to a boxed unit, not a raw scalar");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
}

/// C2b return alignment, boxing direction: a body that produces an unboxed
/// scalar where the signature says `ptr` is re-boxed with the runtime's
/// tagged `clean_box` convention (C2's discipline), so the module validates.
#[test]
fn test_c2b_scalar_return_into_object_signature_reboxed() {
    let decl = IRDecl {
        name: Name::from_string("scalar_into_object"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::USize,
            value: IRExpr::Lit(IRLiteral::USize(5)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect("scalar return under an Object signature must re-box");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
}

/// C2b return alignment, mirror direction: an object-typed value returned
/// where the signature says a scalar has NO faithful lowering — refused,
/// never emitted invalid.
#[test]
fn test_c2b_object_return_into_scalar_signature_refused() {
    let decl = IRDecl {
        name: Name::from_string("object_into_scalar"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let err = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect_err("object return under a scalar signature must be refused");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m) if m.contains("return")),
        "expected the return-alignment refusal, got: {err:?}"
    );
}

/// C2b: an ERASED return under a `ptr` signature returns the boxed erased
/// unit (`clean_box_uint64(0)`), the same convention erased args use.
#[test]
fn test_c2b_erased_return_boxed_when_signature_expects_ptr() {
    let decl = IRDecl {
        name: Name::from_string("erased_into_object"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Erased),
    };
    let module = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect("erased return under an Object signature must box the unit");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
}

/// C4: a 0-arg `Apply` of a dropped callee is a function-VALUE reference
/// (`instLENat`'s `Nat.le` field), not a call — it must NOT poison the
/// callee's extern fallback against a real 2-arg call site elsewhere in the
/// module (the `Nat.repr`-class regression), and it lowers as a closure over
/// the declared symbol.
#[test]
fn test_c4_value_ref_and_call_share_extern_fallback() {
    use trust_ir::ty::Ty;

    // root1: real call site, arity 2.
    let root1 = c1_root_decl(
        "Missing.le",
        vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))],
    );
    // root2: function-value reference (0-arg Apply), stored and returned.
    let root2 = IRDecl {
        name: Name::from_string("inst_like"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("Missing.le")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = emit_trust_ir_with_config(&[root1, root2], &c4_config())
        .expect("value ref + agreeing call site must share one extern fallback");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");

    // The fallback is declared once, with the CALL site's arity (2 Ptr params).
    let fallback = module
        .functions
        .iter()
        .find(|f| f.name == "l_Missing_le")
        .expect("extern fallback l_Missing_le must be declared");
    let sig = module.func_type(fallback.ty).expect("signature interned");
    assert_eq!(
        sig.params,
        vec![Ty::Ptr, Ty::Ptr],
        "arity comes from the call site"
    );
}

/// C4: `PartialApply` of a dropped callee closes over its extern fallback
/// (`Iff.symm`'s `PartialApply` of `Iff.mpr`) — the `arity` field certifies
/// the extern signature, and the emitted module validates.
#[test]
fn test_c4_partial_apply_of_dropped_callee_closes_over_fallback() {
    use trust_ir::ty::Ty;

    let decl = IRDecl {
        name: Name::from_string("symm_like"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: crate::ir::FnId(Name::from_string("Missing.mpr")),
                arity: 2,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect("PartialApply of a dropped callee must close over the fallback");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");

    let fallback = module
        .functions
        .iter()
        .find(|f| f.name == "l_Missing_mpr")
        .expect("extern fallback l_Missing_mpr must be declared");
    let sig = module.func_type(fallback.ty).expect("signature interned");
    assert_eq!(
        sig.params,
        vec![Ty::Ptr, Ty::Ptr],
        "arity comes from the PartialApply's arity field"
    );
}

/// FAIL-CLOSED: a `PartialApply` arity that disagrees with a real call site
/// keeps the `UndefinedFunction` refusal (ambiguous signature).
#[test]
fn test_c4_partial_apply_arity_conflict_refused() {
    let decl = IRDecl {
        name: Name::from_string("root"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                arity: 3,
                args: vec![],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: crate::ir::FnId(Name::from_string("Foo.bar")),
                    args: vec![IRArg::Var(VarId(0))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let err = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect_err("PartialApply/call arity conflict must be refused");
    assert!(
        matches!(&err, TrustIrError::UndefinedFunction(n) if n == "Foo.bar"),
        "expected UndefinedFunction(Foo.bar), got: {err:?}"
    );
}

// ═══ F4 PARITY DIFFERENTIAL: emit_c and emit_trust_ir accept and lower the
// SAME over-applied and C2 carrier-projection shapes (with the default
// `check_ir: true`). Before the parity fix, the C path refused whole modules
// (`ir_checker` `ArityMismatch`/`TypeMismatch`) that trust-ir lowered, and
// with `check_ir: false` emitted arity-mismatched C that did not compile. ═══

/// Over-applied direct Apply: `mapish` (1 param, returns Object — a closure)
/// called with the full 3-arg spine. Both backends must lower it as the
/// saturated call + `clean_apply_2` on its result.
fn over_applied_decls() -> Vec<IRDecl> {
    let callee = IRDecl {
        name: Name::from_string("mapish"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let caller = IRDecl {
        name: Name::from_string("caller"),
        params: vec![
            (VarId(0), IRType::Object),
            (VarId(1), IRType::Object),
            (VarId(2), IRType::Object),
        ],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(3),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: crate::ir::FnId(Name::from_string("mapish")),
                args: vec![
                    IRArg::Var(VarId(0)),
                    IRArg::Var(VarId(1)),
                    IRArg::Var(VarId(2)),
                ],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
        },
    };
    vec![callee, caller]
}

/// C2 carrier projection: `char_bits(c : UInt32)` projects the same-width
/// scalar (identity) and re-boxes the carrier to an Object result.
fn carrier_projection_decl() -> IRDecl {
    IRDecl {
        name: Name::from_string("char_bits"),
        params: vec![(VarId(0), IRType::UInt32)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::UInt32,
            value: IRExpr::SProj {
                n: 0,
                offset: 0,
                var: VarId(0),
                ty: IRType::UInt32,
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Proj {
                    idx: 1,
                    ty: IRType::Object,
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    }
}

#[test]
fn test_parity_over_applied_apply_c_and_trustir() {
    let decls = over_applied_decls();

    // C path, default config (check_ir: true): must accept and use the
    // saturated-call + clean_apply_N discipline.
    let c = crate::emit_c::emit_c_with_config(&decls, crate::emit_c::CEmitConfig::default())
        .expect("emit_c must lower the over-applied spine");
    assert!(
        c.contains("clean_apply_2(l_mapish(_x0), _x1, _x2)"),
        "expected saturated call + clean_apply_2, got:\n{c}"
    );

    // trust-ir path, ExternCalls: the same module lowers.
    emit_trust_ir_with_config(&decls, &c1_config())
        .expect("emit_trust_ir must lower the same over-applied spine");
}

#[test]
fn test_parity_carrier_projection_c_and_trustir() {
    let decls = vec![carrier_projection_decl()];

    let c = crate::emit_c::emit_c_with_config(&decls, crate::emit_c::CEmitConfig::default())
        .expect("emit_c must lower the C2 carrier projections");
    assert!(
        c.contains("uint32_t _x1 = _x0;"),
        "same-width SProj must be the identity, got:\n{c}"
    );
    assert!(
        c.contains("clean_box((size_t)_x0)"),
        "object-typed Proj must re-box the carrier, got:\n{c}"
    );
    assert!(
        !c.contains("clean_ctor_get"),
        "no boxed-layout getter may be emitted for an unboxed carrier, got:\n{c}"
    );

    emit_trust_ir_with_config(&decls, &c1_config())
        .expect("emit_trust_ir must lower the same carrier projections");
}

#[test]
fn test_parity_over_applied_rust_backend() {
    // The Rust backend shares the discipline via clean_closure_apply.
    let decls = over_applied_decls();
    let rs = crate::emit_rust::emit_rust_with_config(
        &decls,
        crate::emit_rust::RustEmitConfig::default(),
    )
    .expect("emit_rust must lower the over-applied spine");
    assert!(
        rs.contains("clean_closure_apply(l_mapish(_x0), &[_x1, _x2])"),
        "expected saturated call + clean_closure_apply, got:\n{rs}"
    );
}

/// Regression (RUNG A / Unit constants): a function whose return type carries
/// NO runtime value (`Erased`/`Void`, for which `lower_ret_tys` is empty) but
/// whose body returns a MATERIALIZED value BY VARIABLE must DROP that value at
/// the terminator, not emit it.
///
/// This is the exact shape of the prelude `Unit.unit` definition — its kernel
/// value is `PUnit.unit`, which lowers to
///   `Unit.unit : [] -> Erased  {  let v0 : Erased = USize(0);  ret v0  }`
/// (the erased `USize(0)` placeholder). Before the fix the `Ret(Var _)` arm
/// unconditionally emitted `ret [val]`, giving the terminator arity 1 against
/// the 0-result signature, so `validate_module` rejected it with
///   "bb0: return arity mismatch: expected 0 values, got 1".
/// Both runtime-lowering modes and both empty-value return types must lower and
/// validate. (The sibling `IRArg::Erased` return arm already dropped this way;
/// this closes the `IRArg::Var` gap.)
#[test]
fn test_emit_trust_ir_erased_return_drops_materialized_value() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};

    let unit_shape = |ret_ty: IRType| IRDecl {
        name: Name::from_string("Unit.unit"),
        params: vec![],
        return_type: ret_ty.clone(),
        body: IRBody::VDecl {
            var: VarId(0),
            ty: ret_ty,
            value: IRExpr::Lit(IRLiteral::USize(0)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };

    for ret_ty in [IRType::Erased, IRType::Void] {
        // Dialect (default) mode.
        let module = emit_trust_ir(&[unit_shape(ret_ty.clone())])
            .unwrap_or_else(|e| panic!("Dialect emit for {ret_ty:?} return failed: {e}"));
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "Dialect validation errors for {ret_ty:?} return",
        );

        // ExternCalls (managed-runtime handoff) mode.
        let config = TrustIrConfig {
            runtime_lowering: RuntimeLowering::ExternCalls,
            ..TrustIrConfig::default()
        };
        let module =
            crate::emit_trust_ir::emit_trust_ir_with_config(&[unit_shape(ret_ty.clone())], &config)
                .unwrap_or_else(|e| panic!("ExternCalls emit for {ret_ty:?} return failed: {e}"));
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "ExternCalls validation errors for {ret_ty:?} return",
        );
    }
}
