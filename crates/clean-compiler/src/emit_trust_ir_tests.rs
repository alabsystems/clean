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
                    fn_id: FnId(Name::from_string("clean_add")),
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
    let errors = validate_module(&module);
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
                fn_id: FnId(Name::from_string("UInt32.add")),
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
                        fn_id: FnId(Name::from_string("UInt32.mul")),
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
    let errors = validate_module(&module);
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

/// POLICY INVERSION (2026-08-25, mirroring `emit_wasm::lower_module`): an
/// in-slice decl named like a `UIntW.{add,sub,mul}` primitive is SKIPPED and
/// every call site takes the native wrapping `BinOp`. The old pin ("a user
/// decl must win — call, not BinOp") guarded a shape that cannot arise from a
/// real kernel environment: `UInt32.add` there is the PRELUDE definition
/// (re-registration is `DuplicateName`), whose Lean body is definitionally
/// mod-2^32 add — the compiled-from-source body is dead weight that shadowed
/// the native arm and made every UIntW-arithmetic root uncertifiable (its
/// calls could never ground a Fragment-2/3 certificate). The equivalence is
/// not taken on faith: the TV mint compares the emitted function against the
/// ORIGINAL kernel definition, so a genuine divergence between the native
/// BinOp and the kernel's semantics REFUSES fail-closed at certification.
#[test]
fn test_uint_arith_primitive_in_slice_is_skipped_for_native_binop() {
    use trust_ir::inst::Inst;

    // A hand-built in-slice `UInt32.add` (divergent body: returns its first
    // param). Under the skip its body is never emitted, and call sites get
    // the native BinOp.
    let user_add = IRDecl {
        name: Name::from_string("UInt32.add"),
        params: vec![(VarId(0), IRType::UInt32), (VarId(1), IRType::UInt32)],
        return_type: IRType::UInt32,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let module = emit_trust_ir(&[user_add, tv_demo_decl()])
        .expect("primitive-named decl skips; call sites lower natively");
    assert!(
        module.functions.iter().all(|f| f.name != "UInt32.add"),
        "the primitive's compiled body must not be emitted"
    );
    let func = module
        .functions
        .iter()
        .find(|f| f.name == "tv_demo")
        .expect("tv_demo emitted");
    let insts: Vec<&Inst> = func.blocks[0].body.iter().map(|n| &n.inst).collect();
    assert!(
        insts
            .iter()
            .any(|i| matches!(i, Inst::BinOp { op: BinOp::Add, .. }))
            && !insts.iter().any(|i| matches!(i, Inst::Call { .. })),
        "call sites must be native BinOps, never calls: {insts:?}"
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
            fn_id: FnId(Name::from_string("UInt32.add")),
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
                fn_id: FnId(Name::from_string("UInt32.add")),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = emit_trust_ir_with_config(&[root], &c1_config())
        .expect("UInt32.add closure value must synthesize a native wrapper, not UndefinedFunction");
    assert!(
        validate_module(&module).is_empty(),
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
    // POLICY INVERSION companion (see
    // [`test_uint_arith_primitive_in_slice_is_skipped_for_native_binop`]):
    // with the in-slice primitive SKIPPED, a function-VALUE reference to it
    // must close over the synthesized native boxed-entry wrapper — exactly
    // as if the primitive had never been in the slice.
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
                fn_id: FnId(Name::from_string("UInt32.add")),
                arity: 2,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = emit_trust_ir_with_config(&[user_add, root], &c1_config())
        .expect("value reference to a skipped primitive lowers over the wrapper");
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "UInt32.add.__clean_uint_arith_boxed"),
        "the synthesized wrapper must exist for the value reference"
    );
    assert!(
        module.functions.iter().all(|f| f.name != "UInt32.add"),
        "the primitive's compiled body must not be emitted"
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
fn test_uint_decision_ops_lower_to_native_icmp() {
    use trust_ir::inst::{ICmpOp, Inst};

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
        ("UInt8.decEq", IRType::UInt8, ICmpOp::Eq),
        ("UInt8.decLt", IRType::UInt8, ICmpOp::Ult),
        ("UInt8.decLe", IRType::UInt8, ICmpOp::Ule),
        ("UInt16.decEq", IRType::UInt16, ICmpOp::Eq),
        ("UInt16.decLt", IRType::UInt16, ICmpOp::Ult),
        ("UInt16.decLe", IRType::UInt16, ICmpOp::Ule),
        ("UInt32.decEq", IRType::UInt32, ICmpOp::Eq),
        ("UInt32.decLt", IRType::UInt32, ICmpOp::Ult),
        ("UInt32.decLe", IRType::UInt32, ICmpOp::Ule),
        ("UInt64.decEq", IRType::UInt64, ICmpOp::Eq),
        ("UInt64.decLt", IRType::UInt64, ICmpOp::Ult),
        ("UInt64.decLe", IRType::UInt64, ICmpOp::Ule),
    ];
    for (name, operand, want_op) in cases {
        let expected_ty = lower_ty(&operand);
        let module = emit_trust_ir(&[dec_decl(name, operand)])
            .unwrap_or_else(|e| panic!("{name} should lower to trust-ir: {e:?}"));
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{name}: validation errors: {errors:?}");

        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 1, "{name}: single straight-line block");
        let insts: Vec<&Inst> = func.blocks[0].body.iter().map(|n| &n.inst).collect();
        // The whole body is exactly `icmp <op> u64` then `ret` — no boxing
        // `clean_box`/`clean_unbox` Call and no decoy `ret false` (a `Const` +
        // `Return`) leak from the bypassed generic body.
        match insts.as_slice() {
            [Inst::ICmp { op, ty, .. }, Inst::Return { .. }] => {
                assert_eq!(*ty, expected_ty, "{name}: wrong operand width");
                assert_eq!(*op, want_op, "{name}: wrong ICmp op")
            }
            other => {
                panic!("{name}: expected `icmp {want_op:?} u64` + `ret`, got: {other:?}")
            }
        }
    }
}

#[test]
fn test_native_uint_decision_call_preserves_actual_declaration_shape() {
    use trust_ir::Inst;
    for (width, scalar) in [
        (8, IRType::UInt8),
        (16, IRType::UInt16),
        (32, IRType::UInt32),
        (64, IRType::UInt64),
    ] {
        let primitive = Name::from_string(&format!("UInt{width}.decLt"));
        let declaration = |params: Vec<IRType>| IRDecl {
            name: primitive.clone(),
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, ty)| (VarId(i as u32), ty))
                .collect(),
            return_type: IRType::Bool,
            body: IRBody::VDecl {
                var: VarId(3),
                ty: IRType::Bool,
                value: IRExpr::Lit(IRLiteral::Bool(false)),
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
            },
        };
        let caller = |operand: IRType| IRDecl {
            name: Name::from_string("decision_shape_caller"),
            params: vec![(VarId(0), operand.clone()), (VarId(1), operand)],
            return_type: IRType::Bool,
            body: IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Bool,
                value: IRExpr::Apply {
                    fn_id: FnId(primitive.clone()),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            },
        };
        let error = emit_trust_ir(&[declaration(vec![scalar.clone(); 3]), caller(scalar.clone())])
            .expect_err("a comparison name cannot erase a real under-application");
        assert!(
            format!("{error:?}").contains("under-applies"),
            "{width}: {error:?}"
        );

        // A known near-miss is still an ordinary declaration. Matching its
        // actual parameters must retain its call and body, not guess an ICmp.
        let other = if width == 8 {
            IRType::UInt16
        } else {
            IRType::UInt8
        };
        let module = emit_trust_ir(&[declaration(vec![other.clone(); 2]), caller(other)])
            .expect("the existing ordinary call path remains available");
        assert!(validate_module(&module).is_empty());
        let body = module
            .functions
            .iter()
            .find(|f| f.name == "decision_shape_caller")
            .unwrap();
        assert!(body
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { .. })));
        assert!(!body
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::ICmp { .. })));
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
        Some(ICmpOp::Eq),
        "fixed-width32 uses its actual carrier"
    );
    assert_eq!(
        fire("UInt32.decEq", vec![UInt64, UInt64], Bool),
        None,
        "raw carrier width must match primitive"
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
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
}

#[test]
fn test_emit_trust_ir_binary_round_trips() {
    let decls = arith_decls();
    let module = emit_trust_ir(&decls).expect("lowering should succeed");

    // Binary serialize -> deserialize -> structural equality.
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
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
    let errors = validate_module(&module);
    assert!(
        errors.is_empty(),
        "join-point lowering must terminate every block; validate_module said: {errors:?}"
    );
}

#[test]
fn test_emit_trust_ir_join_point_round_trips() {
    let module = emit_trust_ir(&[join_point_decl()]).expect("lowering should succeed");
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
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
    let errors = validate_module(&module);
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
    let module = emit_trust_ir_with_config(&[decl], &config)
        .expect("managed-runtime program should lower in ExternCalls mode");

    // Valid trust-ir: variadic clean_alloc_ctor + fixed-arity clean_inc /
    // clean_ctor_get calls all type/arity-check against their declared imports.
    let errors = validate_module(&module);
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
                fn_id: FnId(Name::from_string(callee)),
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
    let module = emit_trust_ir_with_config(&[root], &c1_config())
        .expect("dropped-callee call site must lower via the extern boundary");

    let errors = validate_module(&module);
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
    let module = emit_trust_ir_with_config(&[root], &c1_config())
        .expect("erased-arg dropped-callee call site must lower");
    assert!(validate_module(&module).is_empty());

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
    let module = emit_trust_ir_with_config(&[helper, root], &c1_config())
        .expect("in-slice callee must lower as a plain call");
    assert!(validate_module(&module).is_empty());

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
                fn_id: FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let err = emit_trust_ir_with_config(&[scalar_result], &c1_config())
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
                fn_id: FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let err = emit_trust_ir_with_config(&[scalar_arg], &c1_config())
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
                fn_id: FnId(Name::from_string("Foo.bar")),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("Foo.bar")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let module = emit_trust_ir_with_config(&[root], &c1_config())
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
                fn_id: FnId(Name::from_string("Foo.bar")),
                arity: 3,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                // 2-arg CALL site: under the certified full arity of 3.
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("Foo.bar")),
                    args: vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(1))],
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(2)))),
            }),
        },
    };
    let err = emit_trust_ir_with_config(&[root], &c1_config())
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
    let module = emit_trust_ir_with_config(&[root], &c1_config()).expect("module should emit");
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

/// Codegen license (trust-ir binary v41): the bare emitter — which has no
/// source of truth to certify against — stamps EVERY body it emits with the
/// affirmative `Ungated` claim (never the grandfathered `None`), leaves every
/// bodyless declaration unclaimed, and puts a Clean declaration's readable
/// name in `display_path` exactly when `Function::name` is a mangled link
/// symbol. Both runtime-lowering modes.
#[test]
fn test_codegen_license_claims_every_body_and_no_declaration() {
    use trust_ir::BodyGate;
    // ExternCalls: user fn (body) + runtime imports (bodyless C symbols) + a
    // dropped-callee extern (bodyless, C-mangled `l_Nat_add`).
    let root = c1_root_decl("Nat.add", vec![IRArg::Var(VarId(0)), IRArg::Var(VarId(0))]);
    let module = emit_trust_ir_with_config(&[root], &c1_config()).expect("module should emit");
    let (mut bodies, mut declarations) = (0, 0);
    for f in &module.functions {
        if f.is_declaration() {
            declarations += 1;
            assert_eq!(
                f.body_gate, None,
                "declaration `{}` is not a codegen subject and must make no licensing claim",
                f.name
            );
        } else {
            bodies += 1;
            assert_eq!(
                f.body_gate,
                Some(BodyGate::Ungated),
                "uncertified body `{}` must be affirmatively ungated",
                f.name
            );
        }
    }
    assert_eq!(bodies, 1, "exactly the user decl has a body");
    assert!(declarations > 1, "runtime ABI imports + the dropped callee");
    let by_name = |n: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == n)
            .unwrap_or_else(|| panic!("no function `{n}`"))
    };
    // The dropped callee's symbol is the C-mangled link name; the Clean
    // declaration it stands for is readable through `display_path`.
    assert_eq!(
        by_name("l_Nat_add").display_path.as_deref(),
        Some("Nat.add")
    );
    // The user decl's symbol IS its Lean name, and a runtime ABI import is a
    // C symbol with no Clean declaration behind it: no display path either way.
    assert_eq!(by_name("root").display_path, None);
    assert_eq!(by_name("clean_alloc_ctor").display_path, None);
    // Every claim above is a v41 wire fact: the module still validates and
    // the binary codec round-trips it without laundering a state.
    assert!(validate_module(&module).is_empty());
    let decoded = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture"),
    )
    .expect("v41 blob decodes");
    assert_eq!(decoded, module);

    // Dialect mode too (the license is producer-, not mode-, scoped).
    let module = emit_trust_ir(&arith_decls()).expect("dialect module should emit");
    for f in &module.functions {
        assert!(!f.is_declaration());
        assert_eq!(f.body_gate, Some(BodyGate::Ungated), "`{}`", f.name);
        assert_eq!(
            f.display_path, None,
            "`{}` is an ordinary Lean name",
            f.name
        );
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
        ctor: CtorInfo {
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
fn c2_run_bool(module: &Module, name: &str, args: &[bool]) -> bool {
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
fn c2_calls_to(module: &Module, func: &trust_ir::Function, sym: &str) -> usize {
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
        let module = emit_trust_ir_with_config(&[c2_bool_not_decl()], &config)
            .unwrap_or_else(|e| panic!("bool case must lower in {mode:?}: {e}"));
        assert!(validate_module(&module).is_empty());
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
    let module = emit_trust_ir_with_config(
        &[c2_bool_not_decl(), c2_bool_and_decl(), c2_bool_xor_decl()],
        &c2_config(),
    )
    .expect("bool truth-table module must lower");
    assert!(validate_module(&module).is_empty());

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
    let module = emit_trust_ir_with_config(&[decl], &c2_config()).expect("scalar case must lower");
    assert!(validate_module(&module).is_empty());
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
            .execute_function(f, [InterpretValue::int(Ty::U64, input as i128).unwrap()])
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
    let module =
        emit_trust_ir_with_config(&[decl], &c2_config()).expect("scalar-carrier sproj must lower");
    assert!(validate_module(&module).is_empty());
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
        .execute_function(f, [InterpretValue::int(Ty::U32, 65).unwrap()])
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
    let module = emit_trust_ir_with_config(
        &[
            proj_decl("to_bitvec", IRType::UInt8),
            proj_decl("decidable_proof", IRType::Bool),
        ],
        &c2_config(),
    )
    .expect("scalar-carrier object proj must lower");
    assert!(validate_module(&module).is_empty());

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
    let err = emit_trust_ir_with_config(&[decl], &c2_config())
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
                fn_id: FnId(Name::from_string("And.right")),
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
        let module = emit_trust_ir_with_config(&[callee.clone(), root.clone()], &config)
            .unwrap_or_else(|e| panic!("erased-arg in-slice call must lower in {mode:?}: {e}"));
        assert!(validate_module(&module).is_empty());

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
                fn_id: FnId(Name::from_string("Functor.map")),
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

    let module = emit_trust_ir_with_config(&[callee.clone(), root.clone()], &c2_config())
        .expect("over-applied in-slice call must lower via clean_apply");
    assert!(validate_module(&module).is_empty());

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
    let err = emit_trust_ir_with_config(
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
    let err = emit_trust_ir_with_config(&[callee, root], &c2_config())
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
    let module =
        emit_trust_ir_with_config(&[decl], &c2_config()).expect("Box{Bool} must lower validly");
    assert!(validate_module(&module).is_empty());
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found (set CLEAN_TRUST_CG_BIN)");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
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
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("bool_case.tmbc");
    let bin = dir.path().join("bool_case");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    let out = legacy_trust_cg(&trust_cg)
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
fn extern_build_module() -> Module {
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
    emit_trust_ir_with_config(&[decl], &config).expect("ExternCalls build module should lower")
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
    let module = emit_trust_ir_with_config(&[add2, make, apply_it], &config)
        .expect("closures should lower in ExternCalls mode (no longer Unsupported)");

    // The fn-pointer (fn_addr -> bitcast to Ptr) and clean_alloc_closure /
    // clean_apply_1 calls all type/arity-check against their imports.
    let errors = validate_module(&module);
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
    let module = emit_trust_ir_with_config(&[wide_closure_apply_decl(32)], &config)
        .expect("arity 32 must lower at the exact clean_invoke ceiling");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "closure validation errors: {errors:?}");
    assert!(
        module
            .functions
            .iter()
            .any(|function| function.name == "clean_apply_32"),
        "arity 32 must route to the positional runtime ABI"
    );

    let error = emit_trust_ir_with_config(&[wide_closure_apply_decl(33)], &config)
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    assert!(
        std::path::Path::new(rt_src).is_file(),
        "clean_runtime.c missing at {rt_src}: it is a tracked file of this tree"
    );

    let config = TrustIrConfig {
        module_name: "closure_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&e2e_closure_main_decls(), &config)
        .expect("closure main should lower");
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("c.tmbc");
    let mobj = dir.path().join("c.o");
    let rtobj = dir.path().join("rt.o");
    let bin = dir.path().join("cprog");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    // trust-cg compiles the closure module (fn_addr -> clean_alloc_closure ->
    // clean_apply_1, which invokes `id` through the reified pointer). All runtime
    // symbols are out-of-line, so it links against the runtime with no shims.
    let cg = legacy_trust_cg(&trust_cg)
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
/// only OUT-OF-LINE runtime symbols (sized string constructor, clean_dec), so it links
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
    let module = emit_trust_ir_with_config(&e2e_string_main_decls(), &config)
        .expect("string program should lower in ExternCalls mode");
    let errors = validate_module(&module);
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
        Some(trust_ir::constant::Constant::Bytes { data, utf8: true }) => {
            assert_eq!(*data, expected, "global bytes = literal + NUL");
        }
        other => panic!("string global initializer should be str-origin Bytes: {other:?}"),
    }
    match g.ty {
        Ty::Array(_, len) => {
            assert_eq!(len, expected.len() as u64, "Array length = byte count");
        }
        ref other => panic!("string global type should be Ty::Array: {other:?}"),
    }

    // The body hands the global's address and byte length to the sized ABI.
    let mk = module
        .functions
        .iter()
        .find(|f| f.name == "clean_mk_string_from_bytes")
        .map(|f| f.id)
        .expect("sized string constructor declared in ExternCalls ABI");
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
        "main should call the sized constructor on the global address"
    );
}

/// `fn main() -> u64 { let s = <literal>; dec s; ret 7 }`: one string literal,
/// so the emitted module holds exactly one string global.
fn one_string_main_decls(literal: &str) -> Vec<IRDecl> {
    let mut decls = e2e_string_main_decls();
    let IRBody::VDecl { value, .. } = &mut decls[0].body else {
        panic!("fixture layout: main opens with the string VDecl");
    };
    *value = IRExpr::String(literal.to_string());
    decls
}

/// trust-ir v50 (§3.1): a string global whose bytes are all equal — any
/// literal made only of NULs, `"\0"` being `[0, 0]` with its terminator — is a
/// UNIFORM array, whose list spellings the validator refuses, and whose
/// `Constant::Splat` spelling lowering-target subset v4 refuses. Every string
/// literal is therefore emitted as the str-origin byte carrier, which is
/// neither: the module validates AND stays in the handoff subset, for the
/// all-NUL literals and for every other shape alike.
#[test]
fn test_emit_trust_ir_string_globals_are_canonical_for_uniform_literals() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use trust_ir::constant::Constant;
    use trust_ir_conformance::subset::module_subset_violations;

    let config = TrustIrConfig {
        module_name: "strconst".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    // Uniform with the terminator: "", "\0", "\0\0\0". Not uniform: a NUL
    // beside another byte, a single ASCII byte, a multi-byte scalar.
    for literal in ["", "\0", "\0\0\0", "a\0", "a\x007", "a", "é\0🦀"] {
        // `emit_trust_ir_with_config` already refuses an invalid or
        // out-of-subset module; Ok here is the first half of the claim.
        let module = emit_trust_ir_with_config(&one_string_main_decls(literal), &config)
            .unwrap_or_else(|e| panic!("literal {literal:?} should lower: {e}"));
        assert!(validate_module(&module).is_empty(), "{literal:?}");
        assert!(module_subset_violations(&module).is_empty(), "{literal:?}");
        let constructor = module
            .functions
            .iter()
            .find(|f| f.name == "clean_mk_string_from_bytes")
            .expect("sized ABI");
        let signature = &module.func_types[constructor.ty.index() as usize];
        assert_eq!(signature.params, vec![Ty::Ptr, Ty::U64]);
        assert_eq!(signature.returns, vec![Ty::Ptr]);
        let main = module
            .functions
            .iter()
            .find(|f| f.name == "main")
            .expect("main");
        let args = main
            .instructions()
            .find_map(|node| match &node.inst {
                trust_ir::inst::Inst::Call { callee, args } if *callee == constructor.id => {
                    Some(args)
                }
                _ => None,
            })
            .expect("literal constructor call");
        assert_eq!(args.len(), 2);
        assert!(
            main.instructions()
                .any(|node| node.results.contains(&args[1])
                    && matches!(
                        &node.inst, trust_ir::inst::Inst::Const {
                            ty: Ty::U64, value: Constant::Int(n)
                        } if *n == literal.len() as i128
                    )),
            "{literal:?}: exact UTF-8 byte length"
        );
        assert_eq!(module.globals.len(), 1, "{literal:?}: one global");
        let global = &module.globals[0];
        let mut bytes = literal.as_bytes().to_vec();
        bytes.push(0);
        assert_eq!(
            global.initializer,
            Some(Constant::Bytes {
                data: bytes.clone(),
                utf8: true,
            }),
            "{literal:?}: the literal's bytes, then NUL, as str-origin Bytes"
        );
        match global.ty {
            Ty::Array(_, len) => assert_eq!(len, bytes.len() as u64, "{literal:?}"),
            ref other => panic!("{literal:?}: string global type should be an array: {other:?}"),
        }
    }

    // Controls: the two other spellings of the all-NUL global, each refused
    // where the emitter's own gate would refuse the module.
    let module = emit_trust_ir_with_config(&one_string_main_decls("\0"), &config)
        .expect("the all-NUL literal lowers");
    let mut missing_length = module.clone();
    let constructor = missing_length
        .functions
        .iter()
        .find(|f| f.name == "clean_mk_string_from_bytes")
        .expect("sized ABI")
        .id;
    for function in &mut missing_length.functions {
        for node in function
            .blocks
            .iter_mut()
            .flat_map(|b| b.instructions_mut())
        {
            if let trust_ir::inst::Inst::Call { callee, args } = &mut node.inst {
                if *callee == constructor {
                    args.pop();
                }
            }
        }
    }
    assert!(
        !validate_module(&missing_length).is_empty(),
        "one-arg sized ABI must fail validation"
    );
    let zeros = || vec![Constant::Int(0), Constant::Int(0)];
    // (1) The list spelling the emitter used before v50: NOT canonical.
    let mut list = module.clone();
    list.globals[0].initializer = Some(Constant::Aggregate(zeros()));
    assert!(
        validate_module(&list)
            .iter()
            .any(|e| matches!(e, ValidationError::NonCanonicalUniformArray { .. })),
        "a uniform byte list must be refused as non-canonical: {:?}",
        validate_module(&list)
    );
    // (2) The canonical array spelling IS the splat, which validates but is
    // outside lowering-target subset v4 (not yet admitted with a lowering).
    let splat = Constant::array(zeros());
    assert_eq!(splat, Constant::splat(Constant::Int(0), 2));
    let mut splatted = module.clone();
    splatted.globals[0].initializer = Some(splat);
    assert!(validate_module(&splatted).is_empty());
    assert!(
        module_subset_violations(&splatted)
            .iter()
            .any(|v| v.contains("Constant::Splat")),
        "a splat global initializer is outside the handoff subset"
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    assert!(
        std::path::Path::new(rt_src).is_file(),
        "clean_runtime.c missing at {rt_src}: it is a tracked file of this tree"
    );

    let config = TrustIrConfig {
        module_name: "string_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&e2e_string_main_decls(), &config)
        .expect("string main should lower");
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("s.tmbc");
    let mobj = dir.path().join("s.o");
    let rtobj = dir.path().join("rt.o");
    let bin = dir.path().join("sprog");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    let cg = legacy_trust_cg(&trust_cg)
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

    // The sized constructor copies the read-only byte global, then
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
extern void clean_inc_n(clean_obj*, size_t);
extern bool clean_is_exclusive(clean_obj*);
extern clean_obj* clean_box(size_t);
extern size_t clean_unbox(clean_obj*);
extern uint64_t clean_unbox_uint64(clean_obj*);
extern uint32_t clean_unbox_uint32(clean_obj*);
extern double clean_unbox_float(clean_obj*);
extern unsigned clean_obj_tag(clean_obj*);
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    assert!(
        std::path::Path::new(rt_src).is_file(),
        "clean_runtime.c missing at {rt_src}: it is a tracked file of this tree"
    );

    let config = TrustIrConfig {
        module_name: "inline_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&e2e_inline_managed_decls(), &config)
        .expect("inline managed program should lower");
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("m.tmbc");
    let mobj = dir.path().join("m.o");
    let rtobj = dir.path().join("rt.o");
    let shim_c = dir.path().join("shims.c");
    let shimobj = dir.path().join("shims.o");
    let bin = dir.path().join("prog");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);
    std::fs::write(&shim_c, CLEAN_RUNTIME_SHIMS_C).expect("write shims.c");

    let run_cc = |args: &[&OsStr]| -> std::process::Output {
        std::process::Command::new("cc")
            .args(args)
            .output()
            .expect("spawn cc")
    };
    use std::ffi::OsStr;

    let cg = legacy_trust_cg(&trust_cg)
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    assert!(
        std::path::Path::new(rt_src).is_file(),
        "clean_runtime.c missing at {rt_src}: it is a tracked file of this tree"
    );

    // Lower the managed program in ExternCalls mode and validate.
    let config = TrustIrConfig {
        module_name: "managed_main".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = emit_trust_ir_with_config(&e2e_managed_main_decls(), &config)
        .expect("managed main should lower");
    assert!(
        validate_module(&module).is_empty(),
        "validate errors: {:?}",
        validate_module(&module)
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("m.tmbc");
    let mobj = dir.path().join("m.o");
    let rtobj = dir.path().join("clean_runtime.o");
    let bin = dir.path().join("prog");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    // trust-cg: managed trust-ir -> object (undefined runtime externals).
    let out = legacy_trust_cg(&trust_cg)
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };

    let module = extern_build_module();
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("build.tmbc");
    let obj = dir.path().join("build.o");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    // Compile to an OBJECT only (`-c`): no link, so the unresolved Clean-runtime
    // symbols stay as undefined externals (resolved when linked against the
    // Clean runtime). This proves trust-cg lowers the managed-runtime trust-ir,
    // including the variadic `clean_alloc_ctor` call, to real machine code.
    let out = legacy_trust_cg(&trust_cg)
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
    let nm = std::process::Command::new("nm")
        .arg(&obj)
        .output()
        .expect("spawn nm to inspect the trust-cg object");
    let syms = String::from_utf8_lossy(&nm.stdout);
    assert!(
        syms.contains("clean_alloc_ctor"),
        "object does not reference clean_alloc_ctor:\n{syms}"
    );
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
                fn_id: FnId(Name::from_string("forty_two")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    vec![forty_two, main]
}

/// Wrap a serialized trust-ir module in the `.tmbc` envelope trust-cg reads:
/// `b"tMBC" ++ 1u32_le ++ serialize_module(module)`.
fn tmbc_envelope(module: &Module) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"tMBC");
    bytes.extend_from_slice(&1u32.to_le_bytes());
    bytes.extend_from_slice(
        &trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    );
    bytes
}

/// Check the real producer's license refusal, then retain the native lowering
/// oracle through a clone licensed at the `clean-compiler-unvalidated` grade.
/// These tests start with handwritten L5IR, without the original kernel
/// expressions needed for translation validation, so they cannot mint a
/// verified codegen license. Production emission stays `Ungated`; the clone is
/// re-stamped by the production lane's own
/// [`crate::emit_trust_ir_lane::restamp_ungated_as_unvalidated`], which claims
/// nothing about a body, and compiled with that authority recognized for the
/// one invocation ([`legacy_trust_cg`]). No certificate is fabricated and no
/// body is left claim-less: the old fixture cleared the clone to `None`, which
/// trust-cg refuses since WS7.5 and, from bd0837748, refuses as a producer
/// omission in a v41 blob.
fn write_legacy_native_fixture(
    module: &Module,
    trust_cg: &std::path::Path,
    target: &str,
    destination: &std::path::Path,
) {
    let ungated = destination.with_extension("ungated.tmbc");
    let refused_object = destination.with_extension("refused.o");
    std::fs::write(&ungated, tmbc_envelope(module)).expect("write ungated producer output");
    let refusal = std::process::Command::new(trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&refused_object)
        .arg(&ungated)
        .output()
        .expect("check native producer license refusal");
    assert!(
        !refusal.status.success()
            && String::from_utf8_lossy(&refusal.stderr).contains("affirmatively ungated")
            && !refused_object.exists(),
        "ungated producer output must refuse before object emission: {}",
        String::from_utf8_lossy(&refusal.stderr)
    );

    let mut legacy = module.clone();
    let census = crate::emit_trust_ir_lane::restamp_ungated_as_unvalidated(&mut legacy)
        .expect("every body of the producer's module carries the Ungated claim");
    assert!(
        census.kept.is_empty(),
        "the native fixture carries only Ungated bodies: {census:?}"
    );
    assert!(
        census.unvalidated > 0,
        "native fixture must exercise at least one body"
    );
    std::fs::write(destination, tmbc_envelope(&legacy)).expect("write unvalidated fixture");
}

/// trust-cg over a fixture [`write_legacy_native_fixture`] licensed (or a
/// hand-built copy licensed the same way): the `clean-compiler-unvalidated`
/// authority is recognized for this one invocation, exactly as the production
/// `clean run --backend trust-cg` lane passes it. An `ungated` body and any
/// other unrecognized authority stay refused, which is why the refusal half of
/// [`write_legacy_native_fixture`] runs without it.
fn legacy_trust_cg(trust_cg: &std::path::Path) -> std::process::Command {
    let mut command = std::process::Command::new(trust_cg);
    command.args([
        "--recognize-authority",
        crate::emit_trust_ir_lane::CLEAN_COMPILER_UNVALIDATED_AUTHORITY,
    ]);
    command
}

/// Locate the trust-cg binary, or `None` to skip (tool not available).
///
/// An explicitly SELECTED binary (`CLEAN_TRUST_CG_BIN`) is authoritative: if
/// it does not name a file, this PANICS rather than falling through to the
/// sibling build or `PATH`. Measured 2026-09-18 (WS6.0 review): the
/// `trust-ir-backend-lib` gate leg forwards `TRUSTCG_BIN` as
/// `CLEAN_TRUST_CG_BIN`, and a RELATIVE path valid from the repo root is not
/// a file from the test binary's cwd (the package root), so the old
/// fall-through silently ran the nine native e2e tests against whatever
/// trust-cg was on `PATH` while the leg reported the selected one.
fn find_trust_cg() -> Option<std::path::PathBuf> {
    resolve_trust_cg(
        std::env::var_os("CLEAN_TRUST_CG_BIN"),
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")),
        std::env::var_os("PATH"),
    )
    .unwrap_or_else(|refusal| panic!("{refusal}"))
}

/// The pure half of [`find_trust_cg`]: `Err` when an explicit selection does
/// not name a file (never a silent fall-through), `Ok(None)` when nothing is
/// selected and nothing is found (the e2e tests then skip, loudly).
fn resolve_trust_cg(
    selected: Option<std::ffi::OsString>,
    manifest_dir: &std::path::Path,
    path_var: Option<std::ffi::OsString>,
) -> Result<Option<std::path::PathBuf>, String> {
    if let Some(p) = selected {
        let pb = std::path::PathBuf::from(&p);
        if pb.is_file() {
            return Ok(Some(pb));
        }
        return Err(format!(
            "CLEAN_TRUST_CG_BIN={} does not name a file from cwd {}: an explicitly selected \
             trust-cg is authoritative and never falls through to a sibling build or PATH \
             (pass an absolute path)",
            pb.display(),
            std::env::current_dir()
                .map(|d| d.display().to_string())
                .unwrap_or_else(|_| "<unknown>".into())
        ));
    }
    let sibling = manifest_dir.join("../../../trust-cg");
    for profile in ["debug", "release"] {
        let pb = sibling.join("target").join(profile).join("trust-cg");
        if pb.is_file() {
            return Ok(Some(pb));
        }
    }
    Ok(path_var.and_then(|path| {
        std::env::split_paths(&path)
            .map(|dir| dir.join("trust-cg"))
            .find(|candidate| candidate.is_file())
    }))
}

/// WS6.0 review, adversarial input: a selected trust-cg that is not a file
/// from the test's cwd (a relative path, a typo) is REFUSED by name, never
/// silently replaced by another trust-cg found on `PATH`.
#[test]
fn test_find_trust_cg_selected_path_is_authoritative_never_falls_through() {
    let dir = tempfile::tempdir().expect("tempdir");
    let decoy = dir.path().join("trust-cg");
    std::fs::write(&decoy, b"#!/bin/sh\n").expect("write decoy trust-cg");
    let path_var = Some(dir.path().as_os_str().to_owned());
    let manifest = dir.path().join("no/such/manifest");

    // Negative twin: a relative selection that does not resolve from cwd,
    // with a decoy on PATH -- refused, naming the variable.
    let refusal = resolve_trust_cg(
        Some("target/release/definitely-not-trust-cg".into()),
        &manifest,
        path_var.clone(),
    )
    .expect_err("a selected path that is not a file must not fall through to PATH");
    assert!(refusal.contains("CLEAN_TRUST_CG_BIN="), "{refusal}");
    assert!(refusal.contains("never falls through"), "{refusal}");

    // Positive: a selection that IS a file wins over the PATH decoy.
    let chosen = dir.path().join("chosen-trust-cg");
    std::fs::write(&chosen, b"#!/bin/sh\n").expect("write chosen trust-cg");
    assert_eq!(
        resolve_trust_cg(
            Some(chosen.clone().into_os_string()),
            &manifest,
            path_var.clone()
        ),
        Ok(Some(chosen))
    );

    // Unselected: PATH discovery is unchanged (the dev-convenience lane).
    assert_eq!(resolve_trust_cg(None, &manifest, path_var), Ok(Some(decoy)));
    assert_eq!(resolve_trust_cg(None, &manifest, None), Ok(None));
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
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
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };

    // 1. Lower + validate.
    let module = emit_trust_ir(&e2e_main_decls()).expect("e2e decls should lower");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module errors: {errors:?}");

    // 2. Write the .tmbc envelope.
    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("e2e.tmbc");
    let bin = dir.path().join("e2e");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    // 3. Compile + link via trust-cg (which invokes cc).
    let out = legacy_trust_cg(&trust_cg)
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native e2e (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };

    let module = emit_trust_ir(&e2e_join_point_decls()).expect("join-point main should lower");
    assert!(validate_module(&module).is_empty());

    let dir = tempfile::tempdir().expect("tempdir");
    let tmbc = dir.path().join("jp.tmbc");
    let bin = dir.path().join("jp");
    write_legacy_native_fixture(&module, &trust_cg, target, &tmbc);

    let out = legacy_trust_cg(&trust_cg)
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
) -> CtorInfo {
    CtorInfo {
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
    let module = emit_trust_ir_with_config(decls, &config)
        .expect("differential program should lower to trust-ir");
    assert!(
        validate_module(&module).is_empty(),
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
    write_legacy_native_fixture(&module, trust_cg, target, &tmbc);
    std::fs::write(
        &wrap_c,
        "#include <stdint.h>\nextern uint64_t clean_entry(void);\n\
         int main(void) { return (int)(clean_entry() & 0xFFu); }\n",
    )
    .expect("write trust-ir wrapper");
    std::fs::write(&shim_c, CLEAN_RUNTIME_SHIMS_C).expect("write shim");

    let cg = legacy_trust_cg(trust_cg)
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
            // SELF-SKIP OK: trust-cg targets only aarch64/x86_64; other host arches cannot run this native differential (skip is printed).
            return;
        }
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            eprintln!("differential e2e skipped: trust-cg binary not found");
            // SELF-SKIP OK: trust-cg is an external binary outside this tree; skipped (printed) only when none is selected or found.
            return;
        }
    };
    let rt_src = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../clean-runtime/src/clean_runtime.c"
    );
    let rt_inc = concat!(env!("CARGO_MANIFEST_DIR"), "/../clean-runtime/include");
    assert!(
        std::path::Path::new(rt_src).is_file(),
        "clean_runtime.c missing at {rt_src}: it is a tracked file of this tree"
    );

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
        let module = emit_trust_ir_with_config(&decls, &cfg)
            .unwrap_or_else(|e| panic!("`{label}` should lower: {e:?}"));
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "`{label}` should validate: {errors:?}");
        // The expected runtime symbol must be declared and called.
        let called: HashSet<&str> = module
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
// ExternCalls is dialect-free by contract (trust-ir lowering-target subset v3
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
/// Dialect mode and a `u32` `clean_obj_tag` call in ExternCalls mode.
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

/// The ExternCalls tag read is 32 bits end to end: `clean_obj_tag` is imported
/// as `ptr -> u32`, the width the runtime returns a boxed tag at
/// (`runtime_extern.c`), and `Tag` lowers to that call alone. An 8-bit import
/// plus a `zext` read boxed tag 299 as 43, so a `case` on an enum of 256 or
/// more constructors took the wrong branch.
#[test]
fn test_emit_trust_ir_extern_obj_tag_is_a_u32_read() {
    use trust_ir::inst::Inst;
    let config = TrustIrConfig {
        module_name: "tag_u32".to_string(),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module =
        emit_trust_ir_with_config(&tag_decls(), &config).expect("the tag program must lower");
    assert!(validate_module(&module).is_empty());
    let import = module
        .functions
        .iter()
        .find(|f| f.name == "clean_obj_tag")
        .expect("ExternCalls must declare clean_obj_tag");
    let sig = module
        .func_type(import.ty)
        .expect("extern signature interned");
    assert_eq!(sig.params, vec![Ty::Ptr]);
    assert_eq!(
        sig.returns,
        vec![Ty::U32],
        "clean_obj_tag must return the whole 32-bit tag"
    );
    let f = module
        .functions
        .iter()
        .find(|f| f.name == "tag_of")
        .expect("tag_of must be emitted");
    assert_eq!(c2_calls_to(&module, f, "clean_obj_tag"), 1);
    assert!(
        f.instructions()
            .all(|n| !matches!(n.inst, Inst::Cast { .. })),
        "the tag read needs no widening cast"
    );
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
                errors
                    .iter()
                    .any(|e| matches!(e, ValidationError::TargetInfoRequired { .. })),
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
                fn_id: FnId(Name::from_string("gives_u64")),
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
                errors
                    .iter()
                    .any(|e| matches!(e, ValidationError::ReturnTypeMismatch { .. })),
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
            assert_eq!(version, 6, "checked against the re-audited subset v6");
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
// `lowering-target-subset.md` v6, `trust_ir_conformance::subset`).
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
fn test_trust_ir_lowering_subset_version_is_the_audited_v6() {
    // Audit trail: the 2026-07-04 promotion audit ratified subset v1
    // (`clean.*` ops refused admission; ExternCalls self-gates on the
    // versioned subset). 2026-07-21 re-audit: trust-ir bumped to v2
    // (ae2ded7, "certify fat pointers") — a strictly ADDITIVE expansion
    // (fat-pointer certification joins the allowlists; nothing was removed),
    // so Clean's v1-conformant ExternCalls emissions conform to v2 unchanged
    // (the corpus gate below stays green) and `clean.*` dialect ops remain
    // excluded. 2026-09-22 re-audit: trust-ir bumped to v3 (af7a5b3a, WS2.9)
    // — a breaking SHRINK that moves no allowlist name: `Dealloc` refused by
    // name, `Transmute` integer/pointer-only on both sides, and structural
    // condition 5 (the module targets the pinned 64-bit little-endian byte
    // model). Clean's producer is outside all three: it lowers `dec` to
    // `Release`, never `Dealloc` (trust-ir's own v3 producer census says so);
    // no `emit_trust_ir*.rs` source constructs `CastOp::Transmute`; and
    // `host_target_info` pins `size_of::<usize>()` and the host endianness,
    // 8-byte little-endian on every supported host. The ExternCalls corpus
    // gate below re-measures that. 2026-09-24 re-audit at R29744d5f: v4 adds
    // ONLY Isize/Usize/Char to the type allowlist, with no Inst/CastOp name
    // changes. New condition 6 restricts Char origins (including loads of
    // Char-containing aggregates resolved through module member tables).
    // Clean still emits USize as U64 and UInt32 as U32, not native B1 types.
    // The corpus below inventories ALL stored and resolved result types,
    // including nested/member-table occurrences, to pin that boundary; it
    // does not claim Clean implements the newly admitted Char semantics.
    // 2026-10-28 re-audit at the pinned 73c5a310: v5 expands only target
    // selection to canonical wasm32/4-byte little-endian. The v5 construct
    // allowlists alias v4's (the dialect/proof lists still alias v3), and
    // the default64 behavior is unchanged. Clean's existing host-target
    // guard pins 8-byte pointers; the corpus below retains its no-native-B1
    // inventory and exact subset/dialect-free checks. This audit does not
    // claim Clean emits the newly admitted wasm32 model.
    // Forward E197 re-audit: v6 adds nominal FnItem types/constants and
    // authenticates their module-owned target. Inst/CastOp/dialect/proof
    // allowlists alias v5, target rules are unchanged, and BoxDeref remains
    // excluded. This producer emits no FnItem; the shared-type inventory
    // below pins that absence even in unused/nested tables and resolved
    // results. Existing Func carriers are not relabelled as nominal items.
    // The exact three clean.* dialect violations remain refusals. A future
    // bump invalidates THIS
    // audit — the pin makes it loud so the producer audit is re-run.
    assert_eq!(
        SUBSET_VERSION, 6,
        "trust-ir bumped its lowering-target subset version: re-run the Clean \
         producer audit (docs/lowering-target-subset.md Producer notes) and \
         update this suite's known-violation expectations"
    );
}

/// The shared visitor covers every type table (even unused entries), named
/// aggregate members, signatures, captures, globals, parameters, instruction
/// types and inline children. Also inspect resolved SSA result types: calls
/// and similar instructions obtain theirs indirectly from module tables.
fn unemitted_subset_type_occurrences(module: &Module) -> Vec<String> {
    let mut found = Vec::new();
    let mut record = |ty: &Ty| {
        if matches!(ty, Ty::Char | Ty::Isize | Ty::Usize | Ty::FnItem(_)) {
            found.push(format!("{ty:?}"));
        }
    };
    module.visit_types(&mut record);
    for node in module.functions.iter().flat_map(|f| f.instructions()) {
        for ty in node.result_tys(module) {
            ty.visit_types(&mut record);
        }
    }
    found
}

#[test]
fn test_emit_trust_ir_subset_audit_sees_nested_tables_and_result_types() {
    use trust_ir::Inst;

    let base = emit_trust_ir(&arith_decls()).expect("real producer baseline");
    assert!(unemitted_subset_type_occurrences(&base).is_empty());

    // Diagnostic mutations exercise the inventory, not executable authority.
    let mut table = base.clone();
    table
        .types
        .push(Ty::Tuple(vec![Ty::PtrConst(Box::new(Ty::Char))]));
    assert_eq!(unemitted_subset_type_occurrences(&table), ["Char"]);

    let mut member = base.clone();
    member.structs.push(trust_ir::ty::StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "audit_only_unused_member".into(),
        fields: vec![trust_ir::ty::FieldDef {
            name: "nested".into(),
            ty: Ty::Tuple(vec![Ty::Char]),
            offset: None,
        }],
        size: None,
        align: None,
        repr: trust_ir::ty::StructRepr::Rust,
        origin: None,
    });
    assert_eq!(unemitted_subset_type_occurrences(&member), ["Char"]);

    let mut signature = base.clone();
    signature.func_types[0].returns = vec![Ty::Usize];
    assert!(unemitted_subset_type_occurrences(&signature).contains(&"Usize".into()));

    // v6's new nominal type must also invalidate the unchanged-producer
    // audit when buried in an otherwise unused aggregate type table.
    let mut item = base.clone();
    item.types
        .push(Ty::Tuple(vec![Ty::FnItem(item.functions[0].id)]));
    let item_types = unemitted_subset_type_occurrences(&item);
    assert_eq!(item_types.len(), 1);
    assert!(item_types[0].starts_with("FnItem("));

    let mut instruction = base.clone();
    let node = instruction.functions[1].blocks[0]
        .body
        .iter_mut()
        .find(|node| matches!(node.inst, Inst::Const { .. }))
        .expect("the producer emits an integer constant");
    if let Inst::Const { ty, .. } = &mut node.inst {
        *ty = Ty::Tuple(vec![Ty::Isize]);
    }
    assert_eq!(
        unemitted_subset_type_occurrences(&instruction),
        ["Isize", "Isize"]
    );
    assert!(unemitted_subset_type_occurrences(&base).is_empty());
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
    let corpus = extern_calls_corpus();
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
            unemitted_subset_type_occurrences(&module).is_empty(),
            "`{label}` newly emits a B1 scalar or FnItem; re-audit origins, targets and nominal identity"
        );
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

/// The hand-built `ExternCalls` corpus: every e2e program shape the object
/// path is exercised on. Shared by the lowering-target subset gate above and
/// the WS6.14 `FnDef`-typing census below.
fn extern_calls_corpus() -> Vec<(&'static str, Vec<IRDecl>)> {
    vec![
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
    ]
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
    // The strings deliberately pin trust-ir's v6 message format; they break
    // loudly (together with the SUBSET_VERSION pin) on any subset revision.
    let expected = vec![
        "fn `dialect_probe` bb0 inst #0: dialect op `clean.obj.set_tag` is outside \
         lowering-target subset v6 (no proven lowering)"
            .to_string(),
        "fn `dialect_probe` bb0 inst #1: dialect op `clean.str.const` is outside \
         lowering-target subset v6 (no proven lowering)"
            .to_string(),
        "fn `dialect_probe` bb0 inst #2: dialect op `clean.obj.tag` is outside \
         lowering-target subset v6 (no proven lowering)"
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
fn assert_span_provenance(module: &Module, expected_file: &str) {
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
    let errors = validate_module(&module);
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
    let errors = validate_module(&module);
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
    let errors = validate_module(&module);
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
                fn_id: FnId(Name::from_string("Missing.le")),
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let module = emit_trust_ir_with_config(&[root1, root2], &c4_config())
        .expect("value ref + agreeing call site must share one extern fallback");
    let errors = validate_module(&module);
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
                fn_id: FnId(Name::from_string("Missing.mpr")),
                arity: 2,
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let module = emit_trust_ir_with_config(&[decl], &c4_config())
        .expect("PartialApply of a dropped callee must close over the fallback");
    let errors = validate_module(&module);
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
                fn_id: FnId(Name::from_string("Foo.bar")),
                arity: 3,
                args: vec![],
            },
            rest: Box::new(IRBody::VDecl {
                var: VarId(2),
                ty: IRType::Object,
                value: IRExpr::Apply {
                    fn_id: FnId(Name::from_string("Foo.bar")),
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
                fn_id: FnId(Name::from_string("mapish")),
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
            validate_module(&module).is_empty(),
            "Dialect validation errors for {ret_ty:?} return",
        );

        // ExternCalls (managed-runtime handoff) mode.
        let config = TrustIrConfig {
            runtime_lowering: RuntimeLowering::ExternCalls,
            ..TrustIrConfig::default()
        };
        let module = emit_trust_ir_with_config(&[unit_shape(ret_ty.clone())], &config)
            .unwrap_or_else(|e| panic!("ExternCalls emit for {ret_ty:?} return failed: {e}"));
        assert!(
            validate_module(&module).is_empty(),
            "ExternCalls validation errors for {ret_ty:?} return",
        );
    }
}

/// DRIFT GUARD: `to_ir::code::uint_arith_scalar_ty` (Seam A's name table,
/// consulted in feature-less builds) and this emitter's `uint_arith_binop`
/// (the single native-BinOp realizer and skip set) agree on direct operations
/// and widths. Shifts have scalar typing but require the carrier emitter's
/// modulo-width reduction, so the single-BinOp table must still decline them.
#[test]
fn test_uint_arith_tables_agree() {
    use trust_ir::ty::Ty;
    let widths: &[(&str, IRType, Ty)] = &[
        ("UInt8", IRType::UInt8, Ty::U8),
        ("UInt16", IRType::UInt16, Ty::U16),
        ("UInt32", IRType::UInt32, Ty::U32),
        ("UInt64", IRType::UInt64, Ty::U64),
    ];
    for (prefix, ir_ty, ty) in widths {
        for op in ["add", "sub", "mul", "land", "lor", "xor"] {
            let n = Name::from_string(&format!("{prefix}.{op}"));
            assert_eq!(
                crate::to_ir::code::uint_arith_scalar_ty(&n),
                Some(ir_ty.clone()),
                "{n:?} must be in the to_ir table"
            );
            let (_, got_ty) = uint_arith_binop(&n.to_string())
                .unwrap_or_else(|| panic!("{n:?} must be in the emitter table"));
            assert_eq!(got_ty, *ty, "{n:?} widths must agree");
        }
        // The tables must also DECLINE together: div/mod are deliberately not
        // native (Lean div-by-zero = 0 differs from machine semantics), and
        // complement needs an environment-aware lowering.
        for op in ["div", "mod", "complement"] {
            let n = Name::from_string(&format!("{prefix}.{op}"));
            assert!(crate::to_ir::code::uint_arith_scalar_ty(&n).is_none());
            assert!(uint_arith_binop(&n.to_string()).is_none());
        }
        for (op, expected) in [
            ("shiftLeft", crate::carrier_prims::ScalarBin::Shl),
            ("shiftRight", crate::carrier_prims::ScalarBin::LShr),
        ] {
            let n = Name::from_string(&format!("{prefix}.{op}"));
            assert_eq!(
                crate::to_ir::code::uint_arith_scalar_ty(&n),
                Some(ir_ty.clone())
            );
            assert!(uint_arith_binop(&n.to_string()).is_none());
            let Some(crate::carrier_prims::CarrierPrim::Bin(got, width)) =
                crate::carrier_prims::carrier_prim(&n, false)
            else {
                panic!("{n:?} must use the guarded carrier emitter");
            };
            assert_eq!(got, expected);
            assert_eq!(width.ir_type(), *ir_ty);
        }
    }
    let outside = Name::from_string("USize.add");
    assert!(crate::to_ir::code::uint_arith_scalar_ty(&outside).is_none());
    assert!(uint_arith_binop("USize.add").is_none());
}

// ---------------------------------------------------------------------------
// GAP G15 (end-to-end): a `theorem` must produce NO emitted trust-ir Function
// ---------------------------------------------------------------------------

/// GAP G15, at the FORMAT boundary — the assertion that actually matters.
///
/// The unit-level gate lives in `to_lcnf::tests`
/// (`test_theorem_never_lowers_to_a_decl`); this one carries it all the way to
/// the artifact. A kernel `theorem` and a kernel `def` are pushed through the
/// REAL frontend (`constant_to_decl`) into the REAL pipeline
/// (`compile_lcnf_to_trust_ir`), and the emitted `trust_ir::Module` must
/// contain the definition and NOTHING for the theorem.
///
/// Before the `ConstantKind::Theorem` gate, a theorem's proof term reached the
/// Prop-valued arm of `constant_to_decl`, became a `Decl` with the
/// erased-return stub body, and came out here as a genuine `trust_ir::Function`
/// whose erased return the backend materializes as a boxed zero / NullPtr —
/// proof-to-exec laundering: an item with no computational meaning that the
/// FORMAT presents as executable, and that any module-level quantified
/// statement then silently ranges over.
#[test]
fn test_theorem_emits_no_trust_ir_function() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::pass_manager::{compile_lcnf_to_trust_ir, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;
    use clean_kernel::env::Declaration;
    use clean_kernel::{Environment, Expr as KExpr};

    let mut env = Environment::try_with_prelude().expect("prelude environment");

    // A real, computable definition — the control. If this stops being emitted
    // the test proves nothing about theorems.
    let def_name = Name::from_string("gapG15Def");
    env.add_decl(Declaration::Definition {
        name: def_name.clone(),
        level_params: vec![],
        type_: KExpr::arrow(KExpr::const_str("UInt32"), KExpr::const_str("UInt32")),
        value: KExpr::lam(
            clean_kernel::BinderInfo::Default,
            KExpr::const_str("UInt32"),
            KExpr::bvar(0),
        ),
        is_reducible: true,
    })
    .expect("gapG15Def kernel-checks against the prelude");

    // `theorem gapG15Thm : True := True.intro` — kernel-checked, so the
    // `ConstantKind::Theorem` under test is stamped by the KERNEL.
    let thm_name = Name::from_string("gapG15Thm");
    env.add_decl(Declaration::Theorem {
        name: thm_name.clone(),
        level_params: vec![],
        type_: KExpr::const_str("True"),
        value: KExpr::const_str("True.intro"),
    })
    .expect("`True.intro : True` kernel-checks against the prelude");

    // The REAL frontend lowering for BOTH, in one batch — exactly what a module
    // compile does. The theorem contributes no decl at all.
    let mut decls = Vec::new();
    for name in [&def_name, &thm_name] {
        let info = env.get_const(name).expect("registered");
        if let Some(decl) = constant_to_decl(&env, info).expect("stage-1 lowering is total here") {
            decls.push(decl);
        }
    }
    // Whatever stage-1 hands over goes through UNFILTERED: the assertion that
    // matters is made on the emitted module, so a regression shows up as a
    // real `trust_ir::Function` rather than as a count mismatch here.
    let survivors: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();

    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = compile_lcnf_to_trust_ir(&decls, &env, &PipelineConfig::default(), &config)
        .unwrap_or_else(|e| panic!("the pipeline must compile {survivors:?}; got {e}"));

    let emitted: Vec<&str> = module.functions.iter().map(|f| f.name.as_str()).collect();
    assert!(
        emitted.contains(&"gapG15Def"),
        "the CONTROL definition must be emitted, else this test is vacuous; \
         emitted: {emitted:?}"
    );
    assert!(
        !emitted.iter().any(|n| n.contains("gapG15Thm")),
        "a theorem must NOT become a callable trust_ir::Function \
         (proof-to-exec laundering); emitted: {emitted:?}"
    );
    // Stated last, so the FORMAT-level assertion above is the one that fires
    // on a regression: the theorem must not even reach stage-2 as a `Decl`.
    assert_eq!(
        survivors,
        vec!["gapG15Def".to_string()],
        "only the definition may survive `constant_to_decl`"
    );
}

/// GAP G15 AT THE FORMAT BOUNDARY, AT SCALE — the standing gate.
///
/// `to_lcnf::tests::test_no_prelude_theorem_ever_lowers_to_a_decl` pins the
/// stage-1 half (no theorem becomes a `Decl`);
/// `test_theorem_emits_no_trust_ir_function` above pins one hand-built theorem
/// all the way to the artifact. This one is the POPULATION statement about the
/// artifact itself: over every prelude constant that lowers, the emitted
/// `trust_ir::Module` must not NAME a `ConstantKind::Theorem` symbol —
/// anywhere in its function table or its globals, as a defined function or as
/// a bodyless extern declaration.
///
/// WHERE IT RUNS. Unconditionally in this crate's ordinary test run whenever
/// the backend lane is compiled at all (`--features trust-ir-backend`) — no
/// `#[ignore]`, no env opt-in. It cannot run in the feature-off lane because
/// `trust_ir::Module` does not exist there; the stage-1 half of the same
/// property (`test_no_prelude_theorem_ever_lowers_to_a_decl`) does run there,
/// so neither lane is unguarded.
///
/// WHY A TEST AND NOT A CLAIM. The violation compiles fine: a theorem that
/// reaches the backend becomes a perfectly valid `trust_ir::Function` with an
/// erased return, and every gate downstream (`validate_module`, the lowering
/// -target subset check) passes it. Nothing on the compile path can notice.
/// The theorem fix itself first shipped inside an `if false && …` and only a
/// test caught that, which is exactly the failure mode this guards.
///
/// TWO CHANNELS, BOTH COVERED. A theorem symbol could enter a module either
/// (a) as an in-slice decl — `emit_decl` names those VERBATIM
/// (`decl.name.to_string()`), or (b) as a dropped-callee extern —
/// `declare_extern_fallbacks` names those MANGLED. Both spellings of every
/// theorem name are therefore refused. Compiling each decl in ISOLATION is
/// deliberate: it maximizes channel (b), since every callee outside the
/// one-decl slice becomes an extern candidate.
///
/// Measured 2026-09-01: 332 prelude theorems, 976 decls lowered and 976
/// emitted, 0 theorem symbols in any module — and 195 distinct dropped-callee
/// extern symbols emitted, so channel (b) is demonstrably live rather than
/// silently empty.
#[test]
fn test_no_emitted_module_ever_names_a_theorem_symbol() {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::mangle::mangle_name;
    use crate::pass_manager::{compile_lcnf_to_trust_ir, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;
    use std::collections::{HashMap, HashSet};

    let mut env = clean_kernel::Environment::with_prelude();
    let _ = env.init_io_ops();

    // Every spelling under which a theorem could appear as a module symbol,
    // mapped back to the theorem it would betray.
    let mut theorem_symbols: HashMap<String, String> = HashMap::new();
    // Every mangled constant symbol, so the extern channel can be shown live.
    let mut all_mangled: HashSet<String> = HashSet::new();
    let mut theorem_count = 0usize;
    for c in env.constants() {
        let mangled = mangle_name(&c.name);
        all_mangled.insert(mangled.clone());
        if c.kind == clean_kernel::env::ConstantKind::Theorem {
            theorem_count += 1;
            theorem_symbols.insert(mangled, c.name.to_string());
            theorem_symbols.insert(c.name.to_string(), c.name.to_string());
        }
    }
    assert!(
        theorem_count > 250,
        "prelude theorem population collapsed ({theorem_count}) — this gate \
         would be vacuous"
    );

    let infos: Vec<clean_kernel::ConstantInfo> = env.constants().cloned().collect();
    let config = TrustIrConfig {
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };

    let mut lowered = 0usize;
    let mut emitted = 0usize;
    let mut extern_witnesses: HashSet<String> = HashSet::new();
    let mut leaks: Vec<String> = Vec::new();
    for info in &infos {
        // No `catch_unwind`: `constant_to_decl` totality over this exact
        // environment is a separately standing gate
        // (`to_lcnf::tests::test_constant_to_decl_is_total_over_prelude`), so a
        // panic here is a real regression and should surface as one.
        let Ok(Some(decl)) = constant_to_decl(&env, info) else {
            continue;
        };
        lowered += 1;
        let own_name = decl.name.to_string();
        // An `Err` is a coverage gap in the backend, not a theorem leak — skip
        // it. The floor assertions below keep that from hollowing out the gate.
        let Ok(module) = compile_lcnf_to_trust_ir(
            std::slice::from_ref(&decl),
            &env,
            &PipelineConfig::default(),
            &config,
        ) else {
            continue;
        };
        emitted += 1;

        let named: Vec<&str> = module
            .functions
            .iter()
            .map(|f| f.name.as_str())
            .chain(module.globals.iter().map(|g| g.name.as_str()))
            .collect();
        for name in named {
            if let Some(theorem) = theorem_symbols.get(name) {
                leaks.push(format!(
                    "{own_name} (from {}) emitted symbol {name} — that is the \
                     theorem {theorem}",
                    info.name
                ));
            }
            // Channel-(b) witness: a symbol that is some OTHER constant's
            // mangled name is a dropped-callee extern declaration.
            if name != own_name && all_mangled.contains(name) {
                extern_witnesses.insert(name.to_string());
            }
        }
    }

    leaks.sort();
    leaks.dedup();
    assert!(
        leaks.is_empty(),
        "{} emitted module(s) NAME a theorem symbol (proof-to-exec laundering \
         at the format boundary); first offenders: {:?}",
        leaks.len(),
        &leaks[..leaks.len().min(10)]
    );

    // Non-vacuity floors. Without these the gate passes trivially if lowering
    // or emission ever stops covering the prelude.
    assert!(
        lowered > 500,
        "only {lowered} prelude constants lowered to a Decl — the gate has \
         lost its population"
    );
    assert!(
        emitted > 500,
        "only {emitted} of {lowered} lowered decls emitted a module — the gate \
         has lost its population"
    );
    assert!(
        !extern_witnesses.is_empty(),
        "no emitted module declared a dropped-callee extern, so the channel a \
         theorem symbol would actually arrive through is not being exercised"
    );
}

// ---------------------------------------------------------------------------
// WS6.14 keep-ratchet (F-108): every emitted `FnDef` is typed at its callee's
// OWN signature.
//
// F-108 was a `() -> ()` placeholder `FnDef` — `Const { ty: Func(unit),
// value: FnDef(f) }` for an `f` declared with some other signature — which
// trust-ir v41 refuses with `ConstTypeMismatch`
// (`trust-ir-build/src/validate/constant_values.rs`, the `FnDef`/`Func` arm).
// It was closed upstream: `FnCtx::closure_fn_ptr` mints the address at the
// callee's signature and converts it to the runtime closure fn-type with a
// `PtrToPtr` cast. These tests turn that closure into a ratchet so it cannot
// regress silently: the census below reads every `FnDef` constant directly
// (not only through `validate_module`), and the negative twin re-introduces
// the placeholder and pins the exact refusal.
// ---------------------------------------------------------------------------

/// One `FnDef` constant whose declared type is not its callee's own
/// signature id (or that the census cannot check, which is reported rather
/// than skipped).
fn fndef_signature_census(module: &Module) -> (usize, Vec<String>) {
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;

    fn nested_fndef(value: &Constant) -> bool {
        value
            .children()
            .any(|child| matches!(child, Constant::FnDef(_)) || nested_fndef(child))
    }

    let mut checked = 0usize;
    let mut bad = Vec::new();
    for func in &module.functions {
        for node in func.instructions() {
            let Inst::Const { ty, value } = &node.inst else {
                continue;
            };
            match (value, ty) {
                (Constant::FnDef(callee), Ty::Func(sig)) => {
                    checked += 1;
                    let owners: Vec<&trust_ir::Function> = module
                        .functions
                        .iter()
                        .filter(|f| f.id == *callee)
                        .collect();
                    match owners.as_slice() {
                        [owner] if owner.ty == *sig => {}
                        [owner] => bad.push(format!(
                            "{}: fndef<{}> typed functy.{} but `{}` is declared functy.{}",
                            func.name,
                            owner.name,
                            sig.index(),
                            owner.name,
                            owner.ty.index()
                        )),
                        _ => bad.push(format!(
                            "{}: fndef<func.{}> names no unique module function",
                            func.name,
                            callee.index()
                        )),
                    }
                }
                (Constant::FnDef(callee), other) => bad.push(format!(
                    "{}: fndef<func.{}> typed `{other}`, not a function type",
                    func.name,
                    callee.index()
                )),
                // Fail closed on a shape this census does not type-check: the
                // emitter never nests a `FnDef` today, so one appearing is a
                // change the census must be extended for, not silently pass.
                (aggregate, _) if nested_fndef(aggregate) => bad.push(format!(
                    "{}: FnDef nested inside an aggregate constant (census does not type it)",
                    func.name
                )),
                _ => {}
            }
        }
    }
    for global in &module.globals {
        if let Some(init) = &global.initializer {
            if matches!(init, Constant::FnDef(_)) || nested_fndef(init) {
                bad.push(format!(
                    "global `{}`: FnDef initializer (census does not type it)",
                    global.name
                ));
            }
        }
    }
    bad.extend(closure_arity_census(module));
    (checked, bad)
}

/// The other half of "typed at the callee's own signature": the `PtrToPtr`
/// into `clean_alloc_closure`'s `() -> ()` fn-type ERASES the signature, and
/// the runtime then trusts the call's `arity` operand to decide how many
/// arguments `clean_apply_*` passes. A closure whose `arity` disagrees with
/// its `FnDef` callee's own parameter count validates (the cast is legal
/// between any two thin code pointers) and calls the callee at the wrong
/// arity — so the census binds them: every `clean_alloc_closure` call's `fn`
/// operand must resolve (through `PtrToPtr`) to a `FnDef`, its `arity`
/// operand to an integer constant, and the two must agree. An operand the
/// census cannot resolve is reported, never skipped.
fn closure_arity_census(module: &Module) -> Vec<String> {
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;
    use trust_ir::value::ValueId;

    let Some(alloc) = module
        .functions
        .iter()
        .find(|f| f.name == "clean_alloc_closure")
        .map(|f| f.id)
    else {
        return Vec::new();
    };
    let mut bad = Vec::new();
    for func in &module.functions {
        let defs: HashMap<ValueId, &Inst> = func
            .instructions()
            .flat_map(|n| n.results.iter().map(move |r| (*r, &n.inst)))
            .collect();
        for node in func.instructions() {
            let Inst::Call { callee, args } = &node.inst else {
                continue;
            };
            if *callee != alloc {
                continue;
            }
            let mut fn_operand = args.first().copied();
            let target = loop {
                match fn_operand.and_then(|v| defs.get(&v)) {
                    Some(Inst::Cast {
                        op: CastOp::PtrToPtr,
                        operand,
                        ..
                    }) => fn_operand = Some(*operand),
                    Some(Inst::Const {
                        value: Constant::FnDef(f),
                        ..
                    }) => break Some(*f),
                    _ => break None,
                }
            };
            let arity = match args.get(1).and_then(|v| defs.get(v)) {
                Some(Inst::Const {
                    value: Constant::Int(n),
                    ..
                }) => Some(*n),
                _ => None,
            };
            let owner = target.and_then(|t| module.functions.iter().find(|f| f.id == t));
            match (owner, arity) {
                (Some(owner), Some(arity)) => {
                    let params = module.func_types[owner.ty.index() as usize].params.len();
                    if params as i128 != arity {
                        bad.push(format!(
                            "{}: clean_alloc_closure of `{}` claims arity {arity} but \
                             `{}` takes {params} parameter(s)",
                            func.name, owner.name, owner.name
                        ));
                    }
                }
                _ => bad.push(format!(
                    "{}: clean_alloc_closure whose fn/arity operands the census cannot \
                     resolve to a FnDef and an integer constant",
                    func.name
                )),
            }
        }
    }
    bad
}

/// The census corpus: the shared `ExternCalls` e2e corpus plus the three
/// hand-built shapes that mint a `FnDef` through each of
/// `emit_partial_apply_extern`'s callee sources — an in-slice user decl, the
/// synthesized native UInt-arith wrapper, and a dropped-callee extern
/// fallback.
fn fndef_census_corpus() -> Vec<(&'static str, Vec<IRDecl>)> {
    let partial_apply = |name: &str, callee: &str, arity: u16, captured: bool| IRDecl {
        name: Name::from_string(name),
        params: if captured {
            vec![(VarId(0), IRType::Object)]
        } else {
            vec![]
        },
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(Name::from_string(callee)),
                arity,
                args: if captured {
                    vec![IRArg::Var(VarId(0))]
                } else {
                    vec![]
                },
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let add2 = IRDecl {
        name: Name::from_string("add2"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let mut corpus = extern_calls_corpus();
    corpus.push((
        "in_slice_callee",
        vec![add2, partial_apply("make", "add2", 2, false)],
    ));
    corpus.push((
        "uint_arith_wrapper",
        vec![partial_apply("root", "UInt32.add", 2, false)],
    ));
    corpus.push((
        "dropped_callee_fallback",
        vec![partial_apply("symm_like", "Missing.mpr", 2, true)],
    ));
    corpus
}

fn ws614_config(label: &str) -> TrustIrConfig {
    TrustIrConfig {
        module_name: format!("ws614_{label}"),
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// POSITIVE (hand-built corpus): every census module validates, round-trips
/// byte-exactly through the v41 module codec, and every `FnDef` it carries is
/// typed at its callee's own signature. Each of the four `FnDef`-minting
/// shapes must actually mint one, so the census cannot pass vacuously.
#[test]
fn test_emit_trust_ir_ws614_fndef_census_hand_corpus() {
    let mut total = 0usize;
    for (label, decls) in fndef_census_corpus() {
        let module = emit_trust_ir_with_config(&decls, &ws614_config(label))
            .unwrap_or_else(|e| panic!("census program `{label}` must lower: {e}"));
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "`{label}` validate_module: {errors:?}");
        let bytes = serialize_module_bytes(&module).expect("census module has a wire identity");
        let decoded = deserialize_module_bytes(&bytes)
            .unwrap_or_else(|e| panic!("`{label}` must decode its own bytes: {e}"));
        assert_eq!(
            serialize_module_bytes(&decoded).expect("decoded module has a wire identity"),
            bytes,
            "`{label}` must round-trip byte-exactly"
        );
        let (checked, bad) = fndef_signature_census(&module);
        assert!(bad.is_empty(), "`{label}` mistyped FnDef: {bad:?}");
        if matches!(
            label,
            "closure_partial_apply"
                | "in_slice_callee"
                | "uint_arith_wrapper"
                | "dropped_callee_fallback"
        ) {
            assert!(checked > 0, "`{label}` must mint a FnDef (non-vacuity)");
        }
        total += checked;
    }
    assert!(total >= 4, "census saw only {total} FnDef constants");
}

/// POSITIVE (prelude population): every prelude constant that lowers and
/// emits in isolation — the trust-cg census population, each decl its own
/// module so every out-of-slice callee becomes an extern — carries only
/// correctly typed `FnDef`s. `finalize_module` already refused any module
/// `validate_module` rejects, and such a refusal FAILS the census rather than
/// dropping the decl from it (a regressed `FnDef` is refused exactly there,
/// with `ConstTypeMismatch`); the constants are also read directly so a
/// future relaxation of the validator's `FnDef` arm cannot hide one.
#[test]
fn test_emit_trust_ir_ws614_fndef_census_prelude_population() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir, PipelineConfig, PipelineError};
    use crate::to_lcnf::constant_to_decl;

    let mut env = clean_kernel::Environment::with_prelude();
    let _ = env.init_io_ops();
    let infos: Vec<clean_kernel::ConstantInfo> = env.constants().cloned().collect();
    let config = ws614_config("prelude");

    let mut emitted = 0usize;
    let mut with_fndef: Vec<String> = Vec::new();
    let mut fndefs = 0usize;
    let mut bad: Vec<String> = Vec::new();
    for info in &infos {
        let Ok(Some(decl)) = constant_to_decl(&env, info) else {
            continue;
        };
        let module = match compile_lcnf_to_trust_ir(
            std::slice::from_ref(&decl),
            &env,
            &PipelineConfig::default(),
            &config,
        ) {
            Ok(module) => module,
            // A module the emitter's own finalization gate refuses is exactly
            // where a regressed `FnDef` would land (`ConstTypeMismatch`), so a
            // validation refusal is a census failure, never a skipped decl.
            Err(PipelineError::TrustIr(TrustIrError::Invalid(errs))) => {
                bad.push(format!("{}: validate_module refused: {errs:?}", info.name));
                continue;
            }
            // Other refusals (an unsupported construct) are outside the census.
            Err(_) => continue,
        };
        emitted += 1;
        let (checked, errs) = fndef_signature_census(&module);
        if checked > 0 {
            with_fndef.push(info.name.to_string());
        }
        fndefs += checked;
        bad.extend(errs.into_iter().map(|e| format!("{}: {e}", info.name)));
    }
    assert!(
        bad.is_empty(),
        "{} FnDef census failure(s) across the prelude population; first: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
    // Non-vacuity: the population is the census's, and the F-108 witness
    // (`instHAndUInt64`, run-4) must still be a FnDef-bearing module.
    assert!(emitted > 500, "only {emitted} prelude modules emitted");
    assert!(
        fndefs > 0 && with_fndef.len() > 10,
        "only {fndefs} FnDef constants in {} modules — census lost its subject",
        with_fndef.len()
    );
    assert!(
        with_fndef.iter().any(|n| n == "instHAndUInt64"),
        "the F-108 witness `instHAndUInt64` no longer mints a FnDef; re-pick the \
         witness rather than letting the census go quiet"
    );
}

/// The `() -> ()` placeholder signature every `ExternCalls` module interns
/// for `clean_alloc_closure`'s `fn` parameter — exactly the type F-108 minted
/// `FnDef`s at.
fn unit_fn_ty(module: &Module) -> FuncTyId {
    let index = module
        .func_types
        .iter()
        .position(|t| t.params.is_empty() && t.returns.is_empty() && !t.is_vararg)
        .expect("an ExternCalls module interns the runtime `() -> ()` closure fn-type");
    FuncTyId::new(index as u32)
}

/// Re-introduce F-108 in `module`: retype the first `FnDef` whose callee is
/// NOT declared `() -> ()` at the placeholder, and retarget its `PtrToPtr`
/// conversion so the ONLY remaining difference is the constant's type (the
/// exact pre-v41 spelling, `Const { ty: Func(unit), value: FnDef(f) }`).
/// Returns the callee's name.
fn reintroduce_unit_fndef(module: &mut Module) -> String {
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;

    let unit = unit_fn_ty(module);
    let sigs: HashMap<FuncId, (FuncTyId, String)> = module
        .functions
        .iter()
        .map(|f| (f.id, (f.ty, f.name.clone())))
        .collect();
    for func in &mut module.functions {
        for block in &mut func.blocks {
            let Some(at) = block.body.iter().position(|n| {
                matches!(&n.inst,
                    Inst::Const { ty: Ty::Func(sig), value: Constant::FnDef(callee) }
                        if *sig != unit && sigs.get(callee).is_some_and(|(own, _)| own == sig))
            }) else {
                continue;
            };
            let addr = block.body[at].results[0];
            let Inst::Const {
                ty,
                value: Constant::FnDef(callee),
            } = &mut block.body[at].inst
            else {
                unreachable!("position() matched a FnDef const");
            };
            let name = sigs[callee].1.clone();
            *ty = Ty::Func(unit);
            for node in &mut block.body[at + 1..] {
                if let Inst::Cast {
                    op: CastOp::PtrToPtr,
                    src_ty,
                    operand,
                    ..
                } = &mut node.inst
                {
                    if *operand == addr {
                        *src_ty = Ty::Func(unit);
                    }
                }
            }
            return name;
        }
    }
    panic!("module has no FnDef typed at a non-placeholder signature to mutate");
}

/// NEGATIVE TWIN: the in-slice closure fixture with ONE mutation — its
/// `FnDef` retyped to the `() -> ()` placeholder — is refused by
/// `validate_module` with `ConstTypeMismatch` naming the callee's own
/// signature, by the emitter's own finalization gate, and by the census.
/// MUTATION CONTROL: the same module unmutated is clean on all three, so the
/// placeholder type (and nothing else) causes the refusal.
#[test]
fn test_emit_trust_ir_ws614_unit_fndef_twin_is_const_type_mismatch() {
    let (label, decls) = fndef_census_corpus()
        .into_iter()
        .find(|(label, _)| *label == "in_slice_callee")
        .expect("fixture present");
    let config = ws614_config(label);
    let clean = emit_trust_ir_with_config(&decls, &config).expect("fixture lowers");
    assert!(validate_module(&clean).is_empty(), "control must validate");
    assert!(
        fndef_signature_census(&clean).1.is_empty(),
        "control census"
    );
    assert!(
        finalize_module(clean.clone(), &config).is_ok(),
        "control must pass the emitter's finalization gate"
    );

    let mut twin = clean.clone();
    let callee = reintroduce_unit_fndef(&mut twin);
    assert_eq!(callee, "add2");
    let own_sig = twin
        .functions
        .iter()
        .find(|f| f.name == "add2")
        .expect("callee")
        .ty;
    let unit = unit_fn_ty(&twin);

    let errors = validate_module(&twin);
    assert_eq!(errors.len(), 1, "exactly the one refusal: {errors:?}");
    let ValidationError::ConstTypeMismatch {
        expected, actual, ..
    } = &errors[0]
    else {
        panic!("twin must be refused with ConstTypeMismatch, got {errors:?}");
    };
    assert!(
        expected.starts_with(&format!("functy.{} for func.", own_sig.index())),
        "refusal must name the callee's own signature: {expected}"
    );
    assert_eq!(actual, &format!("functy.{}", unit.index()));

    match finalize_module(twin.clone(), &config) {
        Err(TrustIrError::Invalid(errs)) => assert!(
            errs.iter()
                .any(|e| matches!(e, ValidationError::ConstTypeMismatch { .. })),
            "finalization must refuse with ConstTypeMismatch: {errs:?}"
        ),
        other => panic!("finalization must refuse the twin, got {other:?}"),
    }

    let (_, bad) = fndef_signature_census(&twin);
    assert_eq!(bad.len(), 1, "census must flag exactly the twin: {bad:?}");
    assert!(
        bad[0].contains("fndef<add2>"),
        "census names the callee: {bad:?}"
    );
}

/// `(name, callee, arity)`: a nullary decl whose body is exactly
/// `PartialApply { callee, arity, [] }`.
fn ws614_partial_apply_decl(name: &str, callee: &str, arity: u16) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(Name::from_string(callee)),
                arity,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

/// WS6.14 review (adversarial): the `FnDef` is typed at the callee's own
/// signature, but the `PtrToPtr` into the runtime's `() -> ()` fn-type then
/// ERASES that signature, and `clean_alloc_closure`'s `arity` operand is all
/// the runtime has left. A `PartialApply` whose arity disagrees with an
/// IN-SLICE callee's parameter count used to lower to a module that
/// validates and calls the callee at the wrong arity (only a DROPPED
/// callee's arity was checked). It is refused by name, for a user decl and
/// for a synthesized UInt wrapper alike; the matching arity still lowers.
#[test]
fn test_emit_trust_ir_ws614_in_slice_partial_apply_arity_mismatch_is_refused() {
    let add2 = || IRDecl {
        name: Name::from_string("add2"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let lower = |decls: Vec<IRDecl>| emit_trust_ir_with_config(&decls, &ws614_config("arity"));

    for (decls, callee) in [
        (
            vec![add2(), ws614_partial_apply_decl("make", "add2", 3)],
            "add2",
        ),
        (
            vec![ws614_partial_apply_decl("root", "UInt32.add", 3)],
            "UInt32.add",
        ),
    ] {
        match lower(decls) {
            Err(TrustIrError::Unsupported(msg)) => assert!(
                msg.contains(&format!("PartialApply of `{callee}` with arity 3"))
                    && msg.contains("takes 2 parameter(s)"),
                "refusal must name the callee and both arities: {msg}"
            ),
            other => {
                panic!("arity-3 closure over a 2-ary `{callee}` must be refused, got {other:?}")
            }
        }
    }
    // Control: the agreeing arity lowers, and its closure passes the census.
    for decls in [
        vec![add2(), ws614_partial_apply_decl("make", "add2", 2)],
        vec![ws614_partial_apply_decl("root", "UInt32.add", 2)],
    ] {
        let module = lower(decls).expect("the agreeing arity lowers");
        assert!(fndef_signature_census(&module).1.is_empty());
    }
}

/// MUTATION CONTROL for the census's closure-arity half: the valid in-slice
/// closure module with ONE mutation — the `arity` operand of its
/// `clean_alloc_closure` call bumped from 2 to 3 — is flagged by the census,
/// naming the callee and both arities.
#[test]
fn test_emit_trust_ir_ws614_closure_arity_census_mutation() {
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;

    let (label, decls) = fndef_census_corpus()
        .into_iter()
        .find(|(label, _)| *label == "in_slice_callee")
        .expect("fixture present");
    let mut module = emit_trust_ir_with_config(&decls, &ws614_config(label)).expect("lowers");
    assert!(fndef_signature_census(&module).1.is_empty(), "control");

    let alloc = module
        .functions
        .iter()
        .find(|f| f.name == "clean_alloc_closure")
        .expect("ExternCalls declares clean_alloc_closure")
        .id;
    let arity_value = module
        .functions
        .iter()
        .flat_map(|f| f.instructions())
        .find_map(|n| match &n.inst {
            Inst::Call { callee, args } if *callee == alloc => Some(args[1]),
            _ => None,
        })
        .expect("the fixture allocates a closure");
    let mut mutated = 0;
    for func in &mut module.functions {
        for block in &mut func.blocks {
            for node in &mut block.body {
                if node.results.first() == Some(&arity_value) {
                    if let Inst::Const {
                        value: Constant::Int(n),
                        ..
                    } = &mut node.inst
                    {
                        assert_eq!(*n, 2, "the fixture's closure arity");
                        *n = 3;
                        mutated += 1;
                    }
                }
            }
        }
    }
    assert_eq!(mutated, 1, "exactly the arity constant is mutated");

    let (_, bad) = fndef_signature_census(&module);
    assert_eq!(
        bad.len(),
        1,
        "census flags exactly the mutated closure: {bad:?}"
    );
    assert!(
        bad[0].contains("clean_alloc_closure of `add2` claims arity 3")
            && bad[0].contains("`add2` takes 2 parameter(s)"),
        "{bad:?}"
    );
}

// ---------------------------------------------------------------------------
// WS6.1 (F-101): an integer unbox dispatches on representation.
//
// Measured in the two-language proof program (run 4, license-stripped
// experiment lane): `def w8 (a b : UInt8) : UInt8 := a * b + 1` boxed the
// literal `1` (a `USize`-typed small `Nat`) with the always-heap
// `clean_box_uint64`, and `UInt8.ofNat` read it back with the tagged-only
// `clean_unbox` (`ptr >> 1`), so `w8(16,16)` returned pointer bits (240), not
// the kernel-certified 1. The rule: an unbox may assume only the
// representation every producer guarantees ("tagged OR heap"), so every
// integer / `Bool` unbox reads through the dispatching `clean_unbox_uint64`;
// and a `USize` is boxed with the canonical `Nat` spelling
// `clean_nat_of_u64` (tagged below 2^63).
// ---------------------------------------------------------------------------

/// The `FuncId` of the runtime extern `name`. Panics when the extern is not
/// declared, so a checker built on it can never pass by finding nothing.
fn ws6_1_runtime_fn(module: &Module, name: &str) -> FuncId {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .map(|f| f.id)
        .unwrap_or_else(|| panic!("runtime extern `{name}` is not declared in the module"))
}

/// Every narrowing (`trunc`) or `Bool` test (`icmp`) in `module` that reads a
/// value produced by a call to the runtime extern `reader`, as
/// `"<function>: <inst>"`.
fn ws6_1_narrowings_fed_by(module: &Module, reader: &str) -> Vec<String> {
    use trust_ir::inst::Inst;
    let reader = ws6_1_runtime_fn(module, reader);
    let mut sites = Vec::new();
    for f in &module.functions {
        let produced: HashSet<ValueId> = f
            .instructions()
            .filter(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == reader))
            .flat_map(|n| n.results.iter().copied())
            .collect();
        for n in f.instructions() {
            let fed = match &n.inst {
                Inst::Cast {
                    op: CastOp::Trunc,
                    operand,
                    ..
                } => produced.contains(operand),
                Inst::ICmp { lhs, rhs, .. } => produced.contains(lhs) || produced.contains(rhs),
                _ => false,
            };
            if fed {
                sites.push(format!("{}: {:?}", f.name, n.inst));
            }
        }
    }
    sites
}

/// Calls to the runtime extern `name` anywhere in `module`.
fn ws6_1_calls_to(module: &Module, name: &str) -> usize {
    use trust_ir::inst::Inst;
    let id = ws6_1_runtime_fn(module, name);
    module
        .instructions()
        .filter(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == id))
        .count()
}

/// MUTATION: revert the WS6.1 consumer fix inside an emitted module — every
/// `clean_unbox_uint64` call whose result feeds a narrowing `trunc` or a
/// `Bool` `icmp` is re-pointed at the tagged-only `clean_unbox` (same
/// `(ptr) -> u64` signature). Returns how many calls were reverted.
fn ws6_1_revert_narrow_readers(module: &mut Module) -> usize {
    use trust_ir::inst::Inst;
    let dispatching = ws6_1_runtime_fn(module, "clean_unbox_uint64");
    let tagged_only = ws6_1_runtime_fn(module, "clean_unbox");
    let mut reverted = 0;
    for f in &mut module.functions {
        let narrowed: HashSet<ValueId> = f
            .instructions()
            .filter_map(|n| match &n.inst {
                Inst::Cast {
                    op: CastOp::Trunc,
                    operand,
                    ..
                } => Some(vec![*operand]),
                Inst::ICmp { lhs, rhs, .. } => Some(vec![*lhs, *rhs]),
                _ => None,
            })
            .flatten()
            .collect();
        for block in &mut f.blocks {
            for node in &mut block.body {
                if let Inst::Call { callee, .. } = &mut node.inst {
                    if *callee == dispatching && node.results.iter().any(|r| narrowed.contains(r)) {
                        *callee = tagged_only;
                        reverted += 1;
                    }
                }
            }
        }
    }
    reverted
}

/// `fn unbox_at(o: Object) -> ty { let x : ty = Unbox ty o; ret x }`.
fn ws6_1_unbox_decl(name: &str, ty: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(VarId(0), IRType::Object)],
        return_type: ty.clone(),
        body: IRBody::VDecl {
            var: VarId(1),
            ty: ty.clone(),
            value: IRExpr::Unbox {
                ty,
                arg: IRArg::Var(VarId(0)),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

fn ws6_1_extern_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "ws6_1".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// Positive, structural (hand-built L5IR): in `ExternCalls` mode no integer or
/// `Bool` `Unbox` calls the tagged-only `clean_unbox`, and each narrowing arm
/// reads the dispatching `clean_unbox_uint64`. Mutation control: re-pointing
/// those reads at `clean_unbox` is caught by the same checker.
#[test]
fn test_ws6_1_integer_unbox_reads_the_dispatching_reader() {
    let decls = vec![
        ws6_1_unbox_decl("unbox_u8", IRType::UInt8),
        ws6_1_unbox_decl("unbox_u16", IRType::UInt16),
        ws6_1_unbox_decl("unbox_bool", IRType::Bool),
        ws6_1_unbox_decl("unbox_u32", IRType::UInt32),
        ws6_1_unbox_decl("unbox_u64", IRType::UInt64),
        ws6_1_unbox_decl("unbox_usize", IRType::USize),
    ];
    let module = emit_trust_ir_with_config(&decls, &ws6_1_extern_config())
        .expect("every scalar unbox lowers in ExternCalls mode");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");

    assert_eq!(
        ws6_1_calls_to(&module, "clean_unbox"),
        0,
        "no scalar unbox may read the tagged-only `clean_unbox`"
    );
    assert!(ws6_1_narrowings_fed_by(&module, "clean_unbox").is_empty());
    // u8 trunc + u16 trunc + Bool icmp: the three arms the bug lived in.
    let dispatching = ws6_1_narrowings_fed_by(&module, "clean_unbox_uint64");
    assert_eq!(
        dispatching.len(),
        3,
        "UInt8, UInt16 and Bool must each narrow a `clean_unbox_uint64` read: {dispatching:?}"
    );
    // `clean_unbox_uint64` backs UInt8/UInt16/Bool/UInt64/USize; UInt32 keeps
    // its own dispatching `clean_unbox_uint32`.
    assert_eq!(ws6_1_calls_to(&module, "clean_unbox_uint64"), 5);
    assert_eq!(ws6_1_calls_to(&module, "clean_unbox_uint32"), 1);

    // Mutation control: the pre-WS6.1 shape (tagged-only read, then narrow)
    // is exactly what the checker refuses.
    let mut reverted = module.clone();
    assert_eq!(ws6_1_revert_narrow_readers(&mut reverted), 3);
    let caught = ws6_1_narrowings_fed_by(&reverted, "clean_unbox");
    assert_eq!(
        caught.len(),
        3,
        "the checker must flag every reverted narrowing: {caught:?}"
    );
}

/// Negative twin: an `Unbox` at a type with no scalar representation is
/// REFUSED with the named reason (it used to fall through to `clean_unbox`
/// and hand back a `u64` of pointer bits). The non-`ExternCalls` (dialect)
/// path hands the type attribute to the consumer's own lowering; it is not
/// used by `--emit trustir-bin|obj` and is out of scope here.
#[test]
fn test_ws6_1_unbox_at_non_scalar_type_is_refused() {
    let non_scalars = [
        IRType::Object,
        IRType::TObject,
        IRType::Struct(vec![IRType::UInt8]),
        IRType::Union(vec![IRType::UInt8]),
        IRType::Erased,
        IRType::Void,
    ];
    for ty in non_scalars {
        let decl = IRDecl {
            name: Name::from_string("unbox_non_scalar"),
            params: vec![(VarId(0), IRType::Object)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(1),
                ty: ty.clone(),
                value: IRExpr::Unbox {
                    ty: ty.clone(),
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        };
        let want = format!("unbox at non-scalar type {ty:?} has no representation-faithful reader");
        match emit_trust_ir_with_config(&[decl], &ws6_1_extern_config()) {
            Err(TrustIrError::Unsupported(msg)) => {
                assert!(
                    msg.contains(&want),
                    "{ty:?}: wrong refusal `{msg}`, want `{want}`"
                )
            }
            other => panic!("{ty:?}: unbox must be refused with `{want}`, got {other:?}"),
        }
    }
}

/// Producer canonicalization (WS6.1 DECIDE (b)): a `USize` is boxed with the
/// runtime's one `Nat` spelling `clean_nat_of_u64` (tagged below 2^63), never
/// the always-heap `clean_box_uint64`; a genuine `UInt64` object stays heap.
#[test]
fn test_ws6_1_usize_box_is_the_canonical_nat_spelling() {
    fn box_decl(name: &str, ty: IRType) -> IRDecl {
        IRDecl {
            name: Name::from_string(name),
            params: vec![(VarId(0), ty.clone())],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(1),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty,
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
            },
        }
    }
    let usize_only = emit_trust_ir_with_config(
        &[box_decl("box_usize", IRType::USize)],
        &ws6_1_extern_config(),
    )
    .expect("USize box lowers");
    assert!(validate_module(&usize_only).is_empty());
    assert_eq!(ws6_1_calls_to(&usize_only, "clean_nat_of_u64"), 1);
    assert_eq!(
        ws6_1_calls_to(&usize_only, "clean_box_uint64"),
        0,
        "a USize must not get the heap spelling"
    );

    let uint64_only = emit_trust_ir_with_config(
        &[box_decl("box_u64", IRType::UInt64)],
        &ws6_1_extern_config(),
    )
    .expect("UInt64 box lowers");
    assert_eq!(ws6_1_calls_to(&uint64_only, "clean_box_uint64"), 1);
    assert_eq!(ws6_1_calls_to(&uint64_only, "clean_nat_of_u64"), 0);
}

// ---- the p12 program through the REAL pipeline, kernel to native ----------

/// The prelude `Nat` primitives the runtime provides as shims (the
/// `trustcg_census` / clean-cli denylist discipline): a dependency on one is
/// dropped to an extern `l_Nat_*`, linked against [`WS6_1_NAT_SHIMS_C`].
const WS6_1_NAT_SHIMMED: &[&str] = &[
    "Nat.add",
    "Nat.mul",
    "Nat.sub",
    "Nat.div",
    "Nat.mod",
    "Nat.decEq",
    "Nat.shiftRight",
    "Nat.ble",
    "Nat.blt",
    "Nat.beq",
];

const WS6_1_NAT_SHIMS_C: &str = "\
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_nat_add(a, b); }
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_nat_mul(a, b); }
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { return clean_nat_sub(a, b); }
clean_obj* l_Nat_div(clean_obj* a, clean_obj* b) { return clean_nat_div(a, b); }
clean_obj* l_Nat_mod(clean_obj* a, clean_obj* b) { return clean_nat_mod(a, b); }
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_nat_dec_eq(a, b); }
clean_obj* l_Nat_shiftRight(clean_obj* a, clean_obj* b) { return clean_nat_shift_right(a, b); }
clean_obj* l_Nat_ble(clean_obj* a, clean_obj* b) { return clean_nat_ble(a, b); }
clean_obj* l_Nat_blt(clean_obj* a, clean_obj* b) { return clean_nat_blt(a, b); }
clean_obj* l_Nat_beq(clean_obj* a, clean_obj* b) { return clean_nat_beq(a, b); }
";

/// The w8 differential vectors `(a, b, w8 a b)`: the proof program's three
/// kernel-certified values, re-certified by the kernel in [`ws6_1_env`].
const WS6_1_W8_VECTORS: [(u64, u64, u64); 3] = [(16, 16, 1), (15, 17, 0), (3, 4, 13)];

/// `UInt8.ofNat n` as a kernel term.
fn ws6_1_u8(n: u64) -> clean_kernel::Expr {
    clean_kernel::Expr::app(
        clean_kernel::Expr::const_str("UInt8.ofNat"),
        clean_kernel::Expr::nat_lit(n),
    )
}

/// `theorem <name> : w8 a b = r := rfl`, for the kernel to check.
fn ws6_1_w8_theorem(name: &str, (a, b, r): (u64, u64, u64)) -> clean_kernel::env::Declaration {
    use clean_kernel::{Expr as KExpr, Level};
    let u8t = KExpr::const_str("UInt8");
    let lvl = vec![Level::succ(Level::zero())];
    let lhs = KExpr::apps(KExpr::const_str("w8"), [ws6_1_u8(a), ws6_1_u8(b)]);
    clean_kernel::env::Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: KExpr::apps(
            KExpr::const_(Name::from_string("Eq"), lvl.clone()),
            [u8t.clone(), lhs, ws6_1_u8(r)],
        ),
        value: KExpr::apps(
            KExpr::const_(Name::from_string("Eq.refl"), lvl),
            [u8t, ws6_1_u8(r)],
        ),
    }
}

/// The prelude plus the proof program's `p12_mixed_widths` root and the
/// adversarial twin, as kernel-checked definitions:
///
/// ```text
/// def w8 (a b : UInt8) : UInt8 := a * b + 1
/// def w8big (a : UInt64) : UInt8 := UInt8.ofNat a.toNat
/// ```
///
/// Every `w8` vector is certified here by `rfl` (so the native expectations
/// are the kernel's, not a hand constant), and each vector off by one is
/// REFUSED by the kernel, so the certification is not vacuous.
fn ws6_1_env() -> clean_kernel::Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::{BinderInfo, Environment, Expr as KExpr};
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    let u8t = KExpr::const_str("UInt8");
    let u64t = KExpr::const_str("UInt64");
    let w8_body = KExpr::apps(
        KExpr::const_str("UInt8.add"),
        [
            KExpr::apps(
                KExpr::const_str("UInt8.mul"),
                [KExpr::bvar(1), KExpr::bvar(0)],
            ),
            ws6_1_u8(1),
        ],
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("w8"),
        level_params: vec![],
        type_: KExpr::arrow(u8t.clone(), KExpr::arrow(u8t.clone(), u8t.clone())),
        value: KExpr::lam(
            BinderInfo::Default,
            u8t.clone(),
            KExpr::lam(BinderInfo::Default, u8t.clone(), w8_body),
        ),
        is_reducible: true,
    })
    .expect("w8 kernel-checks against the prelude");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("w8big"),
        level_params: vec![],
        type_: KExpr::arrow(u64t.clone(), u8t),
        value: KExpr::lam(
            BinderInfo::Default,
            u64t,
            KExpr::app(
                KExpr::const_str("UInt8.ofNat"),
                KExpr::app(KExpr::const_str("UInt64.toNat"), KExpr::bvar(0)),
            ),
        ),
        is_reducible: true,
    })
    .expect("w8big kernel-checks against the prelude");
    for (i, v) in WS6_1_W8_VECTORS.into_iter().enumerate() {
        let (a, b, r) = v;
        let wrong = (a, b, (r + 1) % 256);
        assert!(
            env.add_decl(ws6_1_w8_theorem(&format!("ws6_1_w8_off_by_one_{i}"), wrong))
                .is_err(),
            "the kernel must REFUSE `w8 {a} {b} = {}`",
            wrong.2
        );
        env.add_decl(ws6_1_w8_theorem(&format!("ws6_1_w8_vector_{i}"), v))
            .unwrap_or_else(|e| panic!("the kernel must certify `w8 {a} {b} = {r}`: {e:?}"));
    }
    env
}

/// The roots and their dependency closure (the `trustcg_census` BFS: a
/// dependency that does not lower on its own is dropped to an extern, and the
/// `Nat` primitives in [`WS6_1_NAT_SHIMMED`] always are).
fn ws6_1_closure(env: &clean_kernel::Environment, roots: &[&str]) -> Vec<crate::Decl> {
    ws6_1_closure_shimming(env, roots, WS6_1_NAT_SHIMMED)
}

/// [`ws6_1_closure`] with an explicit shim list (`shimmed` dependencies are
/// always dropped to externs).
fn ws6_1_closure_shimming(
    env: &clean_kernel::Environment,
    roots: &[&str],
    shimmed: &[&str],
) -> Vec<crate::Decl> {
    use crate::pass_manager::{compile_lcnf_decls, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;
    use clean_kernel::{ExprVisitor, LevelVec};
    struct Deps(Vec<Name>);
    impl ExprVisitor for Deps {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
            self.0.push(name.clone());
        }
    }
    let mut seen: HashSet<Name> = HashSet::new();
    let mut decls = Vec::new();
    let mut work: Vec<(Name, bool)> = roots
        .iter()
        .rev()
        .map(|r| (Name::from_string(r), true))
        .collect();
    while let Some((name, is_root)) = work.pop() {
        if !seen.insert(name.clone()) || (!is_root && shimmed.contains(&name.to_string().as_str()))
        {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            assert!(!is_root, "root `{name}` is not in the environment");
            continue;
        };
        let decl = match constant_to_decl(env, info) {
            Ok(Some(decl)) => decl,
            _ => {
                assert!(!is_root, "root `{name}` does not lower");
                continue;
            }
        };
        if compile_lcnf_decls(std::slice::from_ref(&decl), env, &PipelineConfig::default()).is_err()
        {
            assert!(!is_root, "root `{name}` does not compile");
            continue;
        }
        if let Some(value) = &info.value {
            let mut deps = Deps(Vec::new());
            deps.visit_expr(value);
            work.extend(deps.0.into_iter().map(|d| (d, false)));
        }
        decls.push(decl);
    }
    decls
}

/// The compiled p12 artifacts: `w8`, `w8big`, `UInt8.ofNat`, `UInt16.ofNat`,
/// at `-O0`: WS6.4 resolves `w8`'s arithmetic and folds its `UInt8.ofNat 1`
/// at `-O1`/`-O2`, which would hide the boxed-`Nat` path these fixtures
/// exist to exercise. The `-O1`/`-O2` oracle runs are
/// [`ws6_1_artifacts_at`]'s other callers (`ws6_4` tests).
fn ws6_1_artifacts() -> crate::pass_manager::PipelineArtifacts {
    ws6_1_artifacts_at(&crate::rc_repair::e2e_support::o0())
}

/// [`ws6_1_artifacts`] through an explicit pipeline.
pub(super) fn ws6_1_artifacts_at(
    pipeline: &crate::pass_manager::PipelineConfig,
) -> crate::pass_manager::PipelineArtifacts {
    use crate::pass_manager::compile_lcnf_decls;
    let env = ws6_1_env();
    let decls = ws6_1_closure(&env, &["w8", "w8big", "UInt8.ofNat", "UInt16.ofNat"]);
    compile_lcnf_decls(&decls, &env, pipeline)
        .expect("the p12 closure compiles through the real pipeline")
}

/// Positive, structural, on the REAL pipeline: the p12 closure's emitted
/// module never calls `clean_unbox`, and its `UInt8.ofNat` / `UInt16.ofNat`
/// narrow a `clean_unbox_uint64` read.
#[test]
fn test_ws6_1_p12_module_has_no_tagged_only_unbox() {
    let module = ws6_1_artifacts()
        .emit_trust_ir(&ws6_1_extern_config())
        .expect("p12 lowers to trust-ir");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
    assert_eq!(ws6_1_calls_to(&module, "clean_unbox"), 0);
    let dispatching = ws6_1_narrowings_fed_by(&module, "clean_unbox_uint64");
    for f in ["UInt8.ofNat", "UInt16.ofNat"] {
        assert!(
            dispatching.iter().any(|s| s.starts_with(&format!("{f}: "))),
            "`{f}` must narrow a dispatching read; narrowings: {dispatching:?}"
        );
    }
    // The literal `1` in `w8` is a `USize`: boxed tagged, never heap.
    assert!(ws6_1_calls_to(&module, "clean_nat_of_u64") > 0);
}

/// Compile `c_sources` (plus the runtime) into one binary, run it, and return
/// its trimmed stdout. `objects` are linked as-is.
fn ws6_1_build_and_run(
    dir: &std::path::Path,
    label: &str,
    c_sources: &[(&str, String)],
    objects: &[&std::path::Path],
    arch: &str,
) -> String {
    let rt_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime");
    let bin = dir.join(format!("{label}_bin"));
    let mut cc = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut cc, arch);
    cc.args(["-O0", "-I"])
        .arg(rt_dir.join("include"))
        .arg("-o")
        .arg(&bin);
    for (name, text) in c_sources {
        let path = dir.join(format!("{label}_{name}"));
        std::fs::write(&path, text).expect("write C source");
        cc.arg(path);
    }
    cc.arg(rt_dir.join("src/clean_runtime.c"));
    for obj in objects {
        cc.arg(obj);
    }
    let out = cc.output().expect("spawn cc");
    assert!(
        out.status.success(),
        "{label}: cc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = std::process::Command::new(&bin)
        .output()
        .expect("run the WS6.1 driver");
    assert!(
        run.status.success(),
        "{label}: driver exited {:?}; stderr: {}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout).trim().to_string()
}

/// The differential comparator: `got` must be exactly the expected values,
/// space-separated. An `Err` names the first differing position.
fn ws6_1_check(label: &str, got: &str, want: &[u64]) -> Result<(), String> {
    let got_vals: Vec<&str> = got.split_whitespace().collect();
    let want_vals: Vec<String> = want.iter().map(u64::to_string).collect();
    if got_vals.len() != want_vals.len() {
        return Err(format!(
            "{label}: got `{got}`, want `{}`",
            want_vals.join(" ")
        ));
    }
    for (i, (g, w)) in got_vals.iter().zip(&want_vals).enumerate() {
        if g != w {
            return Err(format!(
                "{label}: position {i}: got {g}, want {w} (full: `{got}`)"
            ));
        }
    }
    Ok(())
}

/// The driver's entry points, by lane. `w8`/`w8big` take and return unboxed
/// scalars; `UInt{8,16}.ofNat` take a borrowed `Nat` object.
const WS6_1_W8_MAIN: &str = "int main(void){ printf(\"%u %u %u\\n\", \
    (unsigned)ws_w8(16,16), (unsigned)ws_w8(15,17), (unsigned)ws_w8(3,4)); return 0; }\n";

/// The heap paths the measured bug did not reach: a two-limb heap `Nat`
/// (`2^63+5`, via `UInt64.toNat` and via `clean_nat_of_u64`), a
/// `clean_box_uint64` cell (`scalar_sz 8`, `2^40+7`), and a tagged control.
const WS6_1_HEAP_MAIN: &str = "int main(void){ \
    uint64_t big = 0x8000000000000005ull, mid = (1ull << 40) + 7; \
    printf(\"%u %u %u %u %u %u %u %u\\n\", \
      (unsigned)ws_w8big(big), (unsigned)ws_w8big(mid), \
      (unsigned)ws_u8(clean_box(300)), (unsigned)ws_u8(clean_box_uint64(mid)), \
      (unsigned)ws_u8(clean_nat_of_u64(big)), \
      (unsigned)ws_u16(clean_box(65537)), (unsigned)ws_u16(clean_box_uint64(mid)), \
      (unsigned)ws_u16(clean_nat_of_u64(big))); return 0; }\n";
const WS6_1_HEAP_WANT: [u64; 8] = [5, 7, 44, 7, 5, 1, 7, 5];
/// The positions of [`WS6_1_HEAP_WANT`] that read a HEAP cell through
/// `UInt{8,16}.ofNat`: the ones a tagged-only reader must get wrong.
const WS6_1_HEAP_CELL_POSITIONS: [usize; 4] = [3, 4, 6, 7];

fn ws6_1_host() -> Option<(&'static str, &'static str)> {
    match std::env::consts::ARCH {
        "aarch64" => Some(("aarch64", "arm64")),
        "x86_64" => Some(("x86_64", "x86_64")),
        _ => None,
    }
}

/// `--emit c` lane: one translation unit (shims, the emitted C, entry
/// wrappers, `main`), run against the runtime.
fn ws6_1_run_c(c_code: &str, main: &str, dir: &std::path::Path, label: &str, arch: &str) -> String {
    let m = |s: &str| crate::mangle::mangle_name(&Name::from_string(s));
    let tu = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n{WS6_1_NAT_SHIMS_C}\n{c_code}\n\
         static uint8_t ws_w8(uint8_t a, uint8_t b) {{ return {}(a, b); }}\n\
         static uint8_t ws_w8big(uint64_t a) {{ return {}(a); }}\n\
         static uint8_t ws_u8(clean_obj* n) {{ return {}(n); }}\n\
         static uint16_t ws_u16(clean_obj* n) {{ return {}(n); }}\n{main}",
        m("w8"),
        m("w8big"),
        m("UInt8.ofNat"),
        m("UInt16.ofNat"),
    );
    ws6_1_build_and_run(dir, label, &[("tu.c", tu)], &[], arch)
}

/// trust-ir -> trust-cg lane, in the EXPERIMENT (license-stripped) fixture:
/// the producer's `Ungated` refusal is checked first by
/// [`write_legacy_native_fixture`], which then clears the claim on a clone.
fn ws6_1_run_trust_ir(
    module: &Module,
    trust_cg: &std::path::Path,
    main: &str,
    dir: &std::path::Path,
    label: &str,
    (target, arch): (&str, &str),
) -> String {
    let tmbc = dir.join(format!("{label}.tmbc"));
    let obj = dir.join(format!("{label}.o"));
    write_legacy_native_fixture(module, trust_cg, target, &tmbc);
    let cg = legacy_trust_cg(trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "{label}: trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    // trust-cg keeps the raw decl names as link symbols; C reaches them
    // through asm labels (Mach-O prefixes an underscore).
    let p = if cfg!(target_os = "macos") { "_" } else { "" };
    let driver = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
         extern uint8_t ws_w8(uint8_t, uint8_t) __asm__(\"{p}w8\");\n\
         extern uint8_t ws_w8big(uint64_t) __asm__(\"{p}w8big\");\n\
         extern uint8_t ws_u8(clean_obj*) __asm__(\"{p}UInt8.ofNat\");\n\
         extern uint16_t ws_u16(clean_obj*) __asm__(\"{p}UInt16.ofNat\");\n{main}"
    );
    let rt_extern = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-runtime/src/runtime_extern.c");
    let rt_extern = std::fs::read_to_string(rt_extern).expect("read runtime_extern.c");
    let shims = format!("#include \"clean_runtime.h\"\n{WS6_1_NAT_SHIMS_C}");
    ws6_1_build_and_run(
        dir,
        label,
        &[
            ("driver.c", driver),
            ("shims.c", shims),
            ("runtime_extern.c", rt_extern),
        ],
        &[&obj],
        arch,
    )
}

/// GAP row `GENERAL.p12_mixed_widths.w8.linkrun` (PRODUCER-GAP -> PASS in the
/// EXPERIMENT lane only; the licensed row stays refused until WS6.6 earns
/// `Gated`): `w8` compiled from the kernel through the real pipeline computes
/// the kernel-certified `1 0 13`, through `--emit c` AND through
/// trust-ir -> trust-cg. Negative twin: the same differential with each
/// expectation off by one is REJECTED by the comparator.
#[test]
fn general_p12_mixed_widths_w8_linkrun() {
    let Some(host) = ws6_1_host() else {
        eprintln!("w8 linkrun skipped: unsupported host arch");
        // SELF-SKIP OK: native link/run lanes support only aarch64/x86_64 hosts; other arches skip (printed).
        return;
    };
    let want: Vec<u64> = WS6_1_W8_VECTORS.iter().map(|v| v.2).collect();
    let art = ws6_1_artifacts();
    let dir = tempfile::tempdir().expect("tempdir");
    let mut lanes = vec![(
        "emit_c",
        ws6_1_run_c(
            &art.emit_c(crate::emit_c::CEmitConfig::default())
                .expect("p12 lowers to C"),
            WS6_1_W8_MAIN,
            dir.path(),
            "w8_c",
            host.1,
        ),
    )];
    match find_trust_cg() {
        Some(trust_cg) => {
            let module = art
                .emit_trust_ir(&ws6_1_extern_config())
                .expect("p12 lowers to trust-ir");
            lanes.push((
                "trust-ir",
                ws6_1_run_trust_ir(&module, &trust_cg, WS6_1_W8_MAIN, dir.path(), "w8_ti", host),
            ));
        }
        None => eprintln!("w8 trust-ir lane skipped: trust-cg binary not found"),
    }
    for (lane, got) in &lanes {
        ws6_1_check(lane, got, &want).unwrap_or_else(|e| panic!("{e}"));
        for i in 0..want.len() {
            let mut off = want.clone();
            off[i] = (off[i] + 1) % 256;
            assert!(
                ws6_1_check(lane, got, &off).is_err(),
                "{lane}: the differential must REJECT expectation {i} off by one ({off:?})"
            );
        }
    }
}

/// Adversarial / mutation control: the heap cells the measured bug did not
/// reach, through `--emit c` AND trust-ir -> trust-cg. Reverting either
/// backend's narrowing arms to the tagged-only `clean_unbox` must fail every
/// heap-cell vector (and the tagged controls must still pass, so the failure
/// is the reader's, not the harness's).
#[test]
fn test_ws6_1_heap_nat_unbox_vectors_and_mutation_control() {
    let Some(host) = ws6_1_host() else {
        eprintln!("heap-unbox vectors skipped: unsupported host arch");
        // SELF-SKIP OK: native link/run lanes support only aarch64/x86_64 hosts; other arches skip (printed).
        return;
    };
    let art = ws6_1_artifacts();
    let dir = tempfile::tempdir().expect("tempdir");
    let assert_reverted_fails = |lane: &str, got: &str| {
        let vals: Vec<&str> = got.split_whitespace().collect();
        assert_eq!(
            vals.len(),
            WS6_1_HEAP_WANT.len(),
            "{lane} (reverted): `{got}`"
        );
        for i in WS6_1_HEAP_CELL_POSITIONS {
            assert_ne!(
                vals[i],
                WS6_1_HEAP_WANT[i].to_string(),
                "{lane}: with the tagged-only reader restored, heap vector {i} must be WRONG (`{got}`)"
            );
        }
        for i in [2, 5] {
            assert_eq!(
                vals[i],
                WS6_1_HEAP_WANT[i].to_string(),
                "{lane}: tagged control {i} must still pass under the mutation (`{got}`)"
            );
        }
    };

    // --emit c.
    let c_code = art
        .emit_c(crate::emit_c::CEmitConfig::default())
        .expect("p12 lowers to C");
    let got = ws6_1_run_c(&c_code, WS6_1_HEAP_MAIN, dir.path(), "heap_c", host.1);
    ws6_1_check("emit_c", &got, &WS6_1_HEAP_WANT).unwrap_or_else(|e| panic!("{e}"));
    let reverted_c = c_code
        .replace("(uint8_t)clean_unbox_uint64(", "(uint8_t)clean_unbox(")
        .replace("(uint16_t)clean_unbox_uint64(", "(uint16_t)clean_unbox(");
    assert_ne!(
        reverted_c, c_code,
        "the C mutation must change the emitted code"
    );
    let got = ws6_1_run_c(
        &reverted_c,
        WS6_1_HEAP_MAIN,
        dir.path(),
        "heap_c_rev",
        host.1,
    );
    assert_reverted_fails("emit_c", &got);

    // trust-ir -> trust-cg.
    let Some(trust_cg) = find_trust_cg() else {
        eprintln!("heap-unbox trust-ir lane skipped: trust-cg binary not found");
        // SELF-SKIP OK: trust-cg is an external binary outside this tree; only the trust-ir lane skips (printed), the emit_c lane has already asserted.
        return;
    };
    let module = art
        .emit_trust_ir(&ws6_1_extern_config())
        .expect("p12 lowers to trust-ir");
    let got = ws6_1_run_trust_ir(
        &module,
        &trust_cg,
        WS6_1_HEAP_MAIN,
        dir.path(),
        "heap_ti",
        host,
    );
    ws6_1_check("trust-ir", &got, &WS6_1_HEAP_WANT).unwrap_or_else(|e| panic!("{e}"));
    let mut reverted = module.clone();
    assert!(ws6_1_revert_narrow_readers(&mut reverted) > 0);
    let got = ws6_1_run_trust_ir(
        &reverted,
        &trust_cg,
        WS6_1_HEAP_MAIN,
        dir.path(),
        "heap_ti_rev",
        host,
    );
    assert_reverted_fails("trust-ir", &got);
}

/// The WS6.1 Gate census: no `Unbox USize` consumes a `Nat`-typed value that
/// may reach 2^64.
///
/// The dispatching reader returns a `Nat`'s LOW LIMB, which is exact only for
/// a consumer whose semantics is mod 2^w with w <= 64 (every `UIntW.ofNat`) or
/// whose value is bounded below 2^64. An `Unbox USize` of an unbounded `Nat`
/// would silently truncate it, so every `Unbox USize` the backend receives
/// over the full prelude (each computable constant compiled on its own, as
/// `test_no_emitted_module_ever_names_a_theorem_symbol` does) must fall in one
/// of three classes, and anything else fails here BY NAME (a refusal row,
/// never a waiver):
///
/// 1. **enum tag** — the unboxed value is the scrutinee of the very next
///    `Case` (reading past `inc`/`dec` statements, which only move reference
///    counts: WS6.2's post-boxing repair releases the boxed object right
///    after this unbox, its last read), and every alternative is a
///    field-less constructor (`Bool`, `Ordering`, `Decidable`-as-`Bool`, or
///    an empty eliminator). A constructor tag, never a `Nat`.
/// 2. **boxed-ABI wrapper** — the `mk_boxed_version` shim of a sibling decl,
///    unboxing its i-th parameter for the sibling's i-th parameter, which is
///    declared `USize`, i.e. kernel-typed `USize` (`to_ir` types `Nat` as
///    `Object`, never `USize`). A machine word.
/// 3. **bounded `ofNat`** — `USize.ofNatLT n h` unboxes its `n : Nat`, but
///    `h : n < USize.size` bounds it below 2^64, so the low limb IS `n` (the
///    Sound rule's covered case); `USize.ofNat` unboxes the `USize` that
///    `USize.ofNatLT` returns.
///
/// Measured 2026-09-18 on this tree: 129 sites — 104 enum tags, 23 boxed
/// wrappers, and the two bounded-`ofNat` rows.
#[test]
fn test_ws6_1_no_usize_unbox_of_an_unbounded_nat_over_the_prelude() {
    use crate::pass_manager::{compile_lcnf_decls, PipelineConfig};
    use crate::to_lcnf::constant_to_decl;

    const BOUNDED_OFNAT: &[&str] = &["USize.ofNatLT", "USize.ofNat"];

    #[derive(Default)]
    struct Census {
        enum_tag: usize,
        boxed_wrapper: usize,
        bounded: BTreeMap<String, usize>,
        refused: Vec<String>,
        /// Boxed-wrapper name -> the parameter types of the decl it wraps,
        /// for the artifact being walked.
        wrappers: HashMap<String, Vec<IRType>>,
    }

    fn walk(decl: &IRDecl, body: &IRBody, census: &mut Census) {
        match body {
            IRBody::VDecl {
                var, value, rest, ..
            } => {
                if let IRExpr::Unbox {
                    ty: IRType::USize,
                    arg,
                } = value
                {
                    classify(decl, *var, arg, rest, census);
                }
                walk(decl, rest, census)
            }
            IRBody::JDecl { body, rest, .. } => {
                walk(decl, body, census);
                walk(decl, rest, census)
            }
            IRBody::Case { alts, default, .. } => {
                for alt in alts {
                    walk(decl, &alt.body, census)
                }
                if let Some(d) = default {
                    walk(decl, d, census)
                }
            }
            IRBody::Inc { rest, .. }
            | IRBody::Dec { rest, .. }
            | IRBody::Set { rest, .. }
            | IRBody::SetTag { rest, .. }
            | IRBody::USet { rest, .. }
            | IRBody::SSet { rest, .. } => walk(decl, rest, census),
            IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
        }
    }

    fn classify(decl: &IRDecl, var: VarId, arg: &IRArg, rest: &IRBody, census: &mut Census) {
        let name = decl.name.to_string();
        // RC statements between the unbox and its consumer do not change
        // what the unboxed value is used for (the unboxed `USize` itself is
        // a scalar and is never their operand).
        let mut next = rest;
        while let IRBody::Inc { var: v, rest, .. } | IRBody::Dec { var: v, rest } = next {
            assert_ne!(*v, var, "an RC operation on the unboxed scalar itself");
            next = rest;
        }
        if let IRBody::Case {
            scrutinee, alts, ..
        } = next
        {
            if *scrutinee == var
                && alts.iter().all(|a| {
                    a.ctor.num_objects == 0
                        && a.ctor.num_scalars == 0
                        && !a.ctor.name.to_string().starts_with("Nat.")
                })
            {
                census.enum_tag += 1;
                return;
            }
        }
        // The boxed-ABI version of a sibling decl (`mk_boxed_version`),
        // unboxing its i-th parameter for the sibling's i-th parameter, which
        // must itself be declared `USize`.
        let param_index = match arg {
            IRArg::Var(v) => decl.params.iter().position(|(p, _)| p == v),
            IRArg::Erased => None,
        };
        if let (Some(i), Some(unboxed_params)) = (param_index, census.wrappers.get(&name)) {
            if unboxed_params.get(i) == Some(&IRType::USize) {
                census.boxed_wrapper += 1;
                return;
            }
        }
        if BOUNDED_OFNAT.contains(&name.as_str()) {
            *census.bounded.entry(name).or_default() += 1;
            return;
        }
        census
            .refused
            .push(format!("{name}: Unbox USize of {arg:?} (next: {})", {
                let next = format!("{rest:?}");
                next.chars().take(160).collect::<String>()
            }));
    }

    let mut env = clean_kernel::Environment::with_prelude();
    let _ = env.init_io_ops();
    let infos: Vec<clean_kernel::ConstantInfo> = env.constants().cloned().collect();
    let mut census = Census::default();
    let mut compiled = 0usize;
    for info in &infos {
        let Ok(Some(decl)) = constant_to_decl(&env, info) else {
            continue;
        };
        let Ok(art) = compile_lcnf_decls(
            std::slice::from_ref(&decl),
            &env,
            &PipelineConfig::default(),
        ) else {
            continue;
        };
        compiled += 1;
        census.wrappers = art
            .boxed_ir_decls
            .iter()
            .map(|d| {
                let wrapper =
                    crate::mangle::mangle_boxed_name(&crate::mangle::mangle_name(&d.name));
                (wrapper, d.params.iter().map(|(_, t)| t.clone()).collect())
            })
            .collect();
        for d in &art.boxed_ir_decls {
            walk(d, &d.body, &mut census);
        }
    }

    census.refused.sort();
    census.refused.dedup();
    eprintln!(
        "WS6.1 Unbox-USize census: {compiled} constants compiled; enum_tag={} \
         boxed_wrapper={} bounded={:?} refused={}",
        census.enum_tag,
        census.boxed_wrapper,
        census.bounded,
        census.refused.len()
    );
    assert!(
        census.refused.is_empty(),
        "{} `Unbox USize` site(s) are not a constructor tag, a boxed-ABI \
         USize parameter, or a bounded ofNat: each may truncate a Nat >= 2^64 \
         through the low-limb reader. Refuse them in the emitter, never waive: \
         {:?}",
        census.refused.len(),
        &census.refused[..census.refused.len().min(10)]
    );
    // Non-vacuity: the census must still see its population and every class.
    assert!(compiled > 500, "only {compiled} prelude constants compiled");
    assert!(
        census.enum_tag > 50,
        "enum-tag class collapsed ({})",
        census.enum_tag
    );
    assert!(
        census.boxed_wrapper > 10,
        "boxed-wrapper class collapsed ({})",
        census.boxed_wrapper
    );
    // Negative twin: an `Unbox USize` of a plain `Nat` parameter (the shape
    // that WOULD truncate at 2^64) is refused by name, so the classifier is
    // not a blanket pass.
    let truncating = ws6_1_unbox_decl("ws6_1_truncating", IRType::USize);
    let mut twin = Census::default();
    walk(&truncating, &truncating.body, &mut twin);
    assert!(
        twin.refused.len() == 1 && twin.refused[0].starts_with("ws6_1_truncating: "),
        "an Unbox USize of an unbounded Nat must be refused: {:?}",
        twin.refused
    );
    for row in BOUNDED_OFNAT {
        assert!(
            census.bounded.get(*row).copied().unwrap_or(0) > 0,
            "bounded-ofNat row `{row}` no longer observed — a stale row must be \
             removed, not kept: {:?}",
            census.bounded
        );
    }
}

// ---- WS6.1 review: adversarial shapes the implementer's vectors missed ----
//
// The measured bug class (a heap-boxed `Nat` reaching a narrow reader) has
// three producer spellings, and the vectors above reach each only through a
// hand-built C cell. These reach them through the REAL pipeline and through
// widths / limbs the vectors above never touch:
//
// * a `Nat` literal in `[2^32, 2^64)` — typed `UInt64` by `to_ir::lower` and
//   boxed with the `scalar_sz 8` `clean_box_uint64` (the spelling fix (b)
//   deliberately keeps) — fed to `UInt8.ofNat` / `UInt16.ofNat`;
// * a `Nat` literal `>= 2^64` (`NatBig`, a two-limb heap cell with a NONZERO
//   high limb) fed to `UInt8.ofNat` and to `USize.ofNat`;
// * `UInt32.ofNat` over every heap shape (its `clean_unbox_uint32` arm was
//   not touched by WS6.1, so nothing else pins that it dispatches);
// * fix (b) at run time: a small `Nat` literal returned as an object must be
//   the TAGGED immediate, not a heap cell carrying the right value.

/// `(name, value)`: the review's user roots, each `fun (_ : UInt8) => value`
/// so the literal is not hoisted into a nullary constant.
fn ws6_1_review_env() -> clean_kernel::Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::{BinderInfo, Expr as KExpr};
    let mut env = ws6_1_env();
    let of = |f: &str, n: u128| {
        let lit = if n <= u64::MAX as u128 {
            KExpr::nat_lit(n as u64)
        } else {
            // `n = hi * 2^64 + lo` as a kernel Nat expression (the literal
            // itself stays a single `NatBig` after the pipeline folds it).
            KExpr::apps(
                KExpr::const_str("Nat.add"),
                [
                    KExpr::apps(
                        KExpr::const_str("Nat.mul"),
                        [
                            KExpr::nat_lit((n >> 64) as u64),
                            KExpr::apps(
                                KExpr::const_str("Nat.mul"),
                                [KExpr::nat_lit(1u64 << 32), KExpr::nat_lit(1u64 << 32)],
                            ),
                        ],
                    ),
                    KExpr::nat_lit(n as u64),
                ],
            )
        };
        if f.is_empty() {
            lit
        } else {
            KExpr::app(KExpr::const_str(f), lit)
        }
    };
    let roots: [(&str, &str, &str, u128); 5] = [
        ("ws6_1_rv_lit8", "UInt8", "UInt8.ofNat", 5_000_000_007),
        ("ws6_1_rv_lit16", "UInt16", "UInt16.ofNat", 5_000_000_007),
        ("ws6_1_rv_big8", "UInt8", "UInt8.ofNat", (1u128 << 64) + 42),
        ("ws6_1_rv_usz", "USize", "USize.ofNat", (1u128 << 64) + 3),
        ("ws6_1_rv_nat", "Nat", "", 3_000_000_000),
    ];
    for (name, ret, f, n) in roots {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: KExpr::arrow(KExpr::const_str("UInt8"), KExpr::const_str(ret)),
            value: KExpr::lam(BinderInfo::Default, KExpr::const_str("UInt8"), of(f, n)),
            is_reducible: true,
        })
        .unwrap_or_else(|e| panic!("`{name}` kernel-checks against the prelude: {e:?}"));
    }
    env
}

/// The `trustcg_census` shim for `Unit.unit`.
const WS6_1_UNIT_SHIM_C: &str = "clean_obj* l_Unit_unit(void) { return clean_box(0); }\n";

const WS6_1_REVIEW_ROOTS: [&str; 9] = [
    "ws6_1_rv_lit8",
    "ws6_1_rv_lit16",
    "ws6_1_rv_big8",
    "ws6_1_rv_usz",
    "ws6_1_rv_nat",
    "UInt8.ofNat",
    "UInt16.ofNat",
    "UInt32.ofNat",
    "USize.ofNat",
];

/// `(c alias, C prototype tail, decl)` for every entry the driver calls.
const WS6_1_REVIEW_ENTRIES: [(&str, &str, &str, &str); 9] = [
    ("rv_lit8", "uint8_t", "(uint8_t)", "ws6_1_rv_lit8"),
    ("rv_lit16", "uint16_t", "(uint8_t)", "ws6_1_rv_lit16"),
    ("rv_big8", "uint8_t", "(uint8_t)", "ws6_1_rv_big8"),
    ("rv_usz", "size_t", "(uint8_t)", "ws6_1_rv_usz"),
    ("rv_nat", "clean_obj*", "(uint8_t)", "ws6_1_rv_nat"),
    ("rv_u8", "uint8_t", "(clean_obj*)", "UInt8.ofNat"),
    ("rv_u16", "uint16_t", "(clean_obj*)", "UInt16.ofNat"),
    ("rv_u32", "uint32_t", "(clean_obj*)", "UInt32.ofNat"),
    ("rv_uszn", "size_t", "(clean_obj*)", "USize.ofNat"),
];

const WS6_1_REVIEW_MAIN: &str = "int main(void){ \
    uint64_t big = 0x8000000000000005ull, mid = (1ull << 40) + 7; \
    clean_obj* k = rv_nat(0); \
    printf(\"%llu %llu %llu %llu %llu %d %llu %llu %llu %llu %llu %llu %llu %llu\\n\", \
      (unsigned long long)rv_lit8(0), (unsigned long long)rv_lit16(0), \
      (unsigned long long)rv_big8(0), (unsigned long long)rv_usz(0), \
      (unsigned long long)clean_nat_to_u128(k), (int)clean_is_scalar(k), \
      (unsigned long long)rv_u8(clean_nat_big(42, 1)), \
      (unsigned long long)rv_u16(clean_nat_big(0x1234, 5)), \
      (unsigned long long)rv_u32(clean_nat_big(0xDEADBEEF, 7)), \
      (unsigned long long)rv_u32(clean_box_uint64(mid)), \
      (unsigned long long)rv_u32(clean_nat_of_u64(big)), \
      (unsigned long long)rv_uszn(clean_nat_big(3, 1)), \
      (unsigned long long)rv_uszn(clean_nat_of_u64(big)), \
      (unsigned long long)rv_uszn(clean_box(9))); return 0; }\n";

/// The expected values: `5000000007 mod 2^8 = 7`, `mod 2^16 = 61959`,
/// `(2^64+42) mod 2^8 = 42`, `(2^64+3) mod 2^64 = 3`, the literal
/// `3000000000` TAGGED (`1`), then the driver-built heap cells.
const WS6_1_REVIEW_WANT: [u64; 14] = [
    7,
    61959,
    42,
    3,
    3_000_000_000,
    1,
    42,
    0x1234,
    0xDEAD_BEEF,
    7,
    5,
    3,
    0x8000_0000_0000_0005,
    9,
];

/// The review closure at `-O0`, so its `UIntW.ofNat <literal>` roots keep
/// reading a boxed `Nat` (WS6.4 folds them at `-O1`/`-O2`, where the mutation
/// controls below would have no reader to revert).
fn ws6_1_review_artifacts() -> crate::pass_manager::PipelineArtifacts {
    ws6_1_review_artifacts_at(&crate::rc_repair::e2e_support::o0())
}

/// [`ws6_1_review_artifacts`] through an explicit pipeline.
pub(super) fn ws6_1_review_artifacts_at(
    pipeline: &crate::pass_manager::PipelineConfig,
) -> crate::pass_manager::PipelineArtifacts {
    use crate::pass_manager::compile_lcnf_decls;
    let env = ws6_1_review_env();
    // `Unit.unit` is shimmed exactly as `trustcg_census` does: compiled
    // locally, its `Erased` return lowers to a zero-result function that its
    // caller (`System.Platform.numBits`) calls for one result, which the
    // validator refuses (`InstrResultArityMismatch`) — a defect outside WS6.1.
    let mut shimmed = WS6_1_NAT_SHIMMED.to_vec();
    shimmed.push("Unit.unit");
    let decls = ws6_1_closure_shimming(&env, &WS6_1_REVIEW_ROOTS, &shimmed);
    compile_lcnf_decls(&decls, &env, pipeline)
        .expect("the review closure compiles through the real pipeline")
}

fn ws6_1_review_driver(symbol: impl Fn(&str) -> String) -> String {
    let mut s =
        String::from("#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n");
    for (alias, ret, params, decl) in WS6_1_REVIEW_ENTRIES {
        s.push_str(&format!("extern {ret} {alias}{params} {};\n", symbol(decl)));
    }
    s.push_str(WS6_1_REVIEW_MAIN);
    s
}

/// The review's `--emit c` lane: one translation unit; the entries are
/// macros onto the mangled names so the prototypes are not redeclared.
pub(super) fn ws6_1_review_run_c(
    art: &crate::pass_manager::PipelineArtifacts,
    dir: &std::path::Path,
    label: &str,
    arch: &str,
) -> String {
    let c_code = art
        .emit_c(crate::emit_c::CEmitConfig::default())
        .expect("review closure lowers to C");
    let m = |s: &str| crate::mangle::mangle_name(&Name::from_string(s));
    let mut tu = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n{WS6_1_NAT_SHIMS_C}{WS6_1_UNIT_SHIM_C}\n{c_code}\n"
    );
    for (alias, _, _, decl) in WS6_1_REVIEW_ENTRIES {
        tu.push_str(&format!("#define {alias} {}\n", m(decl)));
    }
    tu.push_str(WS6_1_REVIEW_MAIN);
    ws6_1_build_and_run(dir, label, &[("tu.c", tu)], &[], arch)
}

/// The review's trust-ir -> trust-cg lane over `module` (the legacy,
/// license-stripped fixture), returning the driver's stdout.
pub(super) fn ws6_1_review_run_ti(
    module: &Module,
    trust_cg: &std::path::Path,
    dir: &std::path::Path,
    label: &str,
    (target, arch): (&str, &str),
) -> String {
    let p = if cfg!(target_os = "macos") { "_" } else { "" };
    let driver = ws6_1_review_driver(|decl| format!("__asm__(\"{p}{decl}\")"));
    let tmbc = dir.join(format!("{label}.tmbc"));
    let obj = dir.join(format!("{label}.o"));
    write_legacy_native_fixture(module, trust_cg, target, &tmbc);
    let cg = legacy_trust_cg(trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "{label}: trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let rt_extern = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-runtime/src/runtime_extern.c");
    let rt_extern = std::fs::read_to_string(rt_extern).expect("read runtime_extern.c");
    ws6_1_build_and_run(
        dir,
        label,
        &[
            ("driver.c", driver),
            (
                "shims.c",
                format!("#include \"clean_runtime.h\"\n{WS6_1_NAT_SHIMS_C}{WS6_1_UNIT_SHIM_C}"),
            ),
            ("runtime_extern.c", rt_extern),
        ],
        &[&obj],
        arch,
    )
}

/// Review adversarial vectors through `--emit c` AND trust-ir -> trust-cg.
#[test]
fn test_ws6_1_review_literal_and_wide_heap_nat_vectors() {
    let Some(host) = ws6_1_host() else {
        eprintln!("review vectors skipped: unsupported host arch");
        // SELF-SKIP OK: native link/run lanes support only aarch64/x86_64 hosts; other arches skip (printed).
        return;
    };
    let art = ws6_1_review_artifacts();
    let dir = tempfile::tempdir().expect("tempdir");

    let got = ws6_1_review_run_c(&art, dir.path(), "review_c", host.1);
    ws6_1_check("emit_c", &got, &WS6_1_REVIEW_WANT).unwrap_or_else(|e| panic!("{e}"));

    let Some(trust_cg) = find_trust_cg() else {
        eprintln!("review trust-ir lane skipped: trust-cg binary not found");
        // SELF-SKIP OK: trust-cg is an external binary outside this tree; only the trust-ir lane skips (printed), the emit_c lane has already asserted.
        return;
    };
    let module = art
        .emit_trust_ir(&ws6_1_extern_config())
        .expect("review closure lowers to trust-ir");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
    assert_eq!(ws6_1_calls_to(&module, "clean_unbox"), 0);
    let run = |m: &Module, label: &str| ws6_1_review_run_ti(m, &trust_cg, dir.path(), label, host);
    let got = run(&module, "review_ti");
    ws6_1_check("trust-ir", &got, &WS6_1_REVIEW_WANT).unwrap_or_else(|e| panic!("{e}"));

    let vals = |got: &str| -> Vec<String> { got.split_whitespace().map(str::to_string).collect() };

    // Mutation control (a): the tagged-only reader restored in every narrow
    // arm. The literal-cell and wide-heap vectors that go through a narrow
    // `UIntW.ofNat` (0 lit8, 1 lit16, 2 big8, 6 u8 of a nonzero-high-limb
    // Nat, 7 u16 of one) must all go WRONG, so they are not vacuous.
    let mut reverted = module.clone();
    assert!(ws6_1_revert_narrow_readers(&mut reverted) > 0);
    let got = vals(&run(&reverted, "review_ti_rev_a"));
    assert_eq!(got.len(), WS6_1_REVIEW_WANT.len(), "reverted (a): {got:?}");
    for i in [0, 1, 2, 6, 7] {
        assert_ne!(
            got[i],
            WS6_1_REVIEW_WANT[i].to_string(),
            "reverted (a): vector {i} must be wrong under the tagged-only reader: {got:?}"
        );
    }

    // Mutation control (b): `ws6_1_rv_nat`'s `USize` box re-pointed at the
    // pre-WS6.1 always-heap `clean_box_uint64` (same `(u64) -> ptr`
    // signature). The VALUE survives (every Nat reader dispatches), but the
    // spelling is no longer the tagged immediate: vector 5 catches exactly
    // that, and vector 4 shows it is the spelling, not the value, that moved.
    let mut reverted = module.clone();
    let nat_of_u64 = ws6_1_runtime_fn(&reverted, "clean_nat_of_u64");
    let box_u64 = ws6_1_runtime_fn(&reverted, "clean_box_uint64");
    let mut repointed = 0;
    // The literal may be hoisted into `ws6_1_rv_nat._boxed_const_N`.
    for f in reverted
        .functions
        .iter_mut()
        .filter(|f| f.name.starts_with("ws6_1_rv_nat"))
    {
        for node in f.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
            if let trust_ir::inst::Inst::Call { callee, .. } = &mut node.inst {
                if *callee == nat_of_u64 {
                    *callee = box_u64;
                    repointed += 1;
                }
            }
        }
    }
    assert_eq!(
        repointed,
        1,
        "`ws6_1_rv_nat` must box its literal exactly once (names: {:?})",
        module
            .functions
            .iter()
            .filter(|f| f.name.starts_with("ws6_1_rv_nat"))
            .map(|f| f.name.clone())
            .collect::<Vec<_>>()
    );
    let got = vals(&run(&reverted, "review_ti_rev_b"));
    assert_eq!(
        got[4],
        WS6_1_REVIEW_WANT[4].to_string(),
        "reverted (b): {got:?}"
    );
    assert_eq!(
        got[5], "0",
        "reverted (b): the heap spelling must be observed as NOT tagged: {got:?}"
    );
}

/// Review finding (fix (b)'s C twin): a `USize` at or above 2^63 must survive
/// a `Box USize` in BOTH backends. The boxed-ABI wrapper of `USize.ofNat`
/// unboxes its `Nat` argument and re-boxes the `USize` result, so feeding it
/// `2^63 + 5` must hand back a heap `Nat` of value `2^63 + 5`, while a small
/// value must come back as the tagged immediate. Before the review the C
/// backend boxed a `USize` with the tagged `clean_box`, which drops bit 63
/// (it returned the TAGGED `5`); the trust-ir backend is correct since fix
/// (b). Mutation control: the pre-review C spelling is restored in the
/// emitted C and must reproduce the truncation.
#[test]
fn test_ws6_1_review_usize_box_keeps_bit_63_in_both_backends() {
    let Some(host) = ws6_1_host() else {
        eprintln!("USize box vectors skipped: unsupported host arch");
        // SELF-SKIP OK: native link/run lanes support only aarch64/x86_64 hosts; other arches skip (printed).
        return;
    };
    const MAIN: &str = "int main(void){ \
        clean_obj* big = rv_uszb(clean_nat_of_u64(0x8000000000000005ull)); \
        clean_obj* small = rv_uszb(clean_box(9)); \
        printf(\"%llu %d %llu %d\\n\", \
          (unsigned long long)clean_nat_to_u128(big), (int)clean_is_scalar(big), \
          (unsigned long long)clean_nat_to_u128(small), (int)clean_is_scalar(small)); \
        return 0; }\n";
    const WANT: [u64; 4] = [0x8000_0000_0000_0005, 0, 9, 1];
    // `-O1`, as when this test landed: the boxed `USize.ofNat` wrapper is an
    // `-O1` artifact, and WS6.4's resolution never touches `USize`.
    let art = ws6_1_review_artifacts_at(&crate::pass_manager::PipelineConfig::default());
    let dir = tempfile::tempdir().expect("tempdir");

    // --emit c: the boxed wrapper is `mangle_boxed_name(mangle_name(..))`.
    let wrapper =
        crate::mangle::mangle_name(&Name::from_string(&crate::mangle::mangle_boxed_name(
            &crate::mangle::mangle_name(&Name::from_string("USize.ofNat")),
        )));
    let c_code = art
        .emit_c(crate::emit_c::CEmitConfig::default())
        .expect("review closure lowers to C");
    assert!(
        c_code.contains(&format!("clean_obj* {wrapper}(clean_obj* _x0) {{")),
        "the C output must define the boxed wrapper `{wrapper}`"
    );
    let tu = |code: &str| {
        format!(
            "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
             {WS6_1_NAT_SHIMS_C}{WS6_1_UNIT_SHIM_C}\n{code}\n#define rv_uszb {wrapper}\n{MAIN}"
        )
    };
    let got = ws6_1_build_and_run(dir.path(), "uszb_c", &[("tu.c", tu(&c_code))], &[], host.1);
    ws6_1_check("emit_c", &got, &WANT).unwrap_or_else(|e| panic!("{e}"));
    let reverted = c_code.replace("clean_nat_of_u64((uint64_t)", "clean_box((size_t)");
    assert_ne!(
        reverted, c_code,
        "the C mutation must change the emitted code"
    );
    let got = ws6_1_build_and_run(
        dir.path(),
        "uszb_c_rev",
        &[("tu.c", tu(&reverted))],
        &[],
        host.1,
    );
    assert!(
        ws6_1_check("emit_c (reverted)", &got, &WANT).is_err(),
        "the tagged `clean_box` spelling must reproduce the bit-63 truncation: `{got}`"
    );

    let Some(trust_cg) = find_trust_cg() else {
        eprintln!("USize box trust-ir lane skipped: trust-cg binary not found");
        // SELF-SKIP OK: trust-cg is an external binary outside this tree; only the trust-ir lane skips (printed), the emit_c lane has already asserted.
        return;
    };
    let module = art
        .emit_trust_ir(&ws6_1_extern_config())
        .expect("review closure lowers to trust-ir");
    let boxed = module
        .functions
        .iter()
        .find(|f| {
            f.name.contains("USize_ofNat") && f.name.contains("boxed") && !f.blocks.is_empty()
        })
        .map(|f| f.name.clone())
        .expect("the trust-ir module must define USize.ofNat's boxed wrapper");
    let tmbc = dir.path().join("uszb_ti.tmbc");
    let obj = dir.path().join("uszb_ti.o");
    write_legacy_native_fixture(&module, &trust_cg, host.0, &tmbc);
    let cg = legacy_trust_cg(&trust_cg)
        .args(["-c", "--target", host.0, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let p = if cfg!(target_os = "macos") { "_" } else { "" };
    let driver = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
         extern clean_obj* rv_uszb(clean_obj*) __asm__(\"{p}{boxed}\");\n{MAIN}"
    );
    let rt_extern = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-runtime/src/runtime_extern.c");
    let rt_extern = std::fs::read_to_string(rt_extern).expect("read runtime_extern.c");
    let got = ws6_1_build_and_run(
        dir.path(),
        "uszb_ti",
        &[
            ("driver.c", driver),
            (
                "shims.c",
                format!("#include \"clean_runtime.h\"\n{WS6_1_NAT_SHIMS_C}{WS6_1_UNIT_SHIM_C}"),
            ),
            ("runtime_extern.c", rt_extern),
        ],
        &[&obj],
        host.1,
    );
    ws6_1_check("trust-ir", &got, &WANT).unwrap_or_else(|e| panic!("{e}"));
}

// WS6.3 (F-105): the `mask` crash — Nat/UInt bitwise ops get executable
// implementations.
#[path = "emit_trust_ir_ws6_3_tests.rs"]
mod ws6_3;

// WS6.4: known-instance class methods resolve before boxing.
#[path = "emit_trust_ir_ws6_4_tests.rs"]
mod ws6_4;

// WS5.12 (F-097, the `let` half): the p03 `a.lean.let.{emit,carried,exec}`
// GAP rows ported on the Clean producer's own pipeline, plus the
// non-wrapping-op negative twin.
#[path = "emit_trust_ir_ws5_12_tests.rs"]
mod ws5_12;

/// WS6.2, the proof-program ratchet row `GENERAL.p03_let.sqLet.linkrun`
/// (PRODUCER-GAP → PASS): `sqLet` and `twiceApply` from real Clean source,
/// through the `-O0` pipeline, lowered to trust-ir, compiled by trust-cg,
/// linked with the Clean runtime and executed. Before the post-boxing RC
/// repair the emitted body passed one owned boxed `t` twice to the consuming
/// `l_HMul_hMul` with no `retain`, and the executable died (run-rc=-5, SIGBUS
/// class). The expected values are the kernel-certified ones
/// (`sqLet a = (a + 1)^2 mod 2^64`); the off-by-one twin is rejected.
///
/// trust-cg refuses `body_gate: ungated` bodies; like the other native e2e
/// tests this checks that refusal first and then compiles a copy whose
/// Ungated bodies are explicitly licensed as unvalidated. Existing
/// certificates and their `clean-kernel-tv` claims remain and must replay;
/// no certificate or `Gated` authority is fabricated.
#[test]
fn test_emit_trust_ir_e2e_general_p03_let_sqlet_linkrun() {
    ws6_2_sqlet_linkrun(&crate::rc_repair::e2e_support::o0(), "ws62_sqlet", false);
}

/// The body of [`test_emit_trust_ir_e2e_general_p03_let_sqlet_linkrun`]
/// through an explicit pipeline (WS6.4 re-runs it at `-O1`/`-O2`, where the
/// known instances resolve and `sqLet` is native scalar arithmetic).
pub(super) fn ws6_2_sqlet_linkrun(
    pipeline: &crate::pass_manager::PipelineConfig,
    module_name: &str,
    expect_certified_sqlet: bool,
) {
    use crate::emit_trust_ir::{RuntimeLowering, TrustIrConfig};
    use crate::pass_manager::compile_lcnf_to_trust_ir;
    use crate::rc_repair::e2e_support::{
        closure_decls, elaborated_env, off_by_one, trust_cg_driver, EXPECTED, SHIMS_C,
    };

    let env = elaborated_env();
    let decls = closure_decls(&env, pipeline);
    let config = TrustIrConfig {
        module_name: module_name.to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    };
    let module = compile_lcnf_to_trust_ir(&decls, &env, pipeline, &config)
        .expect("the repaired closure lowers to trust-ir");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
    let sqlet = module
        .functions
        .iter()
        .find(|function| function.name == "sqLet")
        .expect("the native fixture emits sqLet");
    assert_eq!(
        matches!(
            &sqlet.body_gate,
            Some(BodyGate::Gated { authority, .. })
                if authority == crate::emit_trust_ir_tv::CLEAN_KERNEL_TV_AUTHORITY
        ),
        expect_certified_sqlet,
        "the fixture's expected sqLet certification must hold before consumer discovery"
    );
    let (target, arch) = match std::env::consts::ARCH {
        "aarch64" => ("aarch64", "arm64"),
        "x86_64" => ("x86_64", "x86_64"),
        other => panic!("unsupported host arch for the trust-cg linkrun: {other}"),
    };
    let trust_cg = match find_trust_cg() {
        Some(p) => p,
        None => {
            // The compile-side half above already asserted the repaired,
            // validated module; only the native half needs a consumer.
            assert!(errors.is_empty());
            eprintln!(
                "GENERAL.p03_let.sqLet.linkrun: trust-cg not found (set CLEAN_TRUST_CG_BIN); \
                 native half not run"
            );
            return;
        }
    };

    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::create_dir_all(dir.path().join("include")).expect("include dir");
    std::fs::create_dir_all(dir.path().join("src")).expect("src dir");
    std::fs::write(
        dir.path().join("include/clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("write header");
    std::fs::write(
        dir.path().join("src/clean_runtime.c"),
        clean_runtime::runtime_source(),
    )
    .expect("write runtime");
    std::fs::write(
        dir.path().join("src/runtime_extern.c"),
        clean_runtime::runtime_extern_source(),
    )
    .expect("write runtime_extern");
    std::fs::write(
        dir.path().join("src/driver.c"),
        format!(
            "#include <stdio.h>\n#include \"../include/clean_runtime.h\"\n{SHIMS_C}\n{}",
            trust_cg_driver()
        ),
    )
    .expect("write driver");

    // The production module is refused by the codegen license ...
    let ungated = dir.path().join("ungated.tmbc");
    std::fs::write(&ungated, tmbc_envelope(&module)).expect("write ungated tmbc");
    let refused = std::process::Command::new(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(dir.path().join("refused.o"))
        .arg(&ungated)
        .output()
        .expect("spawn trust-cg");
    assert!(
        !refused.status.success()
            && String::from_utf8_lossy(&refused.stderr).contains("affirmatively ungated"),
        "an ungated producer module must be refused before codegen: {}",
        String::from_utf8_lossy(&refused.stderr)
    );
    // ... so the native oracle compiles a copy licensed at the
    // `clean-compiler-unvalidated` grade (see `write_legacy_native_fixture`).
    // The module's TV obligations and certificates stay: `sqLet` keeps its
    // `clean-kernel-tv` claim, which trust-cg accepts only beside the evidence
    // it names, exactly as the production lane leaves it.
    let mut legacy = module.clone();
    crate::emit_trust_ir_lane::restamp_ungated_as_unvalidated(&mut legacy)
        .expect("every body of the sqlet module carries a claim");
    let validation = trust_ir_build::validate_module_report(&legacy);
    assert!(
        validation.is_ok(),
        "the current pinned validator must replay the restamped module: {:?}",
        validation.errors()
    );
    let replayed = validation
        .replayed_certificate_refs()
        .expect("a successful validation report exposes its exact replayed certificates");
    for certified in module.functions.iter().filter(|function| {
        matches!(
            &function.body_gate,
            Some(BodyGate::Gated { authority, .. })
                if authority == crate::emit_trust_ir_tv::CLEAN_KERNEL_TV_AUTHORITY
        )
    }) {
        let restamped = legacy
            .functions
            .iter()
            .find(|function| function.id == certified.id)
            .expect("restamping preserves every certified function");
        assert_eq!(restamped.body_gate, certified.body_gate);
        assert_eq!(
            legacy.function_body_digest(certified.id),
            module.function_body_digest(certified.id),
            "restamping cannot alter the body bound to a kernel certificate"
        );
        let Some(BodyGate::Gated {
            evidence: Some(evidence),
            ..
        }) = &restamped.body_gate
        else {
            panic!("a retained clean-kernel-tv claim must name its evidence");
        };
        assert!(
            legacy.proof_certificates.iter().any(|certificate| {
                certificate.obligation == evidence.obligation
                    && replayed.contains(&certificate.lineage_ref())
            }),
            "the current pinned validator must replay the exact certificate for {}",
            certified.name
        );
    }
    let tmbc = dir.path().join("sqlet.tmbc");
    std::fs::write(&tmbc, tmbc_envelope(&legacy)).expect("write legacy tmbc");
    let obj = dir.path().join("sqlet.o");
    let cg = legacy_trust_cg(&trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    if !cg.status.success() {
        let retained = dir.keep();
        panic!(
            "trust-cg {} -c: {}\nretained sqlet input and runtime sources at {}",
            trust_cg.display(),
            String::from_utf8_lossy(&cg.stderr),
            retained.display()
        );
    }
    let mut objects = vec![obj];
    for c_file in ["clean_runtime", "runtime_extern", "driver"] {
        let o = dir.path().join(format!("{c_file}.o"));
        let out = std::process::Command::new("cc")
            .args(["-c", "-O0", "-std=c11", "-w"])
            .arg(dir.path().join(format!("src/{c_file}.c")))
            .arg("-o")
            .arg(&o)
            .output()
            .expect("spawn cc");
        assert!(
            out.status.success(),
            "cc {c_file}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        objects.push(o);
    }
    let bin = dir.path().join("sqlet");
    let mut link = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut link, arch);
    let linked = link
        .arg("-o")
        .arg(&bin)
        .args(&objects)
        .arg("-lm")
        .output()
        .expect("spawn cc link");
    assert!(
        linked.status.success(),
        "link: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let run = std::process::Command::new(&bin)
        .output()
        .expect("run sqlet");
    assert!(
        run.status.success(),
        "the trust-cg-built program crashed: {:?}\nstdout:\n{}\nstderr:\n{}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let lines: Vec<String> = String::from_utf8_lossy(&run.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    assert_eq!(
        lines, EXPECTED,
        "wrong values from the trust-cg-built program"
    );
    assert_ne!(lines, off_by_one(), "the off-by-one twin must be rejected");
}

// --- WS6.10: fixed-width width conversions lower to ONE native cast ---

/// `fn <name>(a: <src>) -> <dst> := <conv> a` — a saturated call to a width
/// conversion, the shape LCNF gives `def widen (a : UInt8) : UInt64 :=
/// a.toUInt64`.
fn ws6_10_conversion_root(name: &str, conv: &str, src: IRType, dst: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string(name),
        params: vec![(VarId(0), src)],
        return_type: dst.clone(),
        body: IRBody::VDecl {
            var: VarId(1),
            ty: dst,
            value: IRExpr::Apply {
                fn_id: FnId(Name::from_string(conv)),
                args: vec![IRArg::Var(VarId(0))],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

/// The conversion's compiled-from-source decl as the pipeline carries it into
/// the slice — with a DIVERGENT body (returns a constant 7), so its survival
/// into the module, or a call to it, would be visible.
fn ws6_10_divergent_conversion(conv: &str, src: IRType, dst: IRType) -> IRDecl {
    IRDecl {
        name: Name::from_string(conv),
        params: vec![(VarId(0), src)],
        return_type: dst.clone(),
        body: IRBody::VDecl {
            var: VarId(1),
            ty: dst,
            value: IRExpr::Lit(IRLiteral::UInt64(7)),
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    }
}

fn ws6_10_insts<'m>(module: &'m Module, name: &str) -> Vec<&'m trust_ir::inst::Inst> {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("`{name}` must be emitted"))
        .instructions()
        .map(|n| &n.inst)
        .collect()
}

/// Port of the proof-program row `GENERAL.p12b_width_conversion.widen.emit`,
/// emitter half: `widen` is ONE `zext u8 → u64` and a narrowing conversion is
/// ONE `trunc u16 → u8` — native casts, no call, and the conversion's
/// compiled-from-source body (in-slice, here divergent) is SKIPPED, so no
/// call site can reach it. The module validates.
#[test]
fn ws6_10_saturated_width_conversions_lower_to_native_casts() {
    use trust_ir::inst::{CastOp, Inst};
    use trust_ir::ty::Ty;

    let decls = [
        ws6_10_divergent_conversion("UInt8.toUInt64", IRType::UInt8, IRType::UInt64),
        ws6_10_conversion_root("widen", "UInt8.toUInt64", IRType::UInt8, IRType::UInt64),
        ws6_10_conversion_root("narrow", "UInt16.toUInt8", IRType::UInt16, IRType::UInt8),
    ];
    let module = emit_trust_ir(&decls).expect("width conversions lower natively");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validation errors: {errors:?}");
    assert!(
        module.functions.iter().all(|f| f.name != "UInt8.toUInt64"),
        "the conversion's compiled body must be skipped when only called"
    );
    for (name, op, src, dst) in [
        ("widen", CastOp::ZExt, Ty::U8, Ty::U64),
        ("narrow", CastOp::Trunc, Ty::U16, Ty::U8),
    ] {
        let insts = ws6_10_insts(&module, name);
        let casts: Vec<_> = insts
            .iter()
            .filter(|i| matches!(i, Inst::Cast { .. }))
            .collect();
        assert!(
            matches!(
                casts.as_slice(),
                [Inst::Cast { op: o, src_ty: s, dst_ty: d, .. }] if *o == op && *s == src && *d == dst
            ),
            "`{name}` must be exactly one {op:?} {src:?} -> {dst:?}, got: {insts:?}"
        );
        assert!(
            !insts.iter().any(|i| matches!(i, Inst::Call { .. })),
            "`{name}` must not call the conversion, got: {insts:?}"
        );
    }
}

/// A conversion referenced as a function VALUE has no synthesized boxed
/// wrapper, so it KEEPS its compiled body, and a saturated call beside the
/// value reference calls that same body (one consistent callee, never an
/// undefined symbol). The module validates.
#[test]
fn ws6_10_value_referenced_conversion_keeps_its_body() {
    use trust_ir::inst::Inst;

    let conv = IRDecl {
        name: Name::from_string("UInt32.toUInt64"),
        params: vec![(VarId(0), IRType::Object)],
        return_type: IRType::Object,
        body: IRBody::Ret(IRArg::Var(VarId(0))),
    };
    let closure = IRDecl {
        name: Name::from_string("as_value"),
        params: vec![],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(Name::from_string("UInt32.toUInt64")),
                arity: 1,
                args: vec![],
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let caller = ws6_10_conversion_root("call", "UInt32.toUInt64", IRType::Object, IRType::Object);
    let module = emit_trust_ir_with_config(&[conv, closure, caller], &c1_config())
        .expect("a value-referenced conversion lowers over its own body");
    assert!(validate_module(&module).is_empty(), "module must validate");
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "UInt32.toUInt64" && !f.blocks.is_empty()),
        "the value-referenced conversion must keep its compiled body"
    );
    let insts = ws6_10_insts(&module, "call");
    assert!(
        insts.iter().any(|i| matches!(i, Inst::Call { .. }))
            && !insts.iter().any(|i| matches!(i, Inst::Cast { .. })),
        "a call beside the value reference must call the kept body: {insts:?}"
    );
}

/// Negative twins: the cast arm refuses, by name, (a) a declared result type
/// that disagrees with the conversion's target, and (b) an operand that is
/// not the source scalar (a boxed `Object`) — never coerced into a cast.
#[test]
fn ws6_10_width_conversion_type_mismatches_are_refused() {
    let bad_result = ws6_10_conversion_root(
        "bad_result",
        "UInt8.toUInt64",
        IRType::UInt8,
        IRType::UInt32,
    );
    let err = emit_trust_ir(&[bad_result]).expect_err("result mismatch must be refused");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m)
            if m.contains("width conversion UInt8.toUInt64 produces U64")),
        "got: {err:?}"
    );

    let boxed_operand = ws6_10_conversion_root(
        "boxed_operand",
        "UInt8.toUInt64",
        IRType::Object,
        IRType::UInt64,
    );
    let err = emit_trust_ir(&[boxed_operand]).expect_err("boxed operand must be refused");
    assert!(
        matches!(&err, TrustIrError::Unsupported(m)
            if m.contains("width conversion UInt8.toUInt64 takes a U8 operand")),
        "got: {err:?}"
    );
}

/// Mutation control over the table: exactly the twelve fixed-width pairs,
/// `ZExt` iff the target is wider. `USize`, same-width, `Nat` and malformed
/// names are NOT casts (fail through to the ordinary call path).
#[test]
fn ws6_10_uint_conversion_cast_table_boundaries() {
    use trust_ir::inst::CastOp;
    use trust_ir::ty::Ty;

    let widths = [
        ("UInt8", 8, Ty::U8),
        ("UInt16", 16, Ty::U16),
        ("UInt32", 32, Ty::U32),
        ("UInt64", 64, Ty::U64),
    ];
    let mut n = 0;
    for (s, sw, st) in &widths {
        for (d, dw, dt) in &widths {
            let got = uint_conversion_cast(&format!("{s}.to{d}"));
            if sw == dw {
                assert_eq!(got, None, "{s}.to{d} is not a cast");
                continue;
            }
            let op = if dw > sw { CastOp::ZExt } else { CastOp::Trunc };
            assert_eq!(got, Some((op, st.clone(), dt.clone())), "{s}.to{d}");
            n += 1;
        }
    }
    assert_eq!(n, 12);
    for name in [
        "UInt8.toUSize",
        "USize.toUInt64",
        "UInt64.toNat",
        "Nat.toUInt8",
        "UInt8.ofNat",
        "UInt8.toUInt128",
        "UInt8.add",
        "toUInt8",
    ] {
        assert_eq!(
            uint_conversion_cast(name),
            None,
            "{name} must not be a cast"
        );
    }
}
