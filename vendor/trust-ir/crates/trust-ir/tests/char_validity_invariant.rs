// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS2.17 (F-037): the `Char` VALIDITY INVARIANT — the dynamic half of
// lowering-target subset v4's structural condition 6.
//
// `Ty::Char` is a 32-bit carrier whose inhabitants are the Unicode SCALAR
// VALUES (`0..=0x10FFFF` minus the surrogate block `0xD800..=0xDFFF`), so
// admitting the type into the proven subset is sound only while every
// ORIGIN of a `Char` re-establishes that invariant. The subset's condition 6
// is the static half (a conforming producer may only make one with a
// range-validated `Const` or `zext u8 -> char`); this file pins the dynamic
// half, which runs on EVERY module the reference interpreter executes,
// in subset or not: an invalid `Char` bound to an SSA name is UNDEFINED
// BEHAVIOUR, never a silently-carried integer.
//
// The Lean mirror is `validChar` (`lean/trust_ir-semantics/TrustIr/Basic.lean`)
// with `validChar_of_lt_256`, `not_validChar_surrogate` and
// `not_validChar_above_max`; the subset-classifier half is
// `subset_v4_char_origin_condition` (`crates/trust-ir/src/bridge.rs`).

use trust_ir::inst::{CastOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Constant, FuncTy, Function, Module, Ty};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

/// `fn() -> char { trunc(<raw>: u32) }`.
///
/// `Cast Trunc U32 -> Char` is the deliberately out-of-subset origin
/// (condition 6 refuses it) that a HOSTILE or non-conforming producer can
/// still spell, which is exactly why the interpreter must have its own
/// check: the validator's `Const` range rule never sees this value.
fn truncated_char_module(raw: u32) -> Module {
    let mut module = Module::new("char_from_u32");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Char],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "char_from_u32", ft, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(i128::from(raw)),
        })
        .with_result(v(0)),
    );
    blk.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U32,
            dst_ty: Ty::Char,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn run(module: &Module) -> Result<Vec<InterpretValue>, trust_ir::interpret::InterpretError> {
    Interpreter::with_module(module)
        .execute_func(FuncId::new(0), Vec::new())
        .map(|out| out.returns)
}

/// POSITIVE: every Unicode scalar value executes and comes back unchanged,
/// including both edges of the surrogate gap and the last code point.
#[test]
fn a_unicode_scalar_value_executes() {
    for raw in [0u32, 0x41, 0xD7FF, 0xE000, 0xFFFD, 0x10FFFF] {
        let returns = run(&truncated_char_module(raw))
            .unwrap_or_else(|e| panic!("char {raw:#x} must execute: {e}"));
        assert_eq!(
            returns[0]
                .as_int()
                .expect("char is an integer")
                .as_unsigned(),
            u128::from(raw),
            "char {raw:#x} round trip"
        );
    }
}

/// NEGATIVE TWIN, one mutation from `0xD7FF` above: the first surrogate is
/// not a Unicode scalar value, so binding it to a `Char` is UB — by the
/// NAMED code, not merely "some error".
#[test]
fn a_surrogate_char_is_undefined_behaviour() {
    let Err(err) = run(&truncated_char_module(0xD800)) else {
        panic!("0xD800 is a surrogate and must be refused")
    };
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(
        err.to_string().contains("not a Unicode scalar value"),
        "wrong reason: {err}"
    );
}

/// NEGATIVE TWIN on the other edge, one mutation from `0x10FFFF`: one past
/// the last code point.
#[test]
fn a_char_above_the_last_code_point_is_undefined_behaviour() {
    for raw in [0xDFFFu32, 0x110000, 0xFFFF_FFFF] {
        let Err(err) = run(&truncated_char_module(raw)) else {
            panic!("{raw:#x} is not a Unicode scalar value and must be refused")
        };
        assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
        assert!(
            err.to_string().contains("not a Unicode scalar value"),
            "wrong reason for {raw:#x}: {err}"
        );
    }
}

/// MUTATION CONTROL: the check is keyed on the declared type `Char`, not on
/// the VALUE. The identical bit pattern at `U32` — the carrier, spelled
/// honestly — executes, so the new rule refuses the type and does not
/// over-refuse arithmetic.
#[test]
fn the_same_bit_pattern_at_u32_is_not_refused() {
    let mut module = Module::new("u32_surrogate");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "u32_surrogate", ft, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0));
    blk.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(0xD800),
        })
        .with_result(v(0)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let returns = run(&module).expect("0xD800 is an ordinary u32");
    assert_eq!(
        returns[0].as_int().expect("integer").as_unsigned(),
        0xD800,
        "u32 arithmetic must be untouched by the char invariant"
    );
}

/// MUTATION CONTROL: the ONE admitted computed origin (subset v4 condition
/// 6) can never produce an invalid `Char`, over the EXHAUSTIVE `u8` domain —
/// the executable counterpart of the Lean theorem `validChar_of_lt_256`.
#[test]
fn zext_u8_to_char_is_valid_for_every_byte() {
    let mut module = Module::new("char_from_u8");
    let ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::U8],
            returns: vec![Ty::Char],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "char_from_u8", ft, BlockId::new(0));
    let mut blk = Block::new(BlockId::new(0)).with_param(v(0), Ty::U8);
    blk.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::Char,
            operand: v(0),
        })
        .with_result(v(1)),
    );
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    for byte in 0u32..=0xFF {
        let arg = InterpretValue::int(Ty::U8, i128::from(byte)).expect("in range");
        let returns = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), vec![arg])
            .unwrap_or_else(|e| panic!("zext u8 {byte:#x} -> char must execute: {e}"))
            .returns;
        assert_eq!(
            returns[0].as_int().expect("char").as_unsigned(),
            u128::from(byte)
        );
    }
}

// Entry transport is checked against its declared by-value Char reach, not
// against arbitrary stored child tags supplied by the embedder.
fn entry_transport_module(ty: Ty) -> Module {
    let mut module = Module::new("entry_char_transport");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("signature");
    let mut function = Function::new(FuncId::new(0), "entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0)).with_param(v(0), ty);
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module.try_add_function(function).expect("entry");
    module
}

#[test]
fn undeclared_char_payloads_are_type_errors_even_when_the_surrogate_is_cold() {
    use trust_ir::interpret::InterpretValueKind;
    for raw in [0x41, 0xD800, 0x110000] {
        for ty in [Ty::Ptr, Ty::Tuple(vec![Ty::U64])] {
            let module = entry_transport_module(ty.clone());
            assert!(!module.type_contains_char_by_value(&ty));
            let input = InterpretValue {
                ty,
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::Char, raw).expect("carrier"),
                ]),
            };
            let error = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), vec![input])
                .expect_err("undeclared Char");
            assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");
            assert!(error.message.contains("not declared"), "{error}");
        }
    }
}

#[test]
fn root_char_cannot_borrow_a_char_free_signature() {
    let module = entry_transport_module(Ty::U64);
    let input = InterpretValue::int(Ty::Char, 0xD800).expect("carrier");
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), vec![input])
        .expect_err("wrong formal");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");
}

#[test]
fn declared_nested_char_preserves_unicode_ub_and_valid_scalar_execution() {
    use trust_ir::interpret::InterpretValueKind;
    let ty = Ty::Tuple(vec![Ty::Char]);
    let module = entry_transport_module(ty.clone());
    assert!(module.type_contains_char_by_value(&ty));
    for raw in [0x41, 0xD800, 0x110000] {
        let input = InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::Char, raw).expect("carrier"),
            ]),
        };
        let result = Interpreter::with_module(&module).execute_func(FuncId::new(0), vec![input]);
        if raw == 0x41 {
            assert!(result.is_ok(), "{result:?}");
        } else {
            assert_eq!(
                result.expect_err("invalid Unicode").code,
                InterpretErrorCode::UndefinedBehavior
            );
        }
    }
}

#[test]
fn char_entry_permission_does_not_preempt_malformed_integer_carrier_checks() {
    use trust_ir::interpret::{InterpretInt, InterpretValueKind};
    let module = entry_transport_module(Ty::Tuple(vec![Ty::Char]));
    let input = InterpretValue {
        ty: Ty::Tuple(vec![Ty::Char]),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue {
            ty: Ty::Char,
            kind: InterpretValueKind::Int(InterpretInt {
                bits: 64,
                signed: false,
                raw: 0xD800,
            }),
        }]),
    };
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), vec![input])
        .expect_err("malformed carrier");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");
    assert!(error.message.contains("malformed"), "{error}");
}

#[test]
fn variadic_declaration_tail_retains_dynamic_unicode_checks_before_host() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use trust_ir::interpret::{HostCalls, HostState, InterpretResult};
    struct TailHost(AtomicUsize);
    impl HostCalls for TailHost {
        fn call(
            &self,
            _: &Function,
            _: &FuncTy,
            _: &[InterpretValue],
            _: &mut HostState,
        ) -> Option<InterpretResult<Vec<InterpretValue>>> {
            self.0.fetch_add(1, Ordering::SeqCst);
            Some(Ok(vec![]))
        }
    }
    let mut module = entry_transport_module(Ty::U64);
    module.functions[0].blocks.clear();
    module.func_types[0].is_vararg = true;
    let host = TailHost(AtomicUsize::new(0));
    for raw in [0x41, 0xD800, 0x110000] {
        let before = host.0.load(Ordering::SeqCst);
        let result = Interpreter::with_module(&module)
            .with_host(&host)
            .execute_func(
                FuncId::new(0),
                vec![
                    InterpretValue::int(Ty::U64, 0).expect("fixed"),
                    InterpretValue::int(Ty::Char, raw).expect("tail"),
                ],
            );
        if raw == 0x41 {
            assert!(result.is_ok(), "{result:?}");
            assert_eq!(host.0.load(Ordering::SeqCst), before + 1);
        } else {
            assert_eq!(
                result.expect_err("invalid Unicode").code,
                InterpretErrorCode::UndefinedBehavior
            );
            assert_eq!(host.0.load(Ordering::SeqCst), before);
        }
    }
}
