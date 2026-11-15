// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Crystal lane (E3b): `Constant::Uninit`, an UNWRITTEN struct/tuple lane, in the reference
//! interpreter. Every test builds the flat-enum shape the Trust bridge emits for
//! `Option<u64>::None` -- `{ isize tag, u64 payload }` with only the tag written -- and pins one
//! rule of the lane's semantics: writing replaces it, reading it is undefined behaviour, the
//! aggregate moves whole, a store leaves the lane's bytes uninitialised and a whole reload gives
//! it back, and it may stand nowhere but a direct lane of a struct/tuple constant. The last test
//! pins the other half of the design: uninitialised bytes that no unwritten lane left keep the
//! strict aggregate-load discipline, so a program without `Constant::Uninit` runs as before.

use super::*;
use crate::ty::{FieldDef, FuncTy, StructDef};
use crate::value::StructId;
use crate::{Block, Function, Module};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn result(inst: Inst, value: ValueId) -> InstrNode {
    InstrNode::new(inst).with_result(value)
}

fn void(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

/// `Option<u64>` as the bridge lays it out on the sidecar lane: `{ isize, u64 }`.
fn opt_ty() -> Ty {
    Ty::Struct(StructId::new(0))
}

/// A one-function module over `opt_ty()` whose body is `body` followed by `ret results`.
fn run(
    body: Vec<InstrNode>,
    returns: Vec<Ty>,
    results: Vec<ValueId>,
) -> InterpretResult<InterpretOutcome> {
    let mut module = Module::new("uninit-lane-test");
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "core::option::Option".to_string(),
        fields: vec![
            FieldDef {
                name: "tag".to_string(),
                ty: Ty::Isize,
                offset: None,
            },
            FieldDef {
                name: "payload".to_string(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let ft = module
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "uninit_lane", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.extend(body);
    block.body.push(void(Inst::Return { values: results }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    Interpreter::with_module(&module).execute_func(FuncId::new(0), [])
}

/// `%0 = const S { uninit, uninit }; %1 = const isize 0; %2 = insertfield S %0, 0, %1` --
/// the lane-on bridge's spelling of `None`.
fn none_value() -> Vec<InstrNode> {
    vec![
        result(
            Inst::Const {
                ty: opt_ty(),
                value: Constant::Aggregate(vec![Constant::Uninit, Constant::Uninit]),
            },
            v(0),
        ),
        result(
            Inst::Const {
                ty: Ty::Isize,
                value: Constant::Int(0),
            },
            v(1),
        ),
        result(
            Inst::InsertField {
                ty: opt_ty(),
                aggregate: v(0),
                field: 0,
                value: v(1),
            },
            v(2),
        ),
    ]
}

fn unwritten(ty: Ty) -> InterpretValue {
    InterpretValue {
        ty,
        kind: InterpretValueKind::Uninit,
    }
}

fn isize_value(n: i128) -> InterpretValue {
    InterpretValue::int(Ty::Isize, n).expect("isize")
}

#[test]
fn a_partial_write_returns_exactly_the_written_lane_and_an_unwritten_one() {
    let outcome = run(none_value(), vec![opt_ty()], vec![v(2)]).expect("None returns");
    assert_eq!(
        outcome.returns,
        vec![InterpretValue {
            ty: opt_ty(),
            kind: InterpretValueKind::Aggregate(vec![isize_value(0), unwritten(Ty::U64)]),
        }],
        "the tag the program wrote, and NO value in the payload lane"
    );
}

#[test]
fn reading_the_written_lane_gives_its_value() {
    let mut body = none_value();
    body.push(result(
        Inst::ExtractField {
            ty: Ty::Isize,
            aggregate: v(2),
            field: 0,
        },
        v(3),
    ));
    let outcome = run(body, vec![Ty::Isize], vec![v(3)]).expect("tag read");
    assert_eq!(outcome.returns, vec![isize_value(0)]);
}

#[test]
fn reading_an_unwritten_lane_is_undefined_behaviour() {
    let mut body = none_value();
    body.push(result(
        Inst::ExtractField {
            ty: Ty::U64,
            aggregate: v(2),
            field: 1,
        },
        v(3),
    ));
    let error = run(body, vec![Ty::U64], vec![v(3)]).expect_err("payload of a None");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

#[test]
fn writing_an_unwritten_lane_replaces_it() {
    let mut body = none_value();
    body.push(result(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        },
        v(3),
    ));
    body.push(result(
        Inst::InsertField {
            ty: opt_ty(),
            aggregate: v(2),
            field: 1,
            value: v(3),
        },
        v(4),
    ));
    body.push(result(
        Inst::ExtractField {
            ty: Ty::U64,
            aggregate: v(4),
            field: 1,
        },
        v(5),
    ));
    let outcome = run(body, vec![Ty::U64], vec![v(5)]).expect("written payload");
    assert_eq!(
        outcome.returns,
        vec![InterpretValue::int(Ty::U64, 7).expect("u64")]
    );
}

#[test]
fn the_aggregate_moves_whole_with_its_lane_still_unwritten() {
    let mut body = none_value();
    body.push(result(
        Inst::Copy {
            ty: opt_ty(),
            operand: v(2),
        },
        v(3),
    ));
    let outcome = run(body, vec![opt_ty()], vec![v(3)]).expect("copy transports");
    assert_eq!(
        outcome.returns[0].kind,
        InterpretValueKind::Aggregate(vec![isize_value(0), unwritten(Ty::U64)])
    );
}

/// `%p = alloca S; store S %2, %p; %l = load S, %p` after `none_value()`.
fn stored_and_reloaded() -> Vec<InstrNode> {
    let mut body = none_value();
    body.push(result(
        Inst::Alloca {
            ty: opt_ty(),
            count: None,
            align: None,
        },
        v(10),
    ));
    body.push(void(Inst::Store {
        ty: opt_ty(),
        ptr: v(10),
        value: v(2),
        volatile: false,
        align: None,
    }));
    body.push(result(
        Inst::Load {
            ty: opt_ty(),
            ptr: v(10),
            volatile: false,
            align: None,
        },
        v(11),
    ));
    body
}

#[test]
fn a_store_and_a_whole_reload_give_the_lane_back_unwritten() {
    let outcome = run(stored_and_reloaded(), vec![opt_ty()], vec![v(11)]).expect("reload");
    assert_eq!(
        outcome.returns[0].kind,
        InterpretValueKind::Aggregate(vec![isize_value(0), unwritten(Ty::U64)]),
        "the MIR local round trip of a None: its payload is still unwritten, never a zero"
    );
    let mut read_payload = stored_and_reloaded();
    read_payload.push(result(
        Inst::ExtractField {
            ty: Ty::U64,
            aggregate: v(11),
            field: 1,
        },
        v(12),
    ));
    let error = run(read_payload, vec![Ty::U64], vec![v(12)]).expect_err("reloaded payload");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

#[test]
fn a_lane_wise_payload_load_of_the_stored_lane_is_poison_and_consuming_it_is_ub() {
    // gep +8 bytes: the payload lane of `{ isize, u64 }`.
    let mut body = stored_and_reloaded();
    body.push(result(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(8),
        },
        v(20),
    ));
    body.push(result(
        Inst::GEP {
            pointee_ty: Ty::I8,
            base: v(10),
            indices: vec![v(20)],
            inbounds: true,
        },
        v(21),
    ));
    body.push(result(
        Inst::Load {
            ty: Ty::U64,
            ptr: v(21),
            volatile: false,
            align: None,
        },
        v(22),
    ));
    body.push(result(
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: v(22),
            rhs: v(20),
        },
        v(23),
    ));
    let error = run(body, vec![Ty::U64], vec![v(23)]).expect_err("arithmetic on the payload");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

#[test]
fn overwriting_the_stored_lane_bytes_makes_the_reload_defined() {
    let mut body = stored_and_reloaded();
    body.push(result(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(8),
        },
        v(20),
    ));
    body.push(result(
        Inst::GEP {
            pointee_ty: Ty::I8,
            base: v(10),
            indices: vec![v(20)],
            inbounds: true,
        },
        v(21),
    ));
    body.push(result(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(5),
        },
        v(22),
    ));
    body.push(void(Inst::Store {
        ty: Ty::U64,
        ptr: v(21),
        value: v(22),
        volatile: false,
        align: None,
    }));
    body.push(result(
        Inst::Load {
            ty: opt_ty(),
            ptr: v(10),
            volatile: false,
            align: None,
        },
        v(23),
    ));
    let outcome = run(body, vec![opt_ty()], vec![v(23)]).expect("reload after the write");
    assert_eq!(
        outcome.returns[0].kind,
        InterpretValueKind::Aggregate(vec![
            isize_value(0),
            InterpretValue::int(Ty::U64, 5).expect("u64"),
        ])
    );
}

#[test]
fn a_volatile_store_of_an_unwritten_lane_is_undefined_behaviour() {
    let mut body = none_value();
    body.push(result(
        Inst::Alloca {
            ty: opt_ty(),
            count: None,
            align: None,
        },
        v(10),
    ));
    body.push(void(Inst::Store {
        ty: opt_ty(),
        ptr: v(10),
        value: v(2),
        volatile: true,
        align: None,
    }));
    let error = run(body, vec![], vec![]).expect_err("volatile store");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

#[test]
fn uninit_stands_only_as_a_direct_struct_or_tuple_lane() {
    let whole = vec![result(
        Inst::Const {
            ty: Ty::U64,
            value: Constant::Uninit,
        },
        v(0),
    )];
    let error = run(whole, vec![Ty::U64], vec![v(0)]).expect_err("a whole uninit constant");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");

    let pair = Ty::Tuple(vec![opt_ty(), Ty::U64]);
    let nested = vec![result(
        Inst::Const {
            ty: pair.clone(),
            value: Constant::Aggregate(vec![
                Constant::Aggregate(vec![Constant::Int(0), Constant::Uninit]),
                Constant::Int(1),
            ]),
        },
        v(0),
    )];
    let error = run(nested, vec![pair], vec![v(0)]).expect_err("an uninit one aggregate deeper");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error}");

    let tuple = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
    let direct = vec![result(
        Inst::Const {
            ty: tuple.clone(),
            value: Constant::Aggregate(vec![Constant::Uninit, Constant::Bool(true)]),
        },
        v(0),
    )];
    let outcome = run(direct, vec![tuple], vec![v(0)]).expect("a direct tuple lane");
    assert_eq!(
        outcome.returns[0].kind,
        InterpretValueKind::Aggregate(vec![unwritten(Ty::U32), InterpretValue::bool(true)])
    );
}

/// The other half of the design, pinned: bytes a program left uninitialised WITHOUT an unwritten
/// lane (here: only the tag stored through a pointer) keep the strict aggregate-load discipline,
/// exactly as before `Constant::Uninit` existed.
#[test]
fn uninitialised_bytes_no_unwritten_lane_left_keep_the_strict_aggregate_load() {
    let body = vec![
        result(
            Inst::Alloca {
                ty: opt_ty(),
                count: None,
                align: None,
            },
            v(0),
        ),
        result(
            Inst::Const {
                ty: Ty::Isize,
                value: Constant::Int(0),
            },
            v(1),
        ),
        void(Inst::Store {
            ty: Ty::Isize,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }),
        result(
            Inst::Load {
                ty: opt_ty(),
                ptr: v(0),
                volatile: false,
                align: None,
            },
            v(2),
        ),
    ];
    let error = run(body, vec![opt_ty()], vec![v(2)]).expect_err("strict aggregate load");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

/// Main's WS2.14 discipline, adapted (not a lane decision): an aggregate store writes padding
/// UNINITIALISED and a whole load treats it as don't-care. `{ u8, u64 }` has seven padding
/// bytes; storing it with its `u64` lane unwritten and reloading it must give the written `u8`
/// back and the lane back unwritten -- the padding is neither a recorded lane nor a covered
/// byte, so it must not turn the reload into undefined behaviour.
#[test]
fn padding_around_an_unwritten_lane_is_dont_care_on_the_reload() {
    let padded = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let body = vec![
        result(
            Inst::Const {
                ty: padded.clone(),
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Uninit]),
            },
            v(0),
        ),
        result(
            Inst::Alloca {
                ty: padded.clone(),
                count: None,
                align: None,
            },
            v(1),
        ),
        void(Inst::Store {
            ty: padded.clone(),
            ptr: v(1),
            value: v(0),
            volatile: false,
            align: None,
        }),
        result(
            Inst::Load {
                ty: padded.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            },
            v(2),
        ),
    ];
    let outcome = run(body, vec![padded], vec![v(2)]).expect("reload across padding");
    assert_eq!(
        outcome.returns[0].kind,
        InterpretValueKind::Aggregate(vec![
            InterpretValue::int(Ty::U8, 7).expect("u8"),
            unwritten(Ty::U64),
        ])
    );
}

/// A decision main's `MemCopy` (WS3.20, which the crystal lane never saw) forced, taken
/// FAIL-CLOSED and pinned so a change is deliberate: a bulk copy moves bytes and their init
/// state but NOT the unwritten-lane record, so a whole reload of the COPY meets uninitialised
/// covered bytes no unwritten lane left there and is undefined behaviour, as for any other
/// uninitialised aggregate bytes. The source still reloads with its lane unwritten.
#[test]
fn a_memcopy_does_not_carry_the_unwritten_lane_record() {
    let copied = |reload_source: bool| {
        let mut body = stored_and_reloaded();
        body.push(result(
            Inst::Alloca {
                ty: opt_ty(),
                count: None,
                align: None,
            },
            v(30),
        ));
        body.push(result(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(16),
            },
            v(31),
        ));
        body.push(void(Inst::MemCopy {
            dst: v(30),
            src: v(10),
            bytes: v(31),
            overlap: false,
        }));
        let from = if reload_source { v(10) } else { v(30) };
        body.push(result(
            Inst::Load {
                ty: opt_ty(),
                ptr: from,
                volatile: false,
                align: None,
            },
            v(32),
        ));
        run(body, vec![opt_ty()], vec![v(32)])
    };
    let source = copied(true).expect("the source keeps its record");
    assert_eq!(
        source.returns[0].kind,
        InterpretValueKind::Aggregate(vec![isize_value(0), unwritten(Ty::U64)])
    );
    let error = copied(false).expect_err("the copy carries no record");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error}");
}

/// The text format carries an unwritten lane as `uninit` and reads it back (crystal lane E3b): the
/// spelling the callee sidecar's text artifact, and every reader of it, sees.
#[cfg(all(feature = "parser", feature = "fmt"))]
#[test]
fn the_text_format_prints_and_reads_back_an_unwritten_lane() {
    let mut module = Module::new("uninit-text");
    module.add_struct(StructDef {
        id: StructId::new(0),
        name: "OptionU64".to_string(),
        fields: vec![
            FieldDef {
                name: "tag".to_string(),
                ty: Ty::Isize,
                offset: None,
            },
            FieldDef {
                name: "payload".to_string(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![opt_ty()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "none", ft, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.extend(none_value());
    block.body.push(void(Inst::Return { values: vec![v(2)] }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let text = crate::format::canonical(&module);
    assert!(text.contains("const struct.0 { uninit, uninit }"), "{text}");
    let back = crate::parser::parse_module(&text).expect("the text reads back");
    assert_eq!(crate::format::canonical(&back), text);
}
