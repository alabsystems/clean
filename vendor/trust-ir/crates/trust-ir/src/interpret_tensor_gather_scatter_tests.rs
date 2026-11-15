// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PKG-U13d: the reference interpreter's tensor gather and scatter
//! (`Inst::TensorGather`, `Inst::TensorScatter`; SPEC_RATIFICATIONS §26).
//! Every computed value is checked against a hand-written loop; the four
//! undefined-behaviour messages are the normative texts SemR spells byte for
//! byte; static-rule and well-formedness failures are `TypeError`s prefixed
//! `tensor gather: ` / `tensor scatter: `. Every operand is an entry argument
//! built here directly (or an `undef`, for the poison rule).

use super::*;

const GATHER_EXTENTS: &str = "tensor gather: coordinate tensors have different extents";
const GATHER_OUT_OF_RANGE: &str = "tensor gather: a coordinate is outside its axis";
const SCATTER_EXTENTS: &str = "tensor scatter: coordinate tensor extents differ from the source's";
const SCATTER_OUT_OF_RANGE: &str = "tensor scatter: a coordinate is outside its axis";

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn tensor_ty(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn int(ty: &Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty.clone(), value).expect("integer value")
}

/// A tensor of `elem` with extents `dims` and the row-major `values`.
fn tensor(elem: &Ty, dims: &[u64], values: &[i128]) -> InterpretValue {
    let elems = values.iter().map(|&value| int(elem, value)).collect();
    InterpretValue {
        ty: tensor_ty(elem.clone(), dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: ArrayValue::from_vec(elems),
        },
    }
}

/// `fn t(%0: args[0].ty, ..) -> result_ty { [%k = undef poison]; %r = inst;
/// return %r }`, run on `args`. `poison`, when given, is an `undef` of that
/// type bound to the id after the parameters, before `inst`.
fn run(
    args: Vec<InterpretValue>,
    poison: Option<Ty>,
    result_ty: Ty,
    inst: Inst,
) -> InterpretResult<InterpretOutcome> {
    let mut module = Module::new("tensor-gather-scatter");
    let params: Vec<Ty> = args.iter().map(|arg| arg.ty.clone()).collect();
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: params.clone(),
            returns: vec![result_ty],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "t", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    for (i, ty) in params.iter().enumerate() {
        block = block.with_param(v(i as u32), ty.clone());
    }
    let mut next = params.len() as u32;
    if let Some(ty) = poison {
        block
            .body
            .push(InstrNode::new(Inst::Undef { ty }).with_result(v(next)));
        next += 1;
    }
    block.body.push(InstrNode::new(inst).with_result(v(next)));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![v(next)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    Interpreter::with_module(&module).execute_func(FuncId::new(0), args)
}

/// The one returned tensor's extents and elements (signed or unsigned as its
/// carrier says).
fn unpack(outcome: &InterpretOutcome) -> (Vec<u64>, Vec<i128>) {
    let [value] = outcome.returns.as_slice() else {
        panic!("one return, got {:?}", outcome.returns);
    };
    let InterpretValueKind::Tensor { dims, elems } = &value.kind else {
        panic!("a tensor result, got {value:?}");
    };
    let values = elems
        .iter()
        .map(|element| {
            let carried = element.as_int().expect("integer element");
            if carried.signed {
                carried.as_signed()
            } else {
                carried.as_unsigned() as i128
            }
        })
        .collect();
    (dims.clone(), values)
}

fn gather(ty: Ty, coords: usize) -> Inst {
    Inst::TensorGather {
        ty,
        data: v(0),
        coords: (1..=coords as u32).map(v).collect(),
    }
}

fn scatter(ty: Ty, coords: usize) -> Inst {
    Inst::TensorScatter {
        ty,
        init: v(0),
        src: v(1),
        coords: (2..2 + coords as u32).map(v).collect(),
    }
}

fn verdict(result: InterpretResult<InterpretOutcome>) -> (InterpretErrorCode, String) {
    let error = result.expect_err("a refusal");
    (error.code, error.message)
}

#[test]
fn a_gather_matches_a_hand_loop_in_one_fuel_unit() {
    // data: 3x4, coordinates of a 2x2 result, the row axis an i64 tensor and
    // the column axis a u8 one.
    let data: Vec<i128> = (0..12).map(|x| 10 * x - 7).collect();
    let rows = [2i128, 0, 1, 2];
    let cols = [3i128, 0, 2, 3];
    let expected: Vec<i128> = rows
        .iter()
        .zip(&cols)
        .map(|(&r, &c)| data[(r * 4 + c) as usize])
        .collect();
    let outcome = run(
        vec![
            tensor(&Ty::I32, &[3, 4], &data),
            tensor(&Ty::I64, &[2, 2], &rows),
            tensor(&Ty::U8, &[2, 2], &cols),
        ],
        None,
        tensor_ty(Ty::I32, 2),
        gather(tensor_ty(Ty::I32, 2), 2),
    )
    .expect("a gather runs");
    assert_eq!(outcome.returns[0].ty, tensor_ty(Ty::I32, 2));
    assert_eq!(unpack(&outcome), (vec![2, 2], expected));
    // The gather and the return: ONE fuel unit each.
    assert_eq!(outcome.steps, 2);
}

#[test]
fn a_scatter_matches_a_hand_loop_and_the_row_major_last_write_wins() {
    // init: 2x3; src: 2x2 written at (rows, cols) row-major, with (0, 1)
    // named by source positions 0 and 2: position 2 is the later write.
    let init: Vec<i128> = (0..6).map(|x| -x).collect();
    let src = [100i128, 200, 300, 400];
    let rows = [0i128, 1, 0, 1];
    let cols = [1i128, 2, 1, 0];
    let mut expected = init.clone();
    for p in 0..4 {
        expected[(rows[p] * 3 + cols[p]) as usize] = src[p];
    }
    assert_eq!(expected[1], 300, "the hand loop keeps the last write");
    let outcome = run(
        vec![
            tensor(&Ty::I16, &[2, 3], &init),
            tensor(&Ty::I16, &[2, 2], &src),
            tensor(&Ty::Usize, &[2, 2], &rows),
            tensor(&Ty::I8, &[2, 2], &cols),
        ],
        None,
        tensor_ty(Ty::I16, 2),
        scatter(tensor_ty(Ty::I16, 2), 2),
    )
    .expect("a scatter runs");
    assert_eq!(unpack(&outcome), (vec![2, 3], expected));
    assert_eq!(outcome.steps, 2);
}

#[test]
fn a_coordinate_reads_as_the_integer_its_type_denotes() {
    let data: Vec<i128> = (0..256).collect();
    // u8 255 is inside an axis of 256.
    let outcome = run(
        vec![
            tensor(&Ty::I32, &[256], &data),
            tensor(&Ty::U8, &[1], &[255]),
        ],
        None,
        tensor_ty(Ty::I32, 1),
        gather(tensor_ty(Ty::I32, 1), 1),
    )
    .expect("an unsigned coordinate");
    assert_eq!(unpack(&outcome), (vec![1], vec![255]));
    // i8 -1 (residue 255) is negative, so outside every axis.
    assert_eq!(
        verdict(run(
            vec![
                tensor(&Ty::I32, &[256], &data),
                tensor(&Ty::I8, &[1], &[-1]),
            ],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 1),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            GATHER_OUT_OF_RANGE.to_string()
        )
    );
}

#[test]
fn the_preconditions_are_undefined_behaviour_by_message() {
    let data = || tensor(&Ty::I32, &[2, 2], &[1, 2, 3, 4]);
    // Coordinate tensors of different extents (the extents precondition is
    // decided before the bounds one, so an out-of-range coordinate does not
    // change the verdict).
    assert_eq!(
        verdict(run(
            vec![
                data(),
                tensor(&Ty::I32, &[2], &[0, 9]),
                tensor(&Ty::I32, &[3], &[0, 0, 0]),
            ],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 2),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            GATHER_EXTENTS.to_string()
        )
    );
    assert_eq!(
        verdict(run(
            vec![
                data(),
                tensor(&Ty::I32, &[2], &[0, 2]),
                tensor(&Ty::I32, &[2], &[0, 0]),
            ],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 2),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            GATHER_OUT_OF_RANGE.to_string()
        )
    );
    assert_eq!(
        verdict(run(
            vec![
                data(),
                tensor(&Ty::I32, &[2], &[5, 6]),
                tensor(&Ty::I32, &[2], &[0, 9]),
                tensor(&Ty::I32, &[3], &[0, 0, 0]),
            ],
            None,
            tensor_ty(Ty::I32, 2),
            scatter(tensor_ty(Ty::I32, 2), 2),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            SCATTER_EXTENTS.to_string()
        )
    );
    // The LAST source position is out of range: the verdict is the bounds
    // precondition, not a partial write.
    assert_eq!(
        verdict(run(
            vec![
                data(),
                tensor(&Ty::I32, &[2], &[5, 6]),
                tensor(&Ty::I32, &[2], &[0, 1]),
                tensor(&Ty::I32, &[2], &[1, -1]),
            ],
            None,
            tensor_ty(Ty::I32, 2),
            scatter(tensor_ty(Ty::I32, 2), 2),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            SCATTER_OUT_OF_RANGE.to_string()
        )
    );
    // A data axis of extent 0 has no coordinate inside it.
    assert_eq!(
        verdict(run(
            vec![tensor(&Ty::I32, &[0], &[]), tensor(&Ty::I32, &[1], &[0]),],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 1),
        )),
        (
            InterpretErrorCode::UndefinedBehavior,
            GATHER_OUT_OF_RANGE.to_string()
        )
    );
}

#[test]
fn empty_coordinate_tensors_read_and_write_nothing() {
    // No position: no coordinate is read, even against an empty data axis.
    let outcome = run(
        vec![tensor(&Ty::I32, &[0], &[]), tensor(&Ty::I32, &[0], &[])],
        None,
        tensor_ty(Ty::I32, 1),
        gather(tensor_ty(Ty::I32, 1), 1),
    )
    .expect("an empty gather");
    assert_eq!(unpack(&outcome), (vec![0], vec![]));
    let outcome = run(
        vec![
            tensor(&Ty::U32, &[3], &[7, 8, 9]),
            tensor(&Ty::U32, &[0, 4], &[]),
            tensor(&Ty::I64, &[0, 4], &[]),
        ],
        None,
        tensor_ty(Ty::U32, 1),
        scatter(tensor_ty(Ty::U32, 1), 1),
    )
    .expect("an empty scatter");
    assert_eq!(unpack(&outcome), (vec![3], vec![7, 8, 9]));
}

#[test]
fn the_static_rules_are_type_errors_and_poison_comes_first() {
    let data = || tensor(&Ty::I32, &[2], &[1, 2]);
    let coord = || tensor(&Ty::I32, &[1], &[0]);
    let type_error = |result: InterpretResult<InterpretOutcome>, prefix: &str| {
        let (code, message) = verdict(result);
        assert_eq!(code, InterpretErrorCode::TypeError, "{message}");
        assert!(message.starts_with(prefix), "{message}");
    };
    // G1: the data's element is not the result's.
    type_error(
        run(
            vec![tensor(&Ty::I64, &[2], &[1, 2]), coord()],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 1),
        ),
        "tensor gather: G1",
    );
    // G2: one coordinate tensor for rank-1 data is required.
    type_error(
        run(
            vec![data(), coord(), coord()],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 2),
        ),
        "tensor gather: G2",
    );
    // G3: a coordinate tensor of the wrong rank.
    type_error(
        run(
            vec![data(), tensor(&Ty::I32, &[1, 1], &[0])],
            None,
            tensor_ty(Ty::I32, 1),
            gather(tensor_ty(Ty::I32, 1), 1),
        ),
        "tensor gather: G3",
    );
    // S1: `init` is not of the result type.
    type_error(
        run(
            vec![tensor(&Ty::I64, &[2], &[1, 2]), data(), coord()],
            None,
            tensor_ty(Ty::I32, 1),
            scatter(tensor_ty(Ty::I32, 1), 1),
        ),
        "tensor scatter: S1",
    );
    // S2: a rank-0 result has no axis.
    type_error(
        run(
            vec![tensor(&Ty::I32, &[], &[1]), tensor(&Ty::I32, &[], &[1])],
            None,
            tensor_ty(Ty::I32, 0),
            Inst::TensorScatter {
                ty: tensor_ty(Ty::I32, 0),
                init: v(0),
                src: v(1),
                coords: vec![],
            },
        ),
        "tensor scatter: S2",
    );
    // S3: a coordinate tensor of the wrong rank for the source.
    type_error(
        run(
            vec![data(), data(), tensor(&Ty::I32, &[1, 1], &[0])],
            None,
            tensor_ty(Ty::I32, 1),
            scatter(tensor_ty(Ty::I32, 1), 1),
        ),
        "tensor scatter: S3",
    );
    // A poison operand is undefined behaviour ahead of every static rule. The
    // poison is a SCALAR `undef` (a `PartialBytes` value, which binds), so
    // the instruction itself runs; at each operand position it is also of
    // the wrong type, under a result type that violates G1 / S1, so only
    // the poison-first order yields this verdict and its message.
    let poisoned = |result: InterpretResult<InterpretOutcome>, site: &str| {
        let (code, message) = verdict(result);
        assert_eq!(code, InterpretErrorCode::UndefinedBehavior, "{message}");
        assert!(
            message.contains(&format!(
                "{site}: use of an uninitialized value — poison (uninitialized bytes, `undef`, \
                 or an unbound slot) may only be copied or stored, never inspected"
            )),
            "{message}"
        );
    };
    // The gather's poison coordinate (`%1`).
    poisoned(
        run(
            vec![data()],
            Some(Ty::I32),
            Ty::I32,
            Inst::TensorGather {
                ty: Ty::I32,
                data: v(0),
                coords: vec![v(1)],
            },
        ),
        "tensor_gather",
    );
    // The gather's poison data (`%1`), ahead of G1.
    poisoned(
        run(
            vec![tensor(&Ty::Usize, &[1], &[0])],
            Some(Ty::I32),
            Ty::I32,
            Inst::TensorGather {
                ty: Ty::I32,
                data: v(1),
                coords: vec![v(0)],
            },
        ),
        "tensor_gather",
    );
    // The scatter's poison init, source and coordinate (`%2` each), ahead
    // of S1.
    let src = || tensor(&Ty::I32, &[1], &[5]);
    let coord = || tensor(&Ty::Usize, &[1], &[0]);
    for (init, source, coordinate) in [(2, 0, 1), (0, 2, 1), (0, 1, 2)] {
        let args = match (init, source) {
            (2, _) => vec![src(), coord()],
            (_, 2) => vec![data(), coord()],
            _ => vec![data(), src()],
        };
        poisoned(
            run(
                args,
                Some(Ty::I32),
                Ty::I32,
                Inst::TensorScatter {
                    ty: Ty::I32,
                    init: v(init),
                    src: v(source),
                    coords: vec![v(coordinate)],
                },
            ),
            "tensor_scatter",
        );
    }
}
