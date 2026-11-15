// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PKG-U13a: the reference interpreter's integer tensor contraction
//! (`Inst::TensorContract` over [`InterpretValueKind::Tensor`] values, XLA
//! `DotGeneral`'s shape). Every computed value is checked against a hand
//! written loop nest; the two undefined-behaviour messages are the normative
//! texts SemR spells byte for byte; static-rule and well-formedness failures
//! are `TypeError`s prefixed `tensor contraction: `. No instruction builds a
//! tensor yet, so every operand is an entry argument built here directly.

use super::*;

const EXTENT_MISMATCH: &str = "tensor contraction: paired axes have different extents";
const RESULT_TOO_LARGE: &str = "tensor contraction: the result has more elements than usize holds";

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

/// A tensor whose extents include a 0, so it has no elements.
fn empty_tensor(elem: &Ty, dims: &[u64]) -> InterpretValue {
    tensor(elem, dims, &[])
}

fn wasm32() -> crate::TargetInfo {
    crate::TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// `fn contract(%0: lhs_ty, %1: rhs_ty) -> result_ty { %2 = tensor_contract
/// result_ty %0, %1 batch [..] contract [..]; return %2 }`.
fn contraction_module(
    lhs_ty: Ty,
    rhs_ty: Ty,
    result_ty: Ty,
    batch: &[(u32, u32)],
    contract: &[(u32, u32)],
    target: Option<crate::TargetInfo>,
) -> Module {
    let mut module = Module::new("tensor-contract");
    module.target_info = target;
    let sig = module
        .add_func_type(FuncTy {
            abi: None,
            params: vec![lhs_ty.clone(), rhs_ty.clone()],
            returns: vec![result_ty.clone()],
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "contract", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0))
        .with_param(v(0), lhs_ty)
        .with_param(v(1), rhs_ty);
    block.body.push(
        InstrNode::new(Inst::TensorContract {
            ty: result_ty,
            lhs: v(0),
            rhs: v(1),
            batch: batch.to_vec(),
            contract: contract.to_vec(),
        })
        .with_result(v(2)),
    );
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

/// Contract `lhs` with `rhs` into `result_ty` (the operand types are the
/// arguments' own).
fn run(
    lhs: InterpretValue,
    rhs: InterpretValue,
    result_ty: Ty,
    batch: &[(u32, u32)],
    contract: &[(u32, u32)],
    target: Option<crate::TargetInfo>,
) -> InterpretResult<InterpretOutcome> {
    let module = contraction_module(
        lhs.ty.clone(),
        rhs.ty.clone(),
        result_ty,
        batch,
        contract,
        target,
    );
    Interpreter::with_module(&module).execute_func(FuncId::new(0), [lhs, rhs])
}

/// The one returned tensor's extents and elements (signed or unsigned as its
/// carrier says). Only for short results: it walks every element.
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

/// The one returned tensor's extents and element payload, without walking it.
fn parts(outcome: &InterpretOutcome) -> (&[u64], &ArrayValue) {
    let [value] = outcome.returns.as_slice() else {
        panic!("one return, got {:?}", outcome.returns);
    };
    let InterpretValueKind::Tensor { dims, elems } = &value.kind else {
        panic!("a tensor result, got {value:?}");
    };
    (dims.as_slice(), elems)
}

#[test]
fn matmul_matches_a_hand_loop_nest_in_one_fuel_unit() {
    let (m, k, n) = (2, 3, 2);
    let a = [1i128, -2, 3, 4, 5, -6];
    let b = [7i128, 8, -9, 10, 11, 12];
    let mut expected = Vec::new();
    for i in 0..m {
        for j in 0..n {
            let mut acc = 0;
            for t in 0..k {
                acc += a[i * k + t] * b[t * n + j];
            }
            expected.push(acc);
        }
    }
    let outcome = run(
        tensor(&Ty::I32, &[2, 3], &a),
        tensor(&Ty::I32, &[3, 2], &b),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect("a 2x3 . 3x2 matmul runs");
    assert_eq!(outcome.returns[0].ty, tensor_ty(Ty::I32, 2));
    assert_eq!(unpack(&outcome), (vec![2, 2], expected));
    // The contraction and the return: ONE fuel unit each, however many
    // elements the contraction materializes.
    assert_eq!(outcome.steps, 2);
}

#[test]
fn free_axes_come_left_then_right_each_ascending() {
    // A . B^T: contracting both last axes leaves the left free axis, then the
    // right free axis.
    let (m, k, n) = (2, 3, 4);
    let a: Vec<i128> = (0..6).map(|x| x - 2).collect();
    let b: Vec<i128> = (0..12).map(|x| 3 * x - 5).collect();
    let mut expected = Vec::new();
    for i in 0..m {
        for j in 0..n {
            let mut acc = 0;
            for t in 0..k {
                acc += a[i * k + t] * b[j * k + t];
            }
            expected.push(acc);
        }
    }
    let outcome = run(
        tensor(&Ty::I64, &[2, 3], &a),
        tensor(&Ty::I64, &[4, 3], &b),
        tensor_ty(Ty::I64, 2),
        &[],
        &[(1, 1)],
        None,
    )
    .expect("A . B^T runs");
    assert_eq!(unpack(&outcome), (vec![2, 4], expected));
}

#[test]
fn batched_matmul_puts_batch_axes_first() {
    // [batch, m, k] . [batch, k, n] -> [batch, m, n].
    let (nb, m, k, n) = (2, 2, 3, 2);
    let a: Vec<i128> = (1..=12).collect();
    let b: Vec<i128> = (1..=12).map(|x| x - 6).collect();
    let mut expected = Vec::new();
    for batch in 0..nb {
        for i in 0..m {
            for j in 0..n {
                let mut acc = 0;
                for t in 0..k {
                    acc += a[batch * m * k + i * k + t] * b[batch * k * n + t * n + j];
                }
                expected.push(acc);
            }
        }
    }
    let outcome = run(
        tensor(&Ty::I32, &[2, 2, 3], &a),
        tensor(&Ty::I32, &[2, 3, 2], &b),
        tensor_ty(Ty::I32, 3),
        &[(0, 0)],
        &[(2, 1)],
        None,
    )
    .expect("a batched matmul runs");
    assert_eq!(unpack(&outcome), (vec![2, 2, 2], expected));

    // A batch axis that is not leading on either side: [k, batch] . [batch,
    // k] -> [batch], one dot product per batch index.
    let (nb, k) = (2, 3);
    let a = [1i128, 2, 3, 4, 5, 6];
    let b = [-1i128, 0, 2, 7, -3, 1];
    let expected: Vec<i128> = (0..nb)
        .map(|batch| {
            (0..k)
                .map(|t| a[t * nb + batch] * b[batch * k + t])
                .sum::<i128>()
        })
        .collect();
    let outcome = run(
        tensor(&Ty::I32, &[3, 2], &a),
        tensor(&Ty::I32, &[2, 3], &b),
        tensor_ty(Ty::I32, 1),
        &[(1, 0)],
        &[(0, 1)],
        None,
    )
    .expect("a trailing batch axis runs");
    assert_eq!(unpack(&outcome), (vec![2], expected));
}

#[test]
fn integer_arithmetic_wraps_at_the_element_width() {
    // Each product and each partial sum wraps at i8, exactly `BinOp::Mul` /
    // `BinOp::Add`: 100*2 = 200 -> -56, -128*-1 = 128 -> -128, and the left
    // fold -56 + -56 + -128 = -240 -> 16.
    let l = [100i128, 100, -128];
    let r = [2i128, 2, -1];
    let expected = l.iter().zip(&r).fold(0i8, |acc, (&x, &y)| {
        acc.wrapping_add((x as i8).wrapping_mul(y as i8))
    });
    assert_eq!(expected, 16);
    let outcome = run(
        tensor(&Ty::I8, &[3], &l),
        tensor(&Ty::I8, &[3], &r),
        tensor_ty(Ty::I8, 0),
        &[],
        &[(0, 0)],
        None,
    )
    .expect("an i8 dot product runs");
    assert_eq!(unpack(&outcome), (vec![], vec![i128::from(expected)]));

    // Unsigned: 200 * 2 = 400 -> 144 at u8.
    let outcome = run(
        tensor(&Ty::U8, &[1], &[200]),
        tensor(&Ty::U8, &[1], &[2]),
        tensor_ty(Ty::U8, 0),
        &[],
        &[(0, 0)],
        None,
    )
    .expect("a u8 dot product runs");
    assert_eq!(unpack(&outcome), (vec![], vec![144]));
}

#[test]
fn a_zero_contracted_extent_gives_zeros_as_one_uniform_node() {
    let outcome = run(
        empty_tensor(&Ty::U16, &[2, 0]),
        empty_tensor(&Ty::U16, &[0, 3]),
        tensor_ty(Ty::U16, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect("an empty contraction runs");
    assert_eq!(unpack(&outcome), (vec![2, 3], vec![0; 6]));
    let (_, elems) = parts(&outcome);
    assert_eq!(elems.as_splat(), Some(&int(&Ty::U16, 0)));

    // A zero FREE extent gives a result with no elements.
    let outcome = run(
        empty_tensor(&Ty::I32, &[0, 3]),
        tensor(&Ty::I32, &[3, 2], &[1, 2, 3, 4, 5, 6]),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect("a contraction with no result elements runs");
    assert_eq!(unpack(&outcome), (vec![0, 2], vec![]));
}

#[test]
fn rank_zero_operands_are_one_element_each() {
    // No pairs: one product of the two scalars.
    let outcome = run(
        tensor(&Ty::I64, &[], &[7]),
        tensor(&Ty::I64, &[], &[-6]),
        tensor_ty(Ty::I64, 0),
        &[],
        &[],
        None,
    )
    .expect("a rank-0 product runs");
    assert_eq!(unpack(&outcome), (vec![], vec![-42]));

    // A rank-0 left operand scales the right one (an outer product).
    let outcome = run(
        tensor(&Ty::I64, &[], &[3]),
        tensor(&Ty::I64, &[4], &[1, 2, 3, 4]),
        tensor_ty(Ty::I64, 1),
        &[],
        &[],
        None,
    )
    .expect("a scalar times a vector runs");
    assert_eq!(unpack(&outcome), (vec![4], vec![3, 6, 9, 12]));
}

#[test]
fn two_contracted_axes_sum_over_both() {
    // [i, j, k] . [k, j, n] contracting (j, j) and (k, k) -> [i, n].
    let (ni, nj, nk, nn) = (2, 3, 4, 5);
    let a: Vec<i128> = (0..24).map(|x| x - 7).collect();
    let b: Vec<i128> = (0..60).map(|x| (x * 7) % 11 - 5).collect();
    let mut expected = Vec::new();
    for i in 0..ni {
        for n in 0..nn {
            let mut acc = 0;
            for j in 0..nj {
                for k in 0..nk {
                    acc += a[i * nj * nk + j * nk + k] * b[k * nj * nn + j * nn + n];
                }
            }
            expected.push(acc);
        }
    }
    for contract in [[(1, 1), (2, 0)], [(2, 0), (1, 1)]] {
        let outcome = run(
            tensor(&Ty::I32, &[2, 3, 4], &a),
            tensor(&Ty::I32, &[4, 3, 5], &b),
            tensor_ty(Ty::I32, 2),
            &[],
            &contract,
            None,
        )
        .expect("a two-axis contraction runs");
        assert_eq!(
            unpack(&outcome),
            (vec![2, 5], expected.clone()),
            "contract {contract:?}"
        );
    }
}

#[test]
fn paired_extents_that_differ_are_undefined_behaviour() {
    // A contracted pair: 3 against 4.
    let error = run(
        tensor(&Ty::I32, &[2, 3], &[0; 6]),
        tensor(&Ty::I32, &[4, 2], &[0; 8]),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect_err("contracted extents differ");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert_eq!(error.message, EXTENT_MISMATCH);

    // A batch pair: 2 against 3, though the contracted pair agrees.
    let error = run(
        tensor(&Ty::I32, &[2, 1, 3], &[0; 6]),
        tensor(&Ty::I32, &[3, 3, 1], &[0; 9]),
        tensor_ty(Ty::I32, 3),
        &[(0, 0)],
        &[(2, 1)],
        None,
    )
    .expect_err("batch extents differ");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert_eq!(error.message, EXTENT_MISMATCH);

    // Operand well-formedness comes first: a left operand whose extents do
    // not describe its elements is a TypeError even though extents differ.
    let error = run(
        tensor(&Ty::I32, &[2, 3], &[0; 5]),
        tensor(&Ty::I32, &[4, 2], &[0; 8]),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect_err("a malformed operand");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
}

#[test]
fn a_result_count_usize_cannot_hold_is_undefined_behaviour() {
    // Zero contracted extents make every operand empty, so only the result
    // count is large: 65536 x 65536 = 2^32 elements, one more than a 32-bit
    // usize holds below 2^32.
    let lhs = empty_tensor(&Ty::I32, &[65_536, 0]);
    let rhs = empty_tensor(&Ty::I32, &[0, 65_536]);
    let error = run(
        lhs.clone(),
        rhs.clone(),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        Some(wasm32()),
    )
    .expect_err("2^32 elements on a 32-bit target");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert_eq!(error.message, RESULT_TOO_LARGE);

    // 65536 x 65535 fits, and the all-zero result is one uniform node: the
    // count was decided before anything was allocated.
    let outcome = run(
        lhs.clone(),
        empty_tensor(&Ty::I32, &[0, 65_535]),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        Some(wasm32()),
    )
    .expect("2^32 - 2^16 elements fit a 32-bit usize");
    let (dims, elems) = parts(&outcome);
    assert_eq!(dims, [65_536, 65_535]);
    assert_eq!(elems.len(), 65_536 * 65_535);
    assert_eq!(elems.as_splat(), Some(&int(&Ty::I32, 0)));

    // The same 2^32 elements fit a 64-bit usize.
    let outcome = run(lhs, rhs, tensor_ty(Ty::I32, 2), &[], &[(1, 0)], None)
        .expect("2^32 elements on a 64-bit target");
    assert_eq!(parts(&outcome).1.len(), 1 << 32);

    // 2^64 elements do not.
    let error = run(
        empty_tensor(&Ty::I32, &[1 << 32, 0]),
        empty_tensor(&Ty::I32, &[0, 1 << 32]),
        tensor_ty(Ty::I32, 2),
        &[],
        &[(1, 0)],
        None,
    )
    .expect_err("2^64 elements on a 64-bit target");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert_eq!(error.message, RESULT_TOO_LARGE);
}

#[test]
fn rank_and_element_mismatches_are_type_errors() {
    let i32_tensor = |dims: &[u64], len: usize| tensor(&Ty::I32, dims, &vec![1; len]);
    let float = |bits: f32| InterpretValue {
        ty: Ty::F32,
        kind: InterpretValueKind::FloatBits(u64::from(bits.to_bits())),
    };
    let f32_tensor = InterpretValue {
        ty: tensor_ty(Ty::F32, 1),
        kind: InterpretValueKind::Tensor {
            dims: vec![2],
            elems: ArrayValue::from_vec(vec![float(1.0), float(2.0)]),
        },
    };
    let wrong_extent_count = InterpretValue {
        ty: tensor_ty(Ty::I32, 2),
        kind: InterpretValueKind::Tensor {
            dims: vec![6],
            elems: ArrayValue::from_vec(vec![int(&Ty::I32, 0); 6]),
        },
    };
    let stray_element = InterpretValue {
        ty: tensor_ty(Ty::I32, 1),
        kind: InterpretValueKind::Tensor {
            dims: vec![2],
            elems: ArrayValue::from_vec(vec![int(&Ty::I32, 0), int(&Ty::I64, 0)]),
        },
    };
    type Case = (
        &'static str,
        InterpretValue,
        InterpretValue,
        Ty,
        Vec<(u32, u32)>,
        Vec<(u32, u32)>,
    );
    let cases: Vec<Case> = vec![
        (
            "result rank",
            i32_tensor(&[2, 3], 6),
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I32, 3),
            vec![],
            vec![(1, 0)],
        ),
        (
            "operand element types",
            i32_tensor(&[2, 3], 6),
            tensor(&Ty::I64, &[3, 2], &[1; 6]),
            tensor_ty(Ty::I32, 2),
            vec![],
            vec![(1, 0)],
        ),
        (
            "result element type",
            i32_tensor(&[2, 3], 6),
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I64, 2),
            vec![],
            vec![(1, 0)],
        ),
        (
            "float element",
            f32_tensor.clone(),
            f32_tensor,
            tensor_ty(Ty::F32, 0),
            vec![],
            vec![(0, 0)],
        ),
        (
            "left axis out of range",
            i32_tensor(&[2, 3], 6),
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I32, 2),
            vec![],
            vec![(2, 0)],
        ),
        (
            "left axis paired twice",
            i32_tensor(&[2, 2], 4),
            i32_tensor(&[2, 2], 4),
            tensor_ty(Ty::I32, 0),
            vec![],
            vec![(0, 0), (0, 1)],
        ),
        (
            "non-tensor operand",
            int(&Ty::I32, 1),
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I32, 2),
            vec![],
            vec![(1, 0)],
        ),
        (
            "extent count against rank",
            wrong_extent_count,
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I32, 2),
            vec![],
            vec![(1, 0)],
        ),
        (
            "extents against element count",
            i32_tensor(&[2, 3], 5),
            i32_tensor(&[3, 2], 6),
            tensor_ty(Ty::I32, 2),
            vec![],
            vec![(1, 0)],
        ),
        (
            "element of another type",
            stray_element,
            i32_tensor(&[2], 2),
            tensor_ty(Ty::I32, 0),
            vec![],
            vec![(0, 0)],
        ),
    ];
    for (what, lhs, rhs, result_ty, batch, contract) in cases {
        let error = run(lhs, rhs, result_ty, &batch, &contract, None).expect_err(what);
        assert_eq!(
            error.code,
            InterpretErrorCode::TypeError,
            "{what}: {error:?}"
        );
        assert!(
            error.message.starts_with("tensor contraction: "),
            "{what}: {error:?}"
        );
    }
}

#[test]
fn usize_elements_run_at_the_target_pointer_width() {
    // Built outside the run at the 64-bit reference width, re-expressed at
    // 32 bits on entry: 4294967295 * 2 + 2 * 3 wraps to 4 at a 32-bit usize.
    let lhs = || tensor(&Ty::Usize, &[2], &[4_294_967_295, 2]);
    let rhs = || tensor(&Ty::Usize, &[2], &[2, 3]);
    let scalar = |target: Option<crate::TargetInfo>| {
        let outcome = run(
            lhs(),
            rhs(),
            tensor_ty(Ty::Usize, 0),
            &[],
            &[(0, 0)],
            target,
        )
        .expect("a usize dot product runs");
        let (dims, elems) = parts(&outcome);
        assert!(dims.is_empty());
        let element = elems.get(0).expect("one element").clone();
        assert_eq!(element.ty, Ty::Usize);
        element.as_int().expect("integer element")
    };
    let narrow = scalar(Some(wasm32()));
    assert_eq!((narrow.bits, narrow.signed, narrow.raw), (32, false, 4));
    let wide = scalar(None);
    assert_eq!(
        (wide.bits, wide.signed, wide.raw),
        (64, false, 8_589_934_596)
    );

    // An element or an extent a 32-bit usize cannot hold is refused on entry.
    let error = run(
        tensor(&Ty::Usize, &[1], &[1 << 32]),
        rhs(),
        tensor_ty(Ty::Usize, 0),
        &[],
        &[(0, 0)],
        Some(wasm32()),
    )
    .expect_err("a usize element above 2^32 - 1 on wasm32");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    let error = run(
        empty_tensor(&Ty::Usize, &[1 << 32, 0]),
        empty_tensor(&Ty::Usize, &[0, 1]),
        tensor_ty(Ty::Usize, 2),
        &[],
        &[(1, 0)],
        Some(wasm32()),
    )
    .expect_err("an extent of 2^32 on wasm32");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
}
