// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::Mutex;

fn scalar(ty: &Ty, bits: u64) -> InterpretValue {
    InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::FloatBits(bits),
    }
}

fn bits(value: &InterpretValue) -> u64 {
    let InterpretValueKind::FloatBits(bits) = value.kind else {
        panic!("not a float: {value:?}")
    };
    bits
}

#[test]
fn minmax_choice_scalar_witness_is_the_actual_selected_operand() {
    for (ty, width, one, nan) in [
        (Ty::F16, 16, 0x3c00, 0x7e00),
        (Ty::F32, 32, 0x3f80_0000, 0x7fc0_0000),
        (Ty::F64, 64, 0x3ff0_0000_0000_0000, 0x7ff8_0000_0000_0000),
    ] {
        let negative_zero = 1u64 << (width - 1);
        for op in [BinOp::FMin, BinOp::FMax] {
            for (left, right) in [(0, negative_zero), (negative_zero, 0)] {
                let events = Mutex::new(Vec::new());
                let record = |choice| events.lock().unwrap().push(choice);
                let observed = Interpreter::new().with_float_zero_choice_observer(&record);
                let result = observed
                    .eval_binop(
                        op,
                        &ty,
                        &scalar(&ty, left),
                        &scalar(&ty, right),
                        BlockId::new(0),
                    )
                    .unwrap();
                assert!(bits(&result) == left || bits(&result) == right);
                assert_eq!(*events.lock().unwrap(), vec![bits(&result) == left]);
            }
            // Every successful case outside the opposite-zero tie has no
            // choice event, including a NaN discarded in favor of a zero.
            for (left, right) in [(0, 0), (negative_zero, negative_zero), (one, 0), (nan, 0)] {
                let events = Mutex::new(Vec::new());
                let record = |choice| events.lock().unwrap().push(choice);
                let result = Interpreter::new()
                    .with_float_zero_choice_observer(&record)
                    .eval_binop(
                        op,
                        &ty,
                        &scalar(&ty, left),
                        &scalar(&ty, right),
                        BlockId::new(0),
                    )
                    .unwrap();
                let plain = Interpreter::new()
                    .eval_binop(
                        op,
                        &ty,
                        &scalar(&ty, left),
                        &scalar(&ty, right),
                        BlockId::new(0),
                    )
                    .unwrap();
                assert_eq!(result, plain);
                assert!(events.lock().unwrap().is_empty());
            }
        }
    }
}

#[test]
fn minmax_choice_splat_records_every_logical_lane_without_expanding_the_value() {
    for (elem, width) in [(Ty::F16, 16), (Ty::F32, 32), (Ty::F64, 64)] {
        for op in [BinOp::FMin, BinOp::FMax] {
            let count = 33;
            let left = 1u64 << (width - 1);
            let ty = Ty::Vector(Box::new(elem.clone()), count);
            let a = InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(ArrayValue::splat(
                    scalar(&elem, left),
                    count.into(),
                )),
            };
            let b = InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(ArrayValue::splat(scalar(&elem, 0), count.into())),
            };
            let events = Mutex::new(Vec::new());
            let record = |choice| events.lock().unwrap().push(choice);
            let output = Interpreter::new()
                .with_float_zero_choice_observer(&record)
                .eval_binop(op, &ty, &a, &b, BlockId::new(0))
                .unwrap();
            let InterpretValueKind::Vector(lanes) = output.kind else {
                panic!("not a vector")
            };
            let lane = lanes
                .as_splat()
                .expect("observation preserves compressed arithmetic");
            assert_eq!(
                *events.lock().unwrap(),
                vec![bits(lane) == left; count as usize]
            );
        }
    }
}

#[test]
fn minmax_choice_periodic_vectors_keep_logical_order_and_skip_nonchoices() {
    let elem = Ty::F64;
    let neg = 1u64 << 63;
    let one = 1.0f64.to_bits();
    let left = ArrayValue::from_vec(vec![
        scalar(&elem, neg),
        scalar(&elem, 0),
        scalar(&elem, one),
    ])
    .repeat(5);
    let right = ArrayValue::from_vec(vec![scalar(&elem, 0), scalar(&elem, neg), scalar(&elem, 0)])
        .repeat(5);
    let ty = Ty::Vector(Box::new(elem), 15);
    for op in [BinOp::FMin, BinOp::FMax] {
        let events = Mutex::new(Vec::new());
        let record = |choice| events.lock().unwrap().push(choice);
        let output = Interpreter::new()
            .with_float_zero_choice_observer(&record)
            .eval_binop(
                op,
                &ty,
                &InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Vector(left.clone()),
                },
                &InterpretValue {
                    ty: ty.clone(),
                    kind: InterpretValueKind::Vector(right.clone()),
                },
                BlockId::new(0),
            )
            .unwrap();
        let InterpretValueKind::Vector(lanes) = output.kind else {
            panic!("not a vector")
        };
        let events = events.lock().unwrap();
        assert_eq!(events.len(), 10);
        for cycle in 0..5 {
            assert_eq!(
                events[cycle * 2],
                bits(lanes.get((cycle * 3) as u64).unwrap()) == neg
            );
            assert_eq!(
                events[cycle * 2 + 1],
                bits(lanes.get((cycle * 3 + 1) as u64).unwrap()) == 0
            );
        }
    }
}

#[test]
fn minmax_choice_failed_vector_does_not_publish_a_partial_vector_witness() {
    let elem = Ty::F64;
    let ty = Ty::Vector(Box::new(elem.clone()), 2);
    let a = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Vector(ArrayValue::from_vec(vec![
            scalar(&elem, 1u64 << 63),
            InterpretValue {
                ty: elem.clone(),
                kind: InterpretValueKind::PartialBytes(vec![None; 8]),
            },
        ])),
    };
    let b = InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Vector(ArrayValue::splat(scalar(&elem, 0), 2)),
    };
    let events = Mutex::new(Vec::new());
    let record = |choice| events.lock().unwrap().push(choice);
    let error = Interpreter::new()
        .with_float_zero_choice_observer(&record)
        .eval_binop(BinOp::FMin, &ty, &a, &b, BlockId::new(0))
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(events.lock().unwrap().is_empty());
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Interpreter<'static>>();
}
