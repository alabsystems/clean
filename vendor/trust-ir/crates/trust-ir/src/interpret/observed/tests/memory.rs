// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(
    clippy::manual_memcpy,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn byte_array(len: u64) -> Ty {
    Ty::Array(TyId::new(0), len)
}
fn constant(ty: Ty, n: i128, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty,
            value: Constant::Int(n),
        },
        result,
    )
}
fn array_value(bytes: &[u8]) -> InterpretValue {
    InterpretValue {
        ty: byte_array(bytes.len() as u64),
        kind: InterpretValueKind::Array(ArrayValue::from_vec(
            bytes.iter().map(|b| int(Ty::U8, i128::from(*b))).collect(),
        )),
    }
}
fn bytes(value: &InterpretValue) -> Vec<u8> {
    let InterpretValueKind::Array(array) = &value.kind else {
        panic!("array");
    };
    array
        .iter()
        .map(|v| v.as_int().expect("U8").raw as u8)
        .collect()
}

fn copy_program(overlap: bool) -> Module {
    let ty = byte_array(6);
    module(
        vec![ty.clone()],
        vec![ty.clone()],
        vec![
            node(
                Inst::Alloca {
                    ty: ty.clone(),
                    count: None,
                    align: None,
                },
                1,
            ),
            void(Inst::Store {
                ty: ty.clone(),
                ptr: v(1),
                value: v(0),
                volatile: false,
                align: None,
            }),
            constant(Ty::U64, 1, 2),
            node(
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: v(1),
                    indices: vec![v(2)],
                    inbounds: false,
                },
                3,
            ),
            constant(Ty::U64, 5, 4),
            void(Inst::MemCopy {
                dst: v(3),
                src: v(1),
                bytes: v(4),
                overlap,
            }),
            node(
                Inst::Load {
                    ty,
                    ptr: v(1),
                    volatile: false,
                    align: None,
                },
                5,
            ),
            void(Inst::Return { values: vec![v(5)] }),
        ],
    )
}

#[test]
fn observed_memmove_uses_prewrite_snapshot_and_matches_independent_byte_loop() {
    let module = copy_program(true);
    let initial = [1, 2, 3, 4, 5, 6];
    let source = initial;
    let mut expected = initial;
    for index in 0..5 {
        expected[index + 1] = source[index];
    }
    let ordinary = Interpreter::with_module(&module)
        .execute_func(f(), vec![array_value(&initial)])
        .expect("ordinary");
    let report = run(
        &module,
        vec![array_value(&initial)],
        &mut Observer::default(),
    );
    assert_eq!(bytes(&returned(&report).returns[0]), expected);
    assert_eq!(&returned(&report).returns, &ordinary.returns);
}

#[test]
fn observed_memcpy_preserves_overlap_ub_instead_of_returning_a_snapshot() {
    let report = run(
        &copy_program(false),
        vec![array_value(&[1, 2, 3, 4, 5, 6])],
        &mut Observer::default(),
    );
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError { site,error } if site.instruction_index == 5 && error.code == InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_zero_bulk_counts_do_not_dereference_null_pointers() {
    let module = module(
        vec![],
        vec![],
        vec![
            node(Inst::NullPtr, 0),
            constant(Ty::U64, 0, 1),
            constant(Ty::U8, 7, 2),
            void(Inst::MemCopy {
                dst: v(0),
                src: v(0),
                bytes: v(1),
                overlap: false,
            }),
            void(Inst::MemSet {
                dst: v(0),
                byte: v(2),
                bytes: v(1),
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    assert!(matches!(
        run(&module, vec![], &mut Observer::default()).exit(),
        ObservedExit::Returned(_)
    ));
}

#[test]
fn observed_memset_and_symbolic_u8_load_do_not_materialize_logical_length() {
    let n = 1u64 << 40;
    let ty = byte_array(n);
    let module = module(
        vec![],
        vec![Ty::U8],
        vec![
            node(
                Inst::Alloca {
                    ty: ty.clone(),
                    count: None,
                    align: None,
                },
                0,
            ),
            constant(Ty::U8, 73, 1),
            constant(Ty::U64, n as i128, 2),
            void(Inst::MemSet {
                dst: v(0),
                byte: v(1),
                bytes: v(2),
            }),
            node(
                Inst::Load {
                    ty,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                3,
            ),
            constant(Ty::U64, (n - 1) as i128, 4),
            node(
                Inst::ExtractElement {
                    ty: Ty::U8,
                    array: v(3),
                    index: v(4),
                },
                5,
            ),
            void(Inst::Return { values: vec![v(5)] }),
        ],
    );
    let mut observer = Observer::default();
    let report = run(&module, vec![], &mut observer);
    assert_eq!(returned(&report).returns, vec![int(Ty::U8, 73)]);
    assert!(observer.events.len() < 1000, "logical length became work");
    assert!(observer.events.iter().map(|e| e.copy_bytes).sum::<usize>() < 1_000_000);
}

#[test]
fn observed_bulk_copy_carries_uninitialized_bytes_to_strict_use_site() {
    let module = module(
        vec![],
        vec![Ty::U8],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                1,
            ),
            constant(Ty::U64, 1, 2),
            void(Inst::MemCopy {
                dst: v(1),
                src: v(0),
                bytes: v(2),
                overlap: false,
            }),
            node(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: v(1),
                    volatile: true,
                    align: None,
                },
                3,
            ),
            void(Inst::Return { values: vec![v(3)] }),
        ],
    );
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError { site,error } if site.instruction_index == 4 && error.code == InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_plain_partial_scalar_copy_store_retains_poison() {
    let module = module(
        vec![],
        vec![Ty::U8],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                0,
            ),
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                1,
            ),
            node(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                2,
            ),
            node(
                Inst::Copy {
                    ty: Ty::U8,
                    operand: v(2),
                },
                3,
            ),
            void(Inst::Store {
                ty: Ty::U8,
                ptr: v(1),
                value: v(3),
                volatile: false,
                align: None,
            }),
            node(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: v(1),
                    volatile: true,
                    align: None,
                },
                4,
            ),
            void(Inst::Return { values: vec![v(4)] }),
        ],
    );
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError { site,error } if site.instruction_index == 5 && error.code == InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_sparse_run_stop_cannot_publish_a_partial_memmove() {
    let mut observer = Observer {
        stop: Some((ExecutionPhase::SparseRun, 5)),
        ..Observer::default()
    };
    let report = run(
        &copy_program(true),
        vec![array_value(&[1, 2, 3, 4, 5, 6])],
        &mut observer,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
}

#[test]
fn observed_array_input_splat_insert_get_share_one_original_session() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let site = ExecutionSite::Entry(f());
    let n = u64::MAX;
    let array = ArrayValue::splat_observed(int(Ty::U8, 7), n, &mut session, site)
        .expect("structural splat");
    let next = array
        .set_observed(n - 1, int(Ty::U8, 9), &mut session, site)
        .expect("persistent insert");
    assert_eq!(
        next.get_observed(n - 1, &mut session, site)
            .expect("observed get"),
        Some(&int(Ty::U8, 9))
    );
    assert_eq!(
        array
            .get_observed(n - 1, &mut session, site)
            .expect("old root"),
        Some(&int(Ty::U8, 7))
    );
    InterpretValue {
        ty: byte_array(n),
        kind: InterpretValueKind::Array(next),
    }
    .retire_observed(&mut session, site)
    .expect("retire new");
    InterpretValue {
        ty: byte_array(n),
        kind: InterpretValueKind::Array(array),
    }
    .retire_observed(&mut session, site)
    .expect("retire old");
    assert!(session.first_refusal().is_none());
}

#[test]
fn observed_huge_array_argument_validation_uses_stored_structure() {
    let n = u64::MAX;
    let ty = byte_array(n);
    let module = module(
        vec![ty.clone()],
        vec![Ty::U8],
        vec![
            constant(Ty::U64, (n - 1) as i128, 1),
            node(
                Inst::ExtractElement {
                    ty: Ty::U8,
                    array: v(0),
                    index: v(1),
                },
                2,
            ),
            void(Inst::Return { values: vec![v(2)] }),
        ],
    );
    let array = InterpretValue {
        ty,
        kind: InterpretValueKind::Array(ArrayValue::splat(int(Ty::U8, 21), n)),
    };
    let mut observer = Observer::default();
    let report = run(&module, vec![array], &mut observer);
    assert_eq!(returned(&report).returns, vec![int(Ty::U8, 21)]);
    assert!(observer.events.len() < 500);
}

#[test]
fn observed_non_u8_array_memory_refuses_without_legacy_fallback() {
    let mut module = module(
        vec![byte_array(4)],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    module.types[0] = Ty::U16;
    assert!(matches!(
        run(
            &module,
            vec![array_value(&[1, 2, 3, 4])],
            &mut Observer::default()
        )
        .exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
}

#[test]
fn observed_volatile_store_refuses_partial_scalar_before_writing() {
    let module = module(
        vec![],
        vec![],
        vec![
            node(
                Inst::Alloca {
                    ty: Ty::U8,
                    count: None,
                    align: None,
                },
                0,
            ),
            node(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
                1,
            ),
            void(Inst::Store {
                ty: Ty::U8,
                ptr: v(0),
                value: v(1),
                volatile: true,
                align: None,
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError { site,error }
        if site.instruction_index == 2 && error.code == InterpretErrorCode::UndefinedBehavior)
    );
}

#[test]
fn observed_positive_signed_bulk_count_does_not_silently_change_semantics() {
    let module = module(
        vec![],
        vec![],
        vec![
            node(Inst::NullPtr, 0),
            constant(Ty::I64, 1, 1),
            void(Inst::MemCopy {
                dst: v(0),
                src: v(0),
                bytes: v(1),
                overlap: false,
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::ExecutedError { error,.. }
        if error.code == InterpretErrorCode::TypeError)
    );
}
