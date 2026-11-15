// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn observed_missing_function_is_entry_rejection_not_an_executed_fault() {
    let module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        FuncId::new(9),
        vec![],
        &mut session,
    );
    assert!(
        matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code == InterpretErrorCode::MissingFunction)
    );
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_fallback_function_scan_polls_each_examined_row() {
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    module.functions[0].id = FuncId::new(9);
    let mut observer = Observer {
        stop: Some((ExecutionPhase::ModuleLookup, 2)),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = Interpreter::with_module(&module).execute_func_observed(
        FuncId::new(9),
        vec![],
        &mut session,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_unused_signature_abi_scan_can_stop_before_first_instruction() {
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    for _ in 0..32 {
        module
            .func_types
            .push(FuncTy::unrecorded(vec![], vec![], false));
    }
    let mut observer = Observer {
        stop: Some((ExecutionPhase::AbiScan, 17)),
        ..Observer::default()
    };
    let report = run(&module, vec![], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_typed_abi_presence_refuses_instead_of_using_legacy_dispatch() {
    use crate::signature_abi::*;
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    let mut unused = FuncTy::unrecorded(vec![], vec![], false);
    unused.abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: "aarch64-unknown-linux-gnu".into(),
            data_layout: String::new(),
            abi: String::new(),
            cpu: String::new(),
            features: vec![],
            target_spec: String::new(),
            pointer_bytes: 8,
            little_endian: true,
        },
        frontend: AbiFrontend {
            name: "test".into(),
            revision: "test".into(),
        },
        convention: "C".into(),
        lowered_convention: crate::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: false,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    });
    module.func_types.push(unused);
    let report = run(&module, vec![], &mut Observer::default());
    assert!(
        matches!(report.exit(),ObservedExit::EntryRejected(error) if error.code == InterpretErrorCode::UnsupportedCall)
    );
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_target_triple_scan_has_interior_layout_poll() {
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    module.target_info = Some(crate::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: crate::StructPassingPolicy::default(),
    });
    let mut observer = Observer {
        stop: Some((ExecutionPhase::Layout, 4)),
        ..Observer::default()
    };
    assert!(matches!(
        run(&module, vec![], &mut observer).exit(),
        ObservedExit::AdmissionRefused
    ));
}

#[test]
fn observed_nonreference_target_is_unsupported_not_a_rust_refutation() {
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    module.target_info = Some(crate::TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: crate::StructPassingPolicy::default(),
    });
    assert!(matches!(
        run(&module, vec![], &mut Observer::default()).exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
}

#[test]
fn observed_drop_table_inline_types_are_polled_before_argument_binding() {
    let mut module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    module.drop_glue.push(crate::DropGlueEntry {
        glue: FuncId::new(3),
        ty: Ty::Tuple(vec![Ty::U8; 64]),
    });
    let mut observer = Observer {
        stop: Some((ExecutionPhase::DropGlueIndex, 19)),
        ..Observer::default()
    };
    let report = run(&module, vec![], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_entry_handle_or_malformed_scalar_never_becomes_executed_panic() {
    let module = module(
        vec![Ty::U8],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let malformed = InterpretValue {
        ty: Ty::U8,
        kind: InterpretValueKind::Int(InterpretInt {
            bits: 8,
            signed: false,
            raw: 256,
        }),
    };
    assert!(matches!(
        run(&module, vec![malformed], &mut Observer::default()).exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
}

#[test]
fn observed_array_argument_checks_each_retained_literal_not_logical_extent() {
    let array_ty = Ty::Array(TyId::new(0), 64);
    let module = module(
        vec![array_ty.clone()],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let array = ArrayValue::from_vec((0..64).map(|n| int(Ty::U8, n)).collect());
    let mut observer = Observer {
        stop: Some((ExecutionPhase::EntryArguments, 19)),
        ..Observer::default()
    };
    let report = run(
        &module,
        vec![InterpretValue {
            ty: array_ty,
            kind: InterpretValueKind::Array(array),
        }],
        &mut observer,
    );
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_block_parameter_debit_refusal_does_not_reset_original_owner() {
    let module = module(
        vec![Ty::U8],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let mut observer = Observer {
        stop: Some((ExecutionPhase::BlockParameters, 2)),
        ..Observer::default()
    };
    let report = run(&module, vec![int(Ty::U8, 7)], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_drop_instruction_never_silently_runs_as_noop() {
    let module = module(
        vec![],
        vec![],
        vec![
            node(Inst::NullPtr, 0),
            void(Inst::Drop {
                ty: Ty::U8,
                ptr: v(0),
            }),
            void(Inst::Return { values: vec![] }),
        ],
    );
    assert!(matches!(
        run(&module, vec![], &mut Observer::default()).exit(),
        ObservedExit::UnsupportedObservation {
            site: ExecutionSite::Instruction(InstructionSite {
                instruction_index: 1,
                ..
            }),
            ..
        }
    ));
}

#[test]
fn observed_options_cannot_change_or_replenish_the_captured_session() {
    let module = module(vec![], vec![], vec![void(Inst::Return { values: vec![] })]);
    let mut observer = Observer::default();
    let original = InterpretOptions {
        fuel: 1,
        ..InterpretOptions::default()
    };
    let mut session = ObservedSession::new(original, &mut observer);
    assert!(matches!(
        Interpreter::with_module(&module)
            .execute_func_observed(f(), vec![], &mut session)
            .exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
    assert_eq!(session.remaining_fuel(), 1);
}

#[test]
fn observed_deep_rejected_inline_type_retires_without_recursive_drop_or_new_stack() {
    let module = module(
        vec![Ty::Unit],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let mut ty = Ty::U8;
    for _ in 0..20_000 {
        ty = Ty::Tuple(vec![Ty::U8, Ty::Ref(Box::new(ty))]);
    }
    let value = InterpretValue {
        ty,
        kind: InterpretValueKind::Unit,
    };
    let report = run(&module, vec![value], &mut Observer::default());
    assert!(matches!(
        report.exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_deep_rejected_mixed_value_tree_uses_existing_owned_slots_for_cleanup() {
    let module = module(
        vec![Ty::Unit],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let mut value = InterpretValue::bool(false);
    for index in 0..10_000 {
        value = InterpretValue {
            ty: Ty::Unit,
            kind: match index % 3 {
                0 => InterpretValueKind::Aggregate(vec![int(Ty::U8, 1), value]),
                1 => InterpretValueKind::Record(vec![("kept".into(), value)]),
                _ => InterpretValueKind::FatPtr {
                    data: Box::new(value),
                    metadata: Box::new(int(Ty::U64, 0)),
                },
            },
        };
    }
    let mut observer = Observer {
        stop: Some((ExecutionPhase::EntryArguments, 1)),
        ..Observer::default()
    };
    let report = run(&module, vec![value], &mut observer);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(report.steps(), 0);
}

#[test]
fn observed_unique_nested_frames_are_rejected_and_drained_without_new_grant() {
    let module = module(
        vec![Ty::Ptr],
        vec![],
        vec![void(Inst::Return { values: vec![] })],
    );
    let mut value = InterpretValue::bool(false);
    for index in 0..10_000 {
        value = InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::Frame {
                lineage: index,
                slots: Arc::from(vec![Some(value)]),
            },
        };
    }
    let report = run(&module, vec![value], &mut Observer::default());
    assert!(matches!(
        report.exit(),
        ObservedExit::UnsupportedObservation { .. }
    ));
    assert_eq!(report.steps(), 0);
}
