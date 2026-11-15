// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn every_actual_collection_callback_refuses_without_returning_a_partial_vector() {
    for instruction in [
        frame(8),
        dialect(8),
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::F32,
            operand: v(),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            ptr: v(),
        },
        Inst::Undef { ty: Ty::U32 },
        Inst::NullPtr,
    ] {
        let (_, baseline) = observed(&instruction);
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert!(matches!(
                instruction.inline_types_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            ));
            assert_eq!(session.first_refusal().unwrap().cause, "original type stop");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop_at)
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_bytes_span_distinct_calls_in_the_same_original_session() {
    let a = frame(3);
    let b = dialect(4);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    a.inline_types_observed(&mut session, site()).unwrap();
    b.inline_types_observed(&mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            a.inline_types_observed(&mut session, site()).unwrap().len(),
            3
        );
        assert!(matches!(
            b.inline_types_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert!(matches!(
            a.inline_types_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
    }
}
#[test]
fn first_borrowed_header_reserve_refuses_before_any_output_allocation_or_push() {
    let ty = Ty::Tuple(vec![Ty::U32; 100]);
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut types = Vec::new();
    assert_eq!(
        work.push(&mut types, &ty),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((types.len(), types.capacity()), (0, 0));
    work.retire_types(&mut types);
    assert_eq!(work.session.first_refusal().unwrap().cause, "bytes");
}
#[test]
fn empty_slot_and_dialect_probe_admission_can_stop_before_final_publication() {
    for instruction in [frame(0), dialect(0)] {
        // Root header, fixed descriptor, index header, then actual probe.
        let mut observer = Observer {
            stop_at: Some(4),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            instruction.inline_types_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        let refusal = session.first_refusal().unwrap();
        assert_eq!(refusal.progress.copy_bytes, 2 * size_of::<&Ty>());
        assert_eq!(refusal.progress.phase, ExecutionPhase::Validation);
        assert!(
            observer
                .events
                .iter()
                .all(|event| event.phase != ExecutionPhase::Publication)
        );
    }
}
#[test]
fn completed_partial_headers_stay_owned_until_explicit_original_retirement() {
    for instruction in [frame(6), dialect(6)] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let mut work = Work {
            session: &mut session,
            site: site(),
        };
        let mut types = Vec::new();
        walk::collect(plan::for_instruction(&instruction), &mut types, &mut work).unwrap();
        work.retire_types(&mut types);
        let mut partial = false;
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let mut work = Work {
                session: &mut session,
                site: site(),
            };
            let mut types = Vec::new();
            let result = walk::collect(plan::for_instruction(&instruction), &mut types, &mut work);
            if result.is_err() && !types.is_empty() && types.len() < 6 {
                partial = true;
                for (actual, expected) in types.iter().zip(oracle::collect(&instruction)) {
                    assert!(core::ptr::eq(*actual, expected));
                }
            }
            work.retire_types(&mut types);
            assert_eq!((types.len(), types.capacity()), (0, 0));
        }
        assert!(partial);
    }
}
#[test]
fn final_publication_stop_retires_every_borrowed_header_and_the_buffer() {
    for instruction in [frame(9), dialect(9)] {
        let (_, baseline) = observed(&instruction);
        let mut observer = Observer {
            stop_at: Some(baseline.events.len()),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            instruction.inline_types_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        let cleanup = &observer.events[baseline.events.len()..];
        assert_eq!(cleanup.len(), 11);
        assert!(
            cleanup
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
        assert_eq!(oracle::collect(&instruction).len(), 9);
    }
}
#[test]
fn original_descriptor_retirement_refusal_cannot_publish_a_completed_vector() {
    let instruction = frame(4);
    let (_, baseline) = observed(&instruction);
    let stop_at = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        instruction.inline_types_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.phase != ExecutionPhase::Publication)
    );
    assert!(observer.events.len() >= stop_at + 7);
}
#[test]
fn wide_real_slot_and_dialect_scans_stop_interiorly_under_original_cumulative_work() {
    for instruction in [frame(5000), dialect(5000)] {
        let mut observer = Observer {
            work_cap: Some(300),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            instruction.inline_types_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(session.first_refusal().unwrap().cause, "work");
        assert!(observer.events.len() < 400);
        assert!(
            observer
                .events
                .iter()
                .all(|event| event.phase != ExecutionPhase::Publication)
        );
    }
}
