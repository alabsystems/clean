// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_primitive_lookup_type_clone_equality_layout_and_publication_stop_is_terminal() {
    let mut f = fixture();
    let ty = Ty::PtrConst(Box::new(Ty::Tuple(vec![
        Ty::U32,
        Ty::Tuple(vec![Ty::Char]),
    ])));
    f.module.functions[0].blocks[0].params[0].1 = ty.clone();
    f.pointer.base_ty = ty;
    for mode in [
        Mode::Pointer,
        Mode::PointerValues,
        Mode::Cast,
        Mode::CastResult,
        Mode::Metadata,
        Mode::Upcast,
    ] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        invoke(&f, mode, &mut session).unwrap();
        for (index, expected) in baseline.events.into_iter().enumerate() {
            let mut observer = Observer {
                stop_at: Some(index + 1),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                invoke(&f, mode, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, expected);
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(
                f.metadata.upcast_errors_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
        }
    }
}

#[test]
fn owned_cloned_value_type_remains_custodied_after_later_structural_comparison_refusal() {
    let mut f = fixture();
    let ty = Ty::PtrConst(Box::new(Ty::Tuple(vec![
        Ty::Char,
        Ty::Tuple(vec![Ty::U32]),
    ])));
    f.module.functions[0].blocks[0].params[0].1 = ty.clone();
    f.pointer.base_ty = ty;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work::new(&mut session, site()).unwrap();
    work.pointer_values(&f.module, &f.pointer, &mut session, site())
        .unwrap();
    let publication = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::Publication)
        .unwrap();
    let stop = publication + 2;
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    let result = work.pointer_values(&f.module, &f.pointer, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(work.owned_ty.is_some());
    assert_eq!(
        work.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer.events[stop..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > stop + 5);
}

#[test]
fn owned_type_retirement_refusal_stops_before_next_value_without_renewal() {
    let f = fixture();
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        invoke(&f, Mode::PointerValues, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
}

#[test]
fn final_publication_refusal_retires_all_primitive_pending_results() {
    let mut f = fixture();
    f.functions.clear();
    f.obligations.clear();
    f.cast.evidence = CastLayoutEvidence::NotLayoutSensitive;
    for mode in [
        Mode::Pointer,
        Mode::PointerValues,
        Mode::Cast,
        Mode::CastResult,
        Mode::Metadata,
        Mode::Upcast,
    ] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        invoke(&f, mode, &mut session).unwrap();
        let last = baseline.events.len();
        assert_eq!(baseline.events[last - 1].phase, ExecutionPhase::Publication);
        let mut observer = Observer {
            stop_at: Some(last),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            invoke(&f, mode, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
        assert!(
            observer.events[last..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn original_cumulative_work_and_copy_limits_span_pointer_cast_and_metadata_calls() {
    let mut f = fixture();
    f.functions.clear();
    let modes = [Mode::Pointer, Mode::Cast, Mode::Metadata];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for mode in modes {
        invoke(&f, mode, &mut session).unwrap();
    }
    for copy in [false, true] {
        let mut observer = if copy {
            Observer {
                byte_limit: Some(baseline.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(baseline.work - 1),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        invoke(&f, Mode::Pointer, &mut session).unwrap();
        invoke(&f, Mode::Cast, &mut session).unwrap();
        assert_eq!(
            invoke(&f, Mode::Metadata, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
    }
}

#[test]
fn actual_shared_unicode_blank_scan_stops_inside_input_without_a_final_string_comparison() {
    let value = "\u{2003}".repeat(1000);
    let mut observer = Observer {
        work_limit: Some(80),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        blank(&value, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(session.first_refusal().unwrap().progress.work, 8);
    assert_eq!(observer.events.len(), 11);
    assert!(
        observer
            .events
            .iter()
            .all(|event| event.work == 8 && event.copy_bytes == 0)
    );
}

#[test]
fn unsupported_detail_and_metadata_symbol_scans_keep_the_original_session_budget() {
    let mut f = fixture();
    f.pointer.provenance = NativePointerOffsetProvenance::Unsupported(NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::Other,
        "\u{2003}".repeat(1000),
    ));
    f.metadata.vtable_symbol = "\u{2003}".repeat(1000);
    for mode in [Mode::Pointer, Mode::Metadata] {
        let mut observer = Observer {
            work_limit: Some(400),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            invoke(&f, mode, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "work");
    }
}

#[test]
fn newly_owned_function_and_obligation_diagnostics_survive_reservation_refusal_until_retirement() {
    for obligation in [false, true] {
        let mut observer = Observer {
            stop_at: Some(3),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work::new(&mut session, site()).unwrap();
        let fact = NativeCompilerFactRef::PointerOffset(NativeCompilerFactId::new(4));
        let result = if obligation {
            work.fixed_error(
                || E::UnknownCompilerFactObligation {
                    fact,
                    obligation: ProofId::new(8),
                },
                &mut session,
                site(),
            )
        } else {
            work.unknown_function(fact, FuncId::new(7), &mut session, site())
        };
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert!(work.errors.is_empty());
        assert!(if obligation {
            matches!(&work.pending, Some(E::UnknownCompilerFactObligation { .. }))
        } else {
            matches!(&work.pending, Some(E::UnknownCompilerFactFunction { .. }))
        });
        assert_eq!(
            work.finish(result, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert!(
            observer.events[3..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
        assert!(observer.events.len() > 3);
    }
}
