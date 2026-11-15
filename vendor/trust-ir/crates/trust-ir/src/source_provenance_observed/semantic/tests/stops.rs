// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_unique_projection_hash_and_semantic_error_callback_refuses() {
    for id in [FuncId::new(151), FuncId::new(u32::MAX)] {
        let m = module();
        let (_, baseline) = run(&m, id);
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                m.source_provenance_semantic_digest_observed(id, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                "original source semantic stop"
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_are_not_reset_by_the_projection_or_final_seal() {
    let m = module();
    let id = FuncId::new(151);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for _ in 0..2 {
        assert!(
            m.source_provenance_semantic_digest_observed(id, &mut session, site())
                .unwrap()
                .is_ok()
        );
    }
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work - 1),
            byte_cap: bytes.then_some(baseline.bytes - 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            m.source_provenance_semantic_digest_observed(id, &mut session, site())
                .unwrap()
                .is_ok()
        );
        assert_eq!(
            m.source_provenance_semantic_digest_observed(id, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = session.first_refusal().unwrap().progress;
        assert_eq!(
            m.source_provenance_semantic_digest_observed(id, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn actual_full_uniqueness_scan_does_not_stop_at_the_first_target_or_duplicate() {
    let mut m = module();
    m.functions[0].id = FuncId::new(151);
    m.functions.extend((0..5000).map(|_| function(17, "tail")));
    let mut observer = Observer {
        work_cap: Some(1000),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(FuncId::new(151), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
}
#[test]
fn original_semantic_error_string_is_retained_across_final_publication_refusal() {
    let m = module();
    let id = FuncId::new(u32::MAX);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::new(),
    };
    let mut state = State::default();
    assert_eq!(state.identity(&m, id, &mut writer), Ok(None));
    assert_eq!(
        state.error,
        "source provenance target function #4294967295 is missing or duplicated"
    );
    writer.retire();
    writer.publication().unwrap();
    state.retire(&mut writer);
    let stop = baseline
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::Publication)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(id, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(observer.events.len() > stop);
    assert!(
        observer
            .events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn original_cleanup_and_initial_header_refusals_never_return_an_identity_or_error_string() {
    let m = module();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(FuncId::new(151), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    let arm = Rc::new(Cell::new(true));
    let mut observer = Observer {
        cleanup: Some(arm),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(FuncId::new(151), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original source semantic cleanup"
    );
}
#[test]
fn unsupported_actual_wire_construct_refuses_without_ordinary_fallback() {
    let mut m = module();
    m.types.push(Ty::Error);
    // An actual poison type is deliberately unsupported by the actual
    // observed wire emitter. No whole-module clone/ordinary hashing may rescue it.
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(FuncId::new(151), &mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    assert!(
        observer
            .events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn internal_projection_out_of_range_refuses_and_retires_collector_without_a_digest() {
    let m = module();
    for (index, error) in [
        (m.functions.len(), ObservedValueError::InvalidRange),
        (usize::MAX, ObservedValueError::CapacityOverflow),
    ] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            crate::binary::observed_source_function_identity(&m, index, &mut session, site()),
            Err(error)
        );
        assert!(
            observer
                .events
                .iter()
                .any(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
