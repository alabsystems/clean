// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_actual_work_and_retirement_callback_keeps_original_stop_sticky() {
    let module = fixture();
    let ty = Ty::Struct(StructId::new(91));
    let mut measured = Observer::default();
    observed(&module, &ty, &mut measured).unwrap().unwrap();
    assert!(
        measured
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    for stop_at in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = LayoutTable::new_observed(&module, &mut session, site())
            .and_then(|table| table.ty_layout_observed(&ty, &mut session, site()));
        assert_eq!(
            result.unwrap_err(),
            ObservedValueError::AdmissionRefused,
            "event {stop_at}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            LayoutTable::new_observed(&module, &mut session, site()).unwrap_err(),
            ObservedValueError::AdmissionRefused
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop_at)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn repeated_queries_share_original_cumulative_work_and_requested_byte_limits() {
    let module = fixture();
    let ty = Ty::Struct(StructId::new(91));
    let mut measured = Observer::default();
    observed(&module, &ty, &mut measured).unwrap().unwrap();
    for copying in [false, true] {
        let mut observer = if copying {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
        let first = table
            .ty_layout_observed(&ty, &mut session, site())
            .unwrap()
            .unwrap();
        assert_eq!(*first, *LayoutTable::new(&module).ty_layout(&ty).unwrap());
        assert_eq!(
            table
                .ty_layout_observed(&ty, &mut session, site())
                .unwrap_err(),
            ObservedValueError::AdmissionRefused
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copying { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}

#[test]
fn storage_admission_precedes_empty_vector_growth_and_first_definition_insertion() {
    let mut observer = Observer {
        byte_limit: Some(size_of::<Work<'_, '_, Observer>>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    let mut rows: Vec<(u64, u64)> = Vec::new();
    assert!(matches!(
        work.reserve(&mut rows),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    assert_eq!((rows.len(), rows.capacity()), (0, 0));
    work.retire_scratch();
    let module = fixture();
    let table = LayoutTable::new(&module);
    let mut observer = Observer {
        byte_limit: Some(size_of::<Work<'_, '_, Observer>>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    assert!(matches!(
        work.walk(&table, &Ty::Struct(StructId::new(91))),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    assert!(work.definitions.is_empty() && work.cache.is_empty() && work.open.is_empty());
    work.retire_scratch();
}

#[test]
fn final_scratch_deallocation_refusal_blocks_an_already_computed_layout() {
    let module = fixture();
    let ty = Ty::Struct(StructId::new(91));
    let mut measured = Observer::default();
    observed(&module, &ty, &mut measured).unwrap().unwrap();
    let last_retirement = measured
        .events
        .iter()
        .rposition(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(last_retirement),
        ..Observer::default()
    };
    assert_eq!(
        observed(&module, &ty, &mut observer).unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
    assert!(
        observer
            .events
            .iter()
            .skip(last_retirement)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn tuple_and_closure_validation_interior_stops_never_return_partial_success() {
    let module = fixture();
    for closure in [false, true] {
        let table = LayoutTable::new(&module);
        let mut measured = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
        if closure {
            table
                .validate_closure_layouts_observed(&mut session, site())
                .unwrap()
                .unwrap();
        } else {
            table
                .validate_tuple_layouts_observed(&mut session, site())
                .unwrap()
                .unwrap();
        }
        for stop_at in [1, measured.events.len() / 2, measured.events.len()] {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = if closure {
                table.validate_closure_layouts_observed(&mut session, site())
            } else {
                table.validate_tuple_layouts_observed(&mut session, site())
            };
            assert_eq!(result.unwrap_err(), ObservedValueError::AdmissionRefused);
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
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
