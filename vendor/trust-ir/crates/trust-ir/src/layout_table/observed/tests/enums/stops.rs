// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_enum_field_descriptor_inhabit_and_retirement_callback_is_terminal() {
    for module in [direct(), niche_graph()] {
        let mut measured = Observer::default();
        run(&module, &mut measured).unwrap().unwrap();
        for stop_at in 1..=measured.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = LayoutTable::new_observed(&module, &mut session, site())
                .and_then(|table| table.enum_layout_observed(EnumId::new(7), &mut session, site()));
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
}

#[test]
fn enum_requested_bytes_and_work_accumulate_in_the_same_session() {
    let module = niche_graph();
    let mut measured = Observer::default();
    run(&module, &mut measured).unwrap().unwrap();
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
            .enum_layout_observed(EnumId::new(7), &mut session, site())
            .unwrap()
            .unwrap();
        assert_eq!(
            *first,
            *LayoutTable::new(&module)
                .enum_layout(EnumId::new(7))
                .unwrap()
        );
        assert_eq!(
            table
                .enum_layout_observed(EnumId::new(7), &mut session, site())
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
fn discriminant_set_and_inhabit_frontier_are_refused_before_first_storage_growth() {
    let module = niche_graph();
    let table = LayoutTable::new(&module);
    let mut observer = Observer {
        byte_limit: Some(size_of::<Work<'_, '_, Observer>>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    assert!(matches!(
        super::super::super::enums::Frame::begin(&table, 0, &mut work),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    assert!(work.enums.is_empty() && work.cache.is_empty());
    work.retire_scratch();
    let mut observer = Observer {
        byte_limit: Some(size_of::<Work<'_, '_, Observer>>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    assert!(matches!(
        inhabit::some(
            &module,
            core::iter::once(&Ty::Enum(EnumId::new(8))),
            &mut work
        ),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    assert!(work.inhabitedness.is_empty());
    work.retire_scratch();
}

#[test]
fn final_enum_and_semantic_error_retirement_stops_override_pending_results() {
    for mut module in [direct(), niche_graph()] {
        for semantic_error in [false, true] {
            if semantic_error {
                module.target_info.as_mut().unwrap().triple = format!("i686-{}", "é".repeat(1300));
            }
            let mut measured = Observer::default();
            let outcome = run(&module, &mut measured).unwrap();
            assert_eq!(outcome.is_err(), semantic_error);
            let stop_at = measured
                .events
                .iter()
                .rposition(|event| event.phase == ExecutionPhase::ScratchRetirement)
                .unwrap()
                + 1;
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            assert_eq!(
                run(&module, &mut observer).unwrap_err(),
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
}

#[test]
fn inhabited_cycle_false_answer_has_interior_stops_and_cumulative_allowances() {
    let mut module = Module::new("observed_inhabited_cycle");
    module.structs.push(structure(
        3,
        vec![field("self", Ty::Struct(StructId::new(3)), None)],
        0,
        1,
    ));
    let ty = Ty::Struct(StructId::new(3));
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    assert!(
        !table
            .ty_is_uninhabited_observed(&ty, &mut session, site())
            .unwrap()
    );
    for stop_at in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = LayoutTable::new_observed(&module, &mut session, site())
            .and_then(|table| table.ty_is_uninhabited_observed(&ty, &mut session, site()));
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert!(
            observer
                .events
                .iter()
                .skip(stop_at)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
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
        assert!(
            !table
                .ty_is_uninhabited_observed(&ty, &mut session, site())
                .unwrap()
        );
        assert_eq!(
            table.ty_is_uninhabited_observed(&ty, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copying { "bytes" } else { "work" }
        );
    }
}
