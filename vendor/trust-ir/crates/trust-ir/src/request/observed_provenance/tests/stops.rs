// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_function_traversal_copy_and_publication_stop_is_terminal() {
    let provenance = provenance(&[]);
    let module = module(&[
        Some(Producer::Other("aλ🦀".repeat(350))),
        None,
        Some(Producer::Other("aλ🦀".repeat(350))),
    ]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    provenance
        .uncovered_functions_observed(&module, &mut session, site())
        .unwrap();
    let events = baseline.events;
    assert!(events.len() > 20);
    for (index, expected) in events.into_iter().enumerate() {
        let mut observer = Observer {
            stop_at: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            provenance.uncovered_functions_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "stop {}",
            index + 1
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            provenance.uncovered_imports_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
    }
}

#[test]
fn every_import_name_producer_copy_and_publication_stop_is_terminal() {
    let provenance = provenance(&[]);
    let mut module = module(&[Some(Producer::Other("🦀".repeat(700))), None]);
    module.imports[0].name = "name-λ".repeat(500);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    provenance
        .uncovered_imports_observed(&module, &mut session, site())
        .unwrap();
    let events = baseline.events;
    assert!(events.len() > 20);
    for (index, expected) in events.into_iter().enumerate() {
        let mut observer = Observer {
            stop_at: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            provenance.uncovered_imports_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "stop {}",
            index + 1
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            provenance.uncovered_functions_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
    }
}

#[test]
fn actual_vector_reservation_is_refused_before_storage_changes() {
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut values: FunctionRows = Vec::new();
    assert_eq!(
        reserve(&mut values, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values.capacity(), 0);
    assert!(values.is_empty());
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn existing_vector_growth_is_refused_before_moving_retained_rows() {
    let mut values: FunctionRows = Vec::with_capacity(1);
    values.push((
        Some(Producer::Other("retained".into())),
        vec![FuncId::new(5)],
    ));
    let capacity = values.capacity();
    let pointer = values.as_ptr();
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        reserve(&mut values, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values.capacity(), capacity);
    assert_eq!(values.as_ptr(), pointer);
    assert_eq!(values[0].1, [FuncId::new(5)]);
}

#[test]
fn partial_string_storage_retirement_retains_original_refusal() {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    assert_eq!(
        copy_text(&"λ".repeat(2500), &mut session, site())
            .unwrap()
            .len(),
        5000
    );
    let second_copy = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.copy_bytes == 1024)
        .nth(2)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop_at: Some(second_copy),
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        copy_text(&"λ".repeat(2500), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn pending_other_is_retained_when_nested_id_storage_refuses_then_explicitly_retired() {
    let producer = Producer::Other("z".repeat(3000));
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = Functions::default();
    state
        .function(Some(&producer), FuncId::new(6), &mut session, site())
        .unwrap();
    let storage = baseline
        .events
        .iter()
        .position(|event| event.copy_bytes == size_of::<FuncId>())
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(storage),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = Functions::default();
    let result = state.function(Some(&producer), FuncId::new(6), &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.pending_producer.as_ref(), Some(&producer));
    assert!(state.pending_ids.is_empty() && state.rows.is_empty());
    assert_eq!(
        state.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer.events[storage..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > storage + 4);
}

#[test]
fn pending_import_name_is_retained_on_producer_refusal_then_explicitly_retired() {
    let mut module = module(&[Some(Producer::Other("producer".into()))]);
    module.imports[0].name = "name-λ".repeat(800);
    let provenance = provenance(&[]);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = Imports::default();
    state
        .scan(&provenance, &module, &mut session, site())
        .unwrap();
    // String and Option<Producer> headers can have the same size. Locate the
    // completed actual name-copy sequence, then stop at the producer header.
    let mut name_observer = Observer::default();
    let mut name_session = ObservedSession::new(InterpretOptions::default(), &mut name_observer);
    assert_eq!(
        copy_text(&module.imports[0].name, &mut name_session, site()).unwrap(),
        module.imports[0].name
    );
    let name_start = baseline
        .events
        .windows(name_observer.events.len())
        .position(|events| events == name_observer.events)
        .unwrap();
    let producer_index = name_start + name_observer.events.len();
    assert_eq!(
        baseline.events[producer_index].phase,
        ExecutionPhase::Validation
    );
    assert_eq!(baseline.events[producer_index].work, 1);
    assert_eq!(
        baseline.events[producer_index].copy_bytes,
        size_of::<Option<Producer>>()
    );
    let producer_copy = producer_index + 1;
    let mut observer = Observer {
        stop_at: Some(producer_copy),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = Imports::default();
    let result = state.scan(&provenance, &module, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(state.pending_name, module.imports[0].name);
    assert!(state.pending_producer.is_none() && state.rows.is_empty());
    assert_eq!(
        state.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer.events[producer_copy..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > producer_copy + 4);
}

#[test]
fn retirement_refusal_cannot_publish_completed_nested_function_diagnostics() {
    let provenance = provenance(&[]);
    let module = long_module();
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        provenance.uncovered_functions_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    assert!(
        observer
            .events
            .iter()
            .filter(|event| event.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 20
    );
    assert!(
        !observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::Publication)
    );
}

#[test]
fn retirement_refusal_cannot_publish_completed_import_names_and_producers() {
    let provenance = provenance(&[]);
    let module = long_module();
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        provenance.uncovered_imports_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    assert!(
        observer
            .events
            .iter()
            .filter(|event| event.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 20
    );
    assert!(
        !observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::Publication)
    );
}

#[test]
fn publication_refusal_retires_rows_without_replacing_first_cause() {
    let provenance = provenance(&[]);
    let module = long_module();
    for import in [false, true] {
        let mut observer = Observer {
            stop_publication: true,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        if import {
            assert_eq!(
                provenance.uncovered_imports_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        } else {
            assert_eq!(
                provenance.uncovered_functions_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
        }
        assert_eq!(session.first_refusal().unwrap().cause, "publication");
        let publication = observer
            .events
            .iter()
            .position(|event| event.phase == ExecutionPhase::Publication)
            .unwrap();
        assert!(
            observer.events[publication + 1..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
        assert!(observer.events.len() > publication + 4);
    }
}

#[test]
fn cumulative_work_and_copy_caps_refuse_long_actual_data() {
    let provenance = provenance(&[]);
    let module = long_module();
    for import in [false, true] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        if import {
            provenance
                .uncovered_imports_observed(&module, &mut session, site())
                .unwrap();
        } else {
            provenance
                .uncovered_functions_observed(&module, &mut session, site())
                .unwrap();
        }
        assert!(baseline.work > 1000 && baseline.bytes > 1000);
        for bytes in [false, true] {
            let mut observer = if bytes {
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
            if import {
                assert_eq!(
                    provenance.uncovered_imports_observed(&module, &mut session, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
            } else {
                assert_eq!(
                    provenance.uncovered_functions_observed(&module, &mut session, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
            }
            assert_eq!(
                session.first_refusal().unwrap().cause,
                if bytes { "bytes" } else { "work" }
            );
        }
    }
}

#[test]
fn long_exact_other_comparison_can_stop_inside_a_later_chunk() {
    let value = Producer::Other("🦀".repeat(2000));
    let mut observer = Observer {
        work_limit: Some(4099),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        producer_equal(Some(&value), Some(&value), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(session.first_refusal().unwrap().progress.work, 2048);
    assert!(observer.events.len() > 3);
}
