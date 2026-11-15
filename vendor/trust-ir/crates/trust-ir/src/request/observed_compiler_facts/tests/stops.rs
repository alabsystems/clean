// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_layout_name_tag_tree_and_publication_stop_is_terminal() {
    let module = module();
    let structure = structure(&module);
    let enumeration = enumeration(&module);
    let fat = fat();
    for case in [Case::Struct, Case::Enum, Case::EnumHelper, Case::Fat] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        run(&module, &structure, &enumeration, &fat, case, &mut session).unwrap();
        for (index, expected) in baseline.events.into_iter().enumerate() {
            let mut observer = Observer {
                stop_at: Some(index + 1),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                run(&module, &structure, &enumeration, &fat, case, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, expected);
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(
                fat.validation_errors_observed(&module, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}

#[test]
fn first_fixed_key_tree_and_error_vector_growth_refuse_before_allocation() {
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut values = BTreeSet::<i128>::new();
    assert_eq!(
        set_insert(&mut values, 9, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(values.is_empty());
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut errors = Vec::<E>::new();
    assert_eq!(
        reserve(&mut errors, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(errors.capacity(), 0);
}

#[test]
fn owned_expected_layout_stays_retained_after_later_name_comparison_refusal() {
    let module = module();
    let fact = structure(&module);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    let mut work = Work::new(&mut session, site()).unwrap();
    work.adt(&table, &fact, &mut session, site()).unwrap();
    let stop = baseline
        .events
        .iter()
        .position(|event| {
            event.phase == ExecutionPhase::Validation && event.work == 2048 && event.copy_bytes == 0
        })
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    let mut work = Work::new(&mut session, site()).unwrap();
    let result = work.adt(&table, &fact, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(work.layout.is_some());
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
    assert!(observer.events.len() > stop + 8);
}

#[test]
fn pending_fixed_diagnostic_is_retained_when_result_vector_storage_refuses() {
    let module = module();
    let mut fact = fat();
    fact.layout.data_bits = 32;
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    fact.validation_errors_observed(&module, &mut session, site())
        .unwrap();
    let storage = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.work == 1 && event.copy_bytes == size_of::<E>())
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut observer = Observer {
        stop_at: Some(storage),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    // Match the public fixed pointer-shape admission before entering invalid.
    admit(
        &mut session,
        site(),
        32,
        size_of::<Option<PointerLayoutShape>>(),
    )
    .unwrap();
    let result = work.invalid(
        NativeCompilerFactRef::FatPointer(fact.id),
        "layout",
        &mut session,
        site(),
    );
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(work.pending.is_some() && work.errors.is_empty());
    assert_eq!(
        work.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
}

#[test]
fn final_retirement_and_publication_refusals_cannot_publish_completed_diagnostics() {
    let module = module();
    let structure = structure(&module);
    let mut enumeration = enumeration(&module);
    enumeration.enum_layout.as_mut().unwrap().tag_bits = Some(0);
    let mut fat = fat();
    fat.layout.data_bits = 32;
    for case in [Case::Struct, Case::Enum, Case::EnumHelper, Case::Fat] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        run(&module, &structure, &enumeration, &fat, case, &mut session).unwrap();
        let last = baseline.events.len();
        assert_eq!(baseline.events[last - 1].phase, ExecutionPhase::Publication);
        for stop in [Some(last), None] {
            let mut observer = Observer {
                stop_at: stop,
                stop_retirement: stop.is_none(),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                run(&module, &structure, &enumeration, &fat, case, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(
                session.first_refusal().unwrap().cause,
                if stop.is_none() {
                    "retirement"
                } else {
                    "interior"
                }
            );
        }
    }
}

#[test]
fn original_cumulative_work_and_copy_caps_cover_repeated_facts_without_renewal() {
    let module = module();
    let structure = structure(&module);
    let enumeration = enumeration(&module);
    let mut fat = fat();
    fat.layout.data_bits = 32;
    let cases = [Case::Struct, Case::Enum, Case::Fat];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for case in cases {
        run(&module, &structure, &enumeration, &fat, case, &mut session).unwrap();
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
        run(
            &module,
            &structure,
            &enumeration,
            &fat,
            Case::Struct,
            &mut session,
        )
        .unwrap();
        run(
            &module,
            &structure,
            &enumeration,
            &fat,
            Case::Enum,
            &mut session,
        )
        .unwrap();
        assert_eq!(
            run(
                &module,
                &structure,
                &enumeration,
                &fat,
                Case::Fat,
                &mut session
            ),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
    }
}

#[test]
fn later_duplicate_definitions_remain_outside_first_definition_fact_lookup() {
    let mut module = module();
    let fact = enumeration(&module);
    let mut duplicate = module.enums[0].clone();
    duplicate.variants.clear();
    module.enums.push(duplicate);
    assert_eq!(adt(&module, &fact), ordinary_adt(&module, &fact));
}
