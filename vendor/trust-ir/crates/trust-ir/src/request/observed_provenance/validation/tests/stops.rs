// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_component_event_refusal_keeps_original_cause_and_cannot_publish_output() {
    let bundle = fixture();
    for case in [Case::Provenance, Case::Serialization, Case::Diagnostics] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        run(&bundle, case, &mut session).unwrap();
        for (index, progress) in baseline.events.into_iter().enumerate() {
            let mut observer = Observer {
                stop_at: Some(index + 1),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                run(&bundle, case, &mut session),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, progress);
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(
                bundle.diagnostics_policy_errors_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}

#[test]
fn actual_owned_row_reversal_is_admitted_before_any_swap() {
    let mut values = vec![
        (Some(Producer::Other("first".into())), vec![FuncId::new(7)]),
        (Some(Producer::Other("last".into())), vec![FuncId::new(1)]),
    ];
    let before = values.clone();
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        reverse(&mut values, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values, before);
}

#[test]
fn language_set_reservation_refuses_before_any_tree_insertion() {
    let mut state = Checking {
        pending: Some(E::BundlePrimaryLanguageUncovered {
            primary: NativeSourceLanguage::Rust,
            source_languages: BTreeSet::new(),
        }),
        ..Checking::default()
    };
    let source = BTreeSet::from([NativeSourceLanguage::Lean, NativeSourceLanguage::Swift]);
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let result = state.language_set(&source, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(
        matches!(&state.pending, Some(E::BundlePrimaryLanguageUncovered { source_languages, .. }) if source_languages.is_empty())
    );
    assert_eq!(
        state.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}

fn second_insertion_stop(bundle: &NativeVerificationBundle, occurrence: usize) -> usize {
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = Checking::default();
    state.provenance(bundle, &mut session, site()).unwrap();
    let cost = observed_btree::insertion_cost::<NativeSourceLanguage, ()>(1).unwrap();
    baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| event.work == cost.work && event.copy_bytes == cost.copy_bytes)
        .nth(occurrence)
        .unwrap()
        .0
        + 1
}

#[test]
fn partial_function_diagnostic_keeps_remaining_rows_and_other_strings_until_retirement() {
    let bundle = fixture();
    let stop = second_insertion_stop(&bundle, 1);
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = Checking::default();
    let result = state.provenance(&bundle, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(
        matches!(&state.pending, Some(E::BundleLanguageUncovered { functions, source_languages, .. })
                    if !functions.is_empty() && source_languages.len() == 1)
    );
    assert_eq!(state.functions.len(), 1);
    assert!(matches!(&state.functions[0].0, Some(Producer::Other(_))));
    assert!(!state.errors.is_empty());
    assert_eq!(
        state.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer.events[stop..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > stop + 20);
}

#[test]
fn partial_import_diagnostic_keeps_name_producer_and_remaining_rows_until_retirement() {
    let bundle = fixture();
    let stop = second_insertion_stop(&bundle, 3);
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = Checking::default();
    let result = state.provenance(&bundle, &mut session, site());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert!(
        matches!(&state.pending, Some(E::BundleImportLanguageUncovered { name, producer: Some(Producer::Other(_)), source_languages, .. })
                    if !name.is_empty() && source_languages.len() == 1)
    );
    assert_eq!(state.imports.len(), 1);
    assert!(!state.errors.is_empty());
    assert_eq!(
        state.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(
        observer.events[stop..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(observer.events.len() > stop + 20);
}

#[test]
fn nested_cleanup_refusal_never_replaces_an_earlier_original_refusal() {
    let bundle = fixture();
    let mut observer = Observer {
        stop_at: Some(1),
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut state = Checking::default();
    let result = state.provenance(&bundle, &mut session, site());
    assert_eq!(
        state.finish(result, &mut session, site()),
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
fn retirement_refusal_cannot_publish_any_component_result() {
    let bundle = fixture();
    for case in [Case::Provenance, Case::Serialization, Case::Diagnostics] {
        let mut observer = Observer {
            stop_retirement: true,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            run(&bundle, case, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "retirement");
        assert!(
            observer
                .events
                .iter()
                .filter(|event| event.phase == ExecutionPhase::ScratchRetirement)
                .count()
                > 2
        );
    }
}

#[test]
fn final_publication_refusal_retires_all_completed_variable_diagnostics() {
    let bundle = fixture();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    run(&bundle, Case::Provenance, &mut session).unwrap();
    let last = baseline.events.len();
    assert_eq!(baseline.events[last - 1].phase, ExecutionPhase::Publication);
    let mut observer = Observer {
        stop_at: Some(last),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        run(&bundle, Case::Provenance, &mut session),
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
    assert!(observer.events.len() > last + 30);
}

#[test]
fn cumulative_work_and_copy_caps_apply_across_all_three_components_in_one_session() {
    let bundle = fixture();
    let cases = [Case::Provenance, Case::Serialization, Case::Diagnostics];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for case in cases {
        run(&bundle, case, &mut session).unwrap();
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
        run(&bundle, Case::Provenance, &mut session).unwrap();
        run(&bundle, Case::Serialization, &mut session).unwrap();
        assert_eq!(
            run(&bundle, Case::Diagnostics, &mut session),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}

#[test]
fn unicode_whitespace_scan_can_refuse_inside_the_original_long_string() {
    let mut observer = Observer {
        work_limit: Some(80),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        blank(&"\u{2003}".repeat(10000), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    // Keep the original80 allowance: one whole64 scalar fits, the next refuses.
    assert_eq!(session.first_refusal().unwrap().progress.work, 64);
    assert_eq!(
        observer.events.iter().map(|p| p.work).collect::<Vec<_>>(),
        vec![64, 64]
    );
}
