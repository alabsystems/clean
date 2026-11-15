// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn string_errors() -> NativeVerificationBundle {
    let mut bundle = fixture();
    // Exercise the real duplicate-id diagnostic and its owning cleanup at
    // every interruption point alongside the existing owned-string errors.
    bundle
        .module
        .proof_obligations
        .push(bundle.module.proof_obligations[0].clone());
    bundle.compiler_facts.obligation_sources[1].public_obligation_id =
        bundle.compiler_facts.obligation_sources[0]
            .public_obligation_id
            .clone();
    bundle.module.proof_obligations[0]
        .source
        .as_mut()
        .unwrap()
        .public
        .as_mut()
        .unwrap()
        .obligation_id = "different".into();
    bundle
}

#[test]
fn every_full_orchestration_callback_is_an_original_sticky_stop_with_owned_cleanup() {
    let bundle = string_errors();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    assert!(
        !bundle
            .compiler_fact_errors_observed(&mut session, site())
            .unwrap()
            .is_empty()
    );
    for (index, expected) in baseline.events.into_iter().enumerate() {
        let mut observer = Observer {
            stop_at: Some(index + 1),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            bundle.compiler_fact_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().progress, expected);
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert_eq!(
            bundle.compiler_fact_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert!(observer.events.iter().all(|event| event.site == site()));
        assert!(
            observer.events[index + 1..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn original_cumulative_work_and_requested_bytes_span_complete_constituent_calls() {
    let bundle = string_errors();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    bundle
        .compiler_fact_errors_observed(&mut session, site())
        .unwrap();
    for copy in [false, true] {
        let mut observer = if copy {
            Observer {
                byte_limit: Some(baseline.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(baseline.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let first = bundle
            .compiler_fact_errors_observed(&mut session, site())
            .unwrap();
        assert!(!first.is_empty());
        assert_eq!(
            bundle.compiler_fact_errors_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
    }
}

#[test]
fn component_retirement_refusal_prevents_later_facts_and_whole_result_publication() {
    let bundle = fixture();
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        bundle.compiler_fact_errors_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    let first = observer
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    assert!(
        observer.events[first..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn final_publication_refusal_retires_complete_owned_string_diagnostics() {
    let bundle = string_errors();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let result = bundle
        .compiler_fact_errors_observed(&mut session, site())
        .unwrap();
    assert!(
        result
            .iter()
            .any(|error| matches!(error, E::DuplicatePublicObligationSource { .. }))
    );
    assert!(
        result
            .iter()
            .any(|error| matches!(error, E::EmbeddedPublicObligationIdMismatch { .. }))
    );
    let last = baseline.events.len();
    assert_eq!(baseline.events[last - 1].phase, ExecutionPhase::Publication);
    let mut observer = Observer {
        stop_at: Some(last),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        bundle.compiler_fact_errors_observed(&mut session, site()),
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
    assert!(observer.events.len() > last + 4);
}

#[test]
fn string_storage_refusal_precedes_actual_public_diagnostic_allocation() {
    let mut observer = Observer {
        stop_at: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work::new(&mut session, site()).unwrap();
    let result = work.public_mismatch(
        NativeRequestId::new(0),
        ProofId::new(0),
        &"x".repeat(5000),
        "y",
        &mut session,
        site(),
    );
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    assert_eq!(work.first_text.capacity(), 0);
    assert!(work.first_text.is_empty());
    assert!(work.second_text.is_empty());
    assert!(work.pending.is_none());
    assert_eq!(
        work.finish(result, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}

#[test]
fn partial_expected_actual_and_pending_string_diagnostics_stay_owned_until_explicit_retirement() {
    let expected = "\u{3bb}".repeat(3000);
    let actual = "\u{1f980}".repeat(1600);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut work = Work::new(&mut session, site()).unwrap();
    work.public_mismatch(
        NativeRequestId::new(0),
        ProofId::new(0),
        &expected,
        &actual,
        &mut session,
        site(),
    )
    .unwrap();
    let (mut first, mut second, mut pending) = (false, false, false);
    for stop in 2..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work::new(&mut session, site()).unwrap();
        let result = work.public_mismatch(
            NativeRequestId::new(0),
            ProofId::new(0),
            &expected,
            &actual,
            &mut session,
            site(),
        );
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        first |= !work.first_text.is_empty();
        second |= !work.second_text.is_empty();
        pending |= matches!(&work.pending, Some(E::EmbeddedPublicObligationIdMismatch { expected: a, actual: b, .. }) if a == &expected && b == &actual);
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
    }
    assert!(first && second && pending);
}

#[test]
fn completed_owned_diagnostics_and_all_borrowed_maps_survive_a_later_source_join_refusal() {
    let bundle = string_errors();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    bundle
        .compiler_fact_errors_observed(&mut session, site())
        .unwrap();
    let mut witnessed = false;
    for stop in 3..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut work = Work::new(&mut session, site()).unwrap();
        admit(&mut session, site(), 1, size_of::<Scratch<'_>>()).unwrap();
        let mut scratch = Scratch::default();
        let result = scratch.run(&bundle, &mut work, &mut session, site());
        if result.is_err()
            && work
                .errors
                .iter()
                .any(|error| matches!(error, E::DuplicatePublicObligationSource { .. }))
            && !scratch.monos.is_empty()
            && !scratch.fats.is_empty()
        {
            witnessed = true;
        }
        scratch.retire(&mut session, site());
        assert!(
            scratch.functions.is_empty()
                && scratch.obligations.is_empty()
                && scratch.fats.is_empty()
                && scratch.monos.is_empty()
                && scratch.public_ids.is_empty()
                && scratch.source_facts.is_empty()
        );
        let finished = work.finish(result, &mut session, site());
        assert_eq!(finished, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
    }
    assert!(witnessed);
}

#[test]
fn actual_long_identity_scan_has_an_interior_bounded_character_stop() {
    let value = "\u{3bb}".repeat(3000);
    let mut observer = Observer {
        work_limit: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        text::identity(&value, false, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress.work, 8);
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(observer.events.len(), 14);
    assert!(observer.events.iter().all(|event| event.copy_bytes == 0));
}

#[test]
fn borrowed_string_index_growth_is_refused_before_allocation_and_replace_is_last_value() {
    let mut observer = Observer {
        stop_at: Some(2),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut rows: Vec<(&str, ProofId)> = Vec::new();
    assert_eq!(
        text_insert(&mut rows, "same", ProofId::new(0), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(rows.is_empty());
    assert_eq!(rows.capacity(), 0);
    let a = "\u{3bb}".repeat(3000);
    let b = "\u{3bb}".repeat(2999) + "x";
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut rows = Vec::new();
    let mut ordinary = BTreeMap::new();
    for (key, value) in [(&a, 0), (&b, 1), (&a, 2), (&a, 3)] {
        assert_eq!(
            text_insert(&mut rows, key, ProofId::new(value), &mut session, site()).unwrap(),
            ordinary.insert(key.as_str(), ProofId::new(value))
        );
    }
    retire_vec(&mut rows, &mut session, site());
}

#[test]
fn borrowed_inline_type_and_vector_value_walks_stop_inside_actual_nesting() {
    let mut ty = Ty::Error;
    for _ in 0..24 {
        ty = Ty::Tuple(vec![Ty::U32, Ty::PtrConst(Box::new(ty))]);
    }
    let mut value = Constant::Int(4);
    let mut value_ty = Ty::U8;
    for _ in 0..24 {
        value = Constant::Vector(vec![value]);
        value_ty = Ty::Vector(Box::new(value_ty), 1);
    }
    for constant in [false, true] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let result = if constant {
            types::constant_matches(&value, &value_ty, 64, &mut session, site())
        } else {
            types::contains_error(&ty, &mut session, site())
        };
        assert_eq!(result, Ok(true));
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let result = if constant {
                types::constant_matches(&value, &value_ty, 64, &mut session, site())
            } else {
                types::contains_error(&ty, &mut session, site())
            };
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        }
    }
}
