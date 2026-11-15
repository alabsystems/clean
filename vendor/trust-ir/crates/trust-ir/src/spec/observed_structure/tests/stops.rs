// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_public_callback_preserves_original_cause_and_never_returns_partial_diagnostics() {
    let specs = compact();
    let (_, base) = run(&specs);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_spec_structure_observed(&specs, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original spec stop");
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_work_and_copy_limits_cumulate_across_calls_without_owner_or_fuel_reset() {
    let specs = compact();
    let (_, base) = run(&specs);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_spec_structure_observed(&specs, &mut s, site()).unwrap();
        assert_eq!(
            validate_spec_structure_observed(&specs, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_spec_structure_observed(&specs, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn initial_copy_refusal_and_preexisting_sticky_refusal_prevent_any_actual_input_walk() {
    let specs = valid();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_spec_structure_observed(&specs, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        validate_spec_structure_observed(&specs, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
    assert_eq!(o.events.len(), 1);
}
#[test]
fn exact_instruction_coordinates_and_zero_execution_fuel_hold_across_all_actual_work() {
    let specs = valid();
    let exact = ExecutionSite::Instruction(crate::interpret::InstructionSite {
        function: FuncId::new(8),
        block: crate::value::BlockId::new(9),
        instruction_index: 55,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_spec_structure_observed(&specs, &mut s, exact).unwrap(),
        validate_spec_structure(&specs)
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn actual_normalization_comparison_can_refuse_interior_without_releasing_full_owned_rows() {
    let a = "λ".repeat(1600) + "B";
    let b = "λ".repeat(1600) + "A";
    let rows = vec![
        SpecLinkViolation::DuplicateMachineIdentity { machine: a },
        SpecLinkViolation::DuplicateMachineIdentity { machine: b },
    ];
    let trace = |stop: Option<usize>| {
        let mut o = Observer {
            stop,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            errors: rows.clone(),
            ..State::default()
        };
        let result = state.normalize(&mut work);
        if stop.is_some() {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(state.errors, rows);
        } else {
            result.unwrap();
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        o
    };
    let base = trace(None);
    let hits = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert!(hits.len() >= 2);
    trace(Some(hits[1]));
}
#[test]
fn actual_unbounded_range_scan_can_stop_before_producing_a_sort_or_accepting_none() {
    let text = "1".repeat(2000) + ".." + &"2".repeat(2000);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        sorts::parse(&text, &mut work).unwrap(),
        Some(sorts::Fixed::Int)
    );
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<&u8>>()
        })
        .nth(50)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        sorts::parse(&text, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        work.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn actual_recursive_debug_stop_keeps_partial_text_and_retires_borrowed_task_storage() {
    let sort = ClauseSort::Datatype {
        name: "D".into(),
        constructors: (0..35)
            .map(|i| (format!("C{i}"), vec![("field".repeat(20), ClauseSort::Int)]))
            .collect(),
    };
    let trace = |stop: Option<usize>| {
        let mut o = Observer {
            stop,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State {
            detail: "prefix: ".into(),
            ..State::default()
        };
        let result = state.sort_text(sorts::Sort::Borrowed(&sort), &mut work);
        if stop.is_some() {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert!(state.detail.starts_with("prefix: Datatype"));
            assert!(state.detail.len() < format!("prefix: {sort:?}").len());
            assert_eq!(state.format.capacity(), 0);
        } else {
            result.unwrap();
            assert_eq!(state.detail, format!("prefix: {sort:?}"));
        }
        drain(&mut state, &mut work);
        assert!(empty(&state));
        o
    };
    let base = trace(None);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 8
                && e.copy_bytes == 4 * size_of::<format::Task<'_>>()
        })
        .nth(10)
        .unwrap()
        .0
        + 1;
    trace(Some(stop));
}
#[test]
fn typed_pending_state_refusal_is_not_a_shorter_successful_structure_result() {
    let specs = compact();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.fields[0] = "already owned".repeat(1000);
    let result = raw(&mut state, &specs, &mut work);
    assert_eq!(result, Err(ObservedValueError::InvalidRange));
    assert_eq!(
        state.finish(result, &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(empty(&state));
    assert!(work.session.first_refusal().is_none());
    assert!(
        !o.events
            .iter()
            .any(|e| e.phase == ExecutionPhase::Publication
                && e.copy_bytes == size_of::<Vec<SpecLinkViolation>>())
    );
}
