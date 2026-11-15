// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::double_ended_iterator_last,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_pending_machine_string_survives_distinct_output_growth_and_header_cuts() {
    let specs = compact();
    let base = private_trace(&specs);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<SpecLinkViolation>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    assert_eq!(cuts[1], cuts[0] + 1);
    for (n, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            raw(&mut state, &specs, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.fields[0], "M");
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut work);
        assert!(empty(&state));
    }
}
#[test]
fn later_output_refusal_retains_prior_complete_errors_and_new_full_pending_fields() {
    let mut specs = compact();
    specs[0].vars.push(SpecVar::new("", ""));
    let base = private_trace(&specs);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<SpecLinkViolation>()
        })
        .last()
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
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &specs, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.len() >= 2);
    assert_eq!(state.fields[0], "M");
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn full_formatted_detail_stays_owned_while_its_pending_output_copy_is_interior() {
    let mut specs = valid();
    specs[0].anchors = vec![anchor("Gone", "a")];
    specs[0].anchors[0].rust_symbol = "x".repeat(3000) + "λTAIL";
    let base = private_trace(&specs);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert!(cuts.len() >= 3);
    assert_eq!(cuts[1], cuts[0] + 1);
    let stop = cuts[2];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &specs, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        state.detail,
        format!(
            "function=unresolved, rust_symbol={:?}",
            specs[0].anchors[0].rust_symbol
        )
    );
    assert_eq!(state.fields[0], "Gone");
    assert_eq!(state.fields[1], "a");
    assert_eq!(state.fields[2].len(), 1024);
    assert!(state.fields[2].starts_with("function=unresolved"));
    assert!(state.errors.is_empty());
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn owned_machine_name_copy_can_stop_before_its_tail_without_overwriting_input() {
    let mut specs = compact();
    specs[0].name = "λ".repeat(2000) + "TAIL";
    let base = private_trace(&specs);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts[1], cuts[0] + 1);
    let stop = cuts[2];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &specs, &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.fields[0], "λ".repeat(512));
    assert!(specs[0].name.ends_with("TAIL"));
    drain(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn sticky_cleanup_consumes_all_partial_fields_detail_tasks_pending_and_prior_violations() {
    let specs = compact();
    let sort = deep_sort();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, &specs, &mut work).unwrap();
    for field in &mut state.fields {
        *field = "pendingλ".repeat(1000);
    }
    state.detail = "detailλ".repeat(1000);
    state.format = vec![format::Task::Sort(&sort)];
    state.equality = vec![sorts::Pair::Sort(&sort, &sort)];
    state.pending = Some(SpecLinkViolation::MachineMissing {
        machine: "machine".repeat(1000),
        action: "action".repeat(1000),
        from: "anchor",
        detail: "pending".repeat(1000),
    });
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(
        work.session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
}
#[test]
fn final_publication_refuses_only_after_all_local_scratch_then_consumes_full_result() {
    let specs = compact();
    let (_, base) = run(&specs);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_spec_structure_observed(&specs, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(o.events.len() > stop);
    assert!(
        o.events
            .iter()
            .skip(stop)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
