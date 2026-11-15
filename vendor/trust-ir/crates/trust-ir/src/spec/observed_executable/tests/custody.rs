// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::double_ended_iterator_last,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_pending_fields_survive_distinct_output_reserve_and_header_refusals() {
    let m = compact();
    let base = trace(&m);
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
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            raw(&mut state, &m, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(state.fields[0], "M");
        assert_eq!(state.fields[1], "a");
        assert_eq!(
            state.detail,
            format!("function id is not present in module {:?}", m.name)
        );
        assert!(state.errors.is_empty());
        assert_eq!(state.errors.capacity() == 0, n == 0);
        drain(&mut state, &mut w);
        assert!(empty(&state));
    }
}
#[test]
fn actual_machine_copy_keeps_partial_prefix_full_detail_and_original_tail() {
    let mut m = compact();
    m.spec_modules[0].name = "λ".repeat(2000) + "TAIL";
    m.spec_modules[0].anchors[0].machine = m.spec_modules[0].name.clone();
    let base = trace(&m);
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
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.fields[0], "λ".repeat(512));
    assert_eq!(
        state.detail,
        format!("function id is not present in module {:?}", m.name)
    );
    assert!(m.spec_modules[0].name.ends_with("TAIL"));
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn later_output_stop_keeps_full_previous_errors_and_new_detail_before_complete_cleanup() {
    let mut m = compact();
    let mut a = m.spec_modules[0].anchors[0].clone();
    a.action = "b".into();
    m.spec_modules[0].anchors.push(a);
    let base = trace(&m);
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
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        raw(&mut state, &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.len(), 1);
    assert_eq!(state.errors[0], validate_spec_executable_links(&m)[0]);
    assert_eq!(state.fields[0], "M");
    assert_eq!(state.fields[1], "b");
    assert!(!state.detail.is_empty());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original executable stop"
    );
}
#[test]
fn sticky_scratch_cleanup_consumes_all_pending_and_prior_violation_fields_and_tasks() {
    let m = compact();
    let ty = Ty::Tuple(vec![Ty::U8]);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    raw(&mut state, &m, &mut w).unwrap();
    state.fields = ["field".repeat(1000), "action".repeat(1000)];
    state.detail = "detail".repeat(1000);
    state.tasks = vec![super::super::debug::Task::Type(&ty)];
    state.pending = Some(SpecLinkViolation::ExecutableTargetInvalid {
        machine: "machine".repeat(1000),
        action: "action".repeat(1000),
        target: "projection",
        function: u32::MAX,
        detail: "pending".repeat(1000),
    });
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn refused_final_publication_consumes_all_complete_owned_output_after_scratch() {
    let m = compact();
    let (_, base) = run(&m);
    let stop = base.events.len();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_spec_executable_links_observed(&m, &mut s, site()),
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
