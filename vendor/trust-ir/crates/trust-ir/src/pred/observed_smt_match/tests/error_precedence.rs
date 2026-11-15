// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN: actual public matcher finish preserves a held typed failure.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;

fn held() -> State<'static> {
    let mut text = String::with_capacity(4097);
    text.push_str("whole pending λ\0尾");
    State {
        tasks: vec![Task::Text("unvisited"), Task::Text("complete tail")],
        pending: Some(text),
        cursor: 0,
    }
}

#[test]
fn held_typed_traversal_errors_survive_later_cleanup_stop_in_actual_finish() {
    for error in [
        ObservedValueError::AllocationFailed,
        ObservedValueError::CapacityOverflow,
        ObservedValueError::InvalidRange,
        ObservedValueError::UnsupportedValue,
    ] {
        let mut o = Observer {
            cleanup_after: Some(0),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = held();
        assert_eq!(state.finish(Err(error), &mut w), Err(error));
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original cleanup stop"
        );
        drop(w);
        drop(s);
        assert!(
            o.events
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn healthy_actual_finish_retires_whole_state_then_publishes_each_boolean() {
    for answer in [false, true] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = held();
        assert_eq!(state.finish(Ok(answer), &mut w), Ok(answer));
        assert!(empty(&state));
        assert!(w.session.first_refusal().is_none());
        drop(w);
        drop(s);
        let last = o.events.last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 1, size_of::<bool>())
        );
        assert!(
            o.events[..o.events.len() - 1]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn healthy_boolean_is_withheld_if_actual_finish_cleanup_stops() {
    for answer in [false, true] {
        let mut o = Observer {
            cleanup_after: Some(0),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = held();
        assert_eq!(
            state.finish(Ok(answer), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original cleanup stop"
        );
        drop(w);
        drop(s);
        assert!(
            o.events
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn prior_original_cause_is_immutable_while_held_error_and_whole_state_are_retired() {
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let marker = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: 0,
    };
    assert!(s.admit(marker).is_err());
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = held();
    assert_eq!(
        state.finish(Err(ObservedValueError::CapacityOverflow), &mut w),
        Err(ObservedValueError::CapacityOverflow)
    );
    assert!(empty(&state));
    let first = w.session.first_refusal().unwrap();
    assert_eq!(first.progress, marker);
    assert_eq!(first.cause, "original predicate stop");
    drop(w);
    drop(s);
    assert_eq!(o.events[0], marker);
    assert!(
        o.events[1..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
