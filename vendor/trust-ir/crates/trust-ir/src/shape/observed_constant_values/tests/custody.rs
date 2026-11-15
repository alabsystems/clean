// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn suspended_borrowed_vector_siblings_and_buffer_remain_owned_until_complete_retirement() {
    let (v, t) = branching();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.matches(&v, &t, 64, &mut work).unwrap());
    let end = calls.get();
    state.retire(&mut work);
    empty(&state);
    drop(work);
    drop(s);
    let mut held = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.matches(&v, &t, 64, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= !state.pending.is_empty();
        state.retire(&mut work);
        empty(&state);
    }
    assert!(held);
}
#[test]
fn complete_variable_shape_label_stays_owned_before_fallible_final_text_step() {
    let v = symbol();
    let expected = v.shape_label();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.label(&v, &mut work).unwrap();
    let end = calls.get();
    state.retire(&mut work);
    drop(work);
    drop(s);
    let mut held = false;
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.label(&v, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        held |= state.label == expected;
        state.retire(&mut work);
        empty(&state);
    }
    assert!(held);
}
#[test]
fn healthy_true_false_and_owned_label_cannot_escape_refused_final_publication() {
    for bad in [false, true] {
        let (v, mut t) = branching();
        if bad {
            t = Ty::Bool;
        }
        let (_, _, end) = predicate(&v, &t, 64);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            v.value_matches_ty_observed(&t, 64, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
    let v = symbol();
    let (_, _, end) = label(&v);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        v.shape_label_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
#[test]
fn owned_label_explicit_caller_retirement_preserves_original_refusal_after_complete_drop() {
    let v = symbol();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = v.shape_label_observed(&mut s, site()).unwrap();
    let end = calls.get();
    Work {
        session: &mut s,
        site: site(),
    }
    .flat(text);
    assert!(s.first_refusal().is_none());
    drop(s);
    let mut o = Observer {
        stop: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = v.shape_label_observed(&mut s, site()).unwrap();
    Work {
        session: &mut s,
        site: site(),
    }
    .flat(text);
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original constant-value stop"
    );
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
        .is_err()
    );
}
