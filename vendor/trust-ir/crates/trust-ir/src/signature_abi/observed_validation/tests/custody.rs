// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn inspect(a: &SignatureAbi, sig: &FuncTy, mut check: impl FnMut(&State)) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let _ = state.validate(a, sig, &mut w).unwrap();
    let end = calls.get();
    drain(&mut state, &mut w);
    empty(&state);
    drop(w);
    drop(s);
    let start = semantic_start(&o.events[..end]);
    for cut in start + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.validate(a, sig, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        check(&state);
        drain(&mut state, &mut w);
        empty(&state);
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original signature semantic stop"
        );
    }
}
#[test]
fn all_complete_nested_census_and_live_sorted_range_buffers_remain_owned_after_stop() {
    let (a, s) = direct();
    let (mut census, mut ranges) = (false, false);
    inspect(&a, &s, |x| {
        census |= x.parameters.iter().any(|v| !v.is_empty());
        ranges |= !x.ranges.is_empty();
    });
    assert!(census && ranges);
}
#[test]
fn full_semantic_detail_is_held_before_argument_context_prefix_and_final_error_transfer() {
    let (mut a, s) = direct();
    a.arguments[0].align = 3;
    let (mut detail, mut prefix) = (false, false);
    inspect(&a, &s, |x| {
        detail |= x.reason == "source alignment is not a nonzero power of two";
        prefix |= !x.reason.is_empty() && x.context == "source argument 0: ";
    });
    assert!(detail && prefix);
}
#[test]
fn last_whole_semantic_error_publication_refusal_drains_in_original_session() {
    let (mut a, sig) = direct();
    a.arguments[0].align = 3;
    let (_, _, end) = run(&a, Request::Validate(&sig));
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.validate_observed(&sig, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original signature semantic stop"
    );
}
#[test]
fn successful_caller_error_string_cleanup_can_latch_original_refusal_without_renewal() {
    let (mut a, sig) = direct();
    a.arguments[0].align = 3;
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let trace = o.trace.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = a.validate_observed(&sig, &mut s, site()).unwrap();
    assert_eq!(out, a.validate(&sig));
    let before = calls.get();
    arm.set(true);
    retire(out, &mut s);
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    assert!(
        trace.borrow()[before..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(
        a.validate_observed(&sig, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
