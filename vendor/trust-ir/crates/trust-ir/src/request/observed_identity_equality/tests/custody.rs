// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_input_strings_and_optional_fields_remain_unmodified_after_stop() {
    let a = tool();
    let before = a.clone();
    let mut o = Observer {
        stop: Some(7),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(a.structural_eq_observed(&a, &mut s, site()).is_err());
    assert_eq!(a, before);
}
#[test]
fn replay_inputs_remain_owned_by_caller_after_stop() {
    let a = replay();
    let before = a.clone();
    let mut o = Observer {
        stop: Some(7),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(a.structural_eq_observed(&a, &mut s, site()).is_err());
    assert_eq!(a, before);
}
#[test]
fn no_retirement_or_owned_allocation_is_introduced_by_the_borrowed_helper() {
    let a = tool();
    let p = replay();
    for events in [tool_run(&a, &a).1.events, replay_run(&p, &p).1.events] {
        assert!(events.iter().all(|p| matches!(
            p.phase,
            ExecutionPhase::Validation | ExecutionPhase::Publication
        )));
        assert_eq!(
            events
                .iter()
                .filter(|p| p.phase == ExecutionPhase::Publication)
                .count(),
            1
        );
    }
}
#[test]
fn both_sides_of_each_large_actual_window_are_charged() {
    let mut a = tool();
    a.name = "λ".repeat(2000);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.text(&a.name, &a.name).unwrap());
    drop(w);
    drop(s);
    assert!(o.work >= 2 * a.name.len());
    assert!(o.events.iter().any(|p| p.work == 2048 && p.copy_bytes == 0));
}
#[test]
fn false_equality_still_requires_its_original_final_publication() {
    let a = NativeToolIdentity::new("a");
    let b = NativeToolIdentity::new("b");
    let (_, base) = tool_run(&a, &b);
    let mut o = Observer {
        stop: Some(base.events.len()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.structural_eq_observed(&b, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress,
        *base.events.last().unwrap()
    );
}
#[test]
fn equal_empty_fields_still_require_their_original_final_publication() {
    let a = ProofReplayIdentity::new("", "");
    let (_, base) = replay_run(&a, &a);
    let mut o = Observer {
        stop: Some(base.events.len()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        a.structural_eq_observed(&a, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress,
        *base.events.last().unwrap()
    );
}
