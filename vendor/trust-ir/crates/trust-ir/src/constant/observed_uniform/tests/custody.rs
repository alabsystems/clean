// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_current_building_pending_key_bucket_and_class_buffers_stay_owned_until_drain() {
    let root = sample();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.walk(&root, &mut work).unwrap();
    let end = calls.get();
    drain(&mut state, &mut work);
    empty(&state);
    drop(work);
    drop(s);
    let (mut current, mut building, mut key, mut bucket, mut classes) =
        (false, false, false, false, false);
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
            state.walk(&root, &mut work),
            Err(ObservedValueError::AdmissionRefused)
        );
        current |= state.current.is_some();
        building |= state.building.is_some();
        key |= state.pending_key.is_some();
        bucket |= !state.pending_bucket.is_empty();
        classes |= !state.classes.is_empty();
        drain(&mut state, &mut work);
        empty(&state);
    }
    assert!(current && building && key && bucket && classes);
}
#[test]
fn successful_walk_holds_every_owned_scratch_store_before_output_only_transfer() {
    let root = sample();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    state.walk(&root, &mut work).unwrap();
    assert!(!state.classes.is_empty() && !state.buckets.is_empty());
    assert_eq!(state.uniform.len(), 2);
    state.retire_scratch(&mut work);
    assert_eq!(
        state.classes.capacity()
            + state.results.capacity()
            + state.stack.capacity()
            + state.pending_bucket.capacity(),
        0
    );
    assert!(state.buckets.is_empty() && state.building.is_none() && state.pending_key.is_none());
    assert_eq!(state.uniform.len(), 2);
    work.rows(take(&mut state.uniform));
    empty(&state);
}
#[test]
fn final_constructor_and_true_false_membership_publications_never_escape_stop() {
    let root = sample();
    let (_, _, end, _) = run(&root);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        root.uniform_element_lists_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    drop(s);
    for positive in [false, true] {
        let external = root.clone();
        let mut o = Observer::default();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
        let node = if positive { &root } else { &external };
        assert_eq!(
            table.contains_observed(node, &mut s, site()).unwrap(),
            positive
        );
        let end = calls.get();
        table.retire_observed(&mut s, site()).unwrap();
        drop(s);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
        assert_eq!(
            table.contains_observed(node, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let _ = table.retire_observed(&mut s, site());
    }
}
#[test]
fn complete_table_caller_retirement_preserves_healthy_terminal_and_original_stop() {
    let root = sample();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    let end = calls.get();
    table.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
    let mut o = Observer {
        stop: Some(end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = root.uniform_element_lists_observed(&mut s, site()).unwrap();
    assert_eq!(
        table.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original uniform-class stop"
    );
}
