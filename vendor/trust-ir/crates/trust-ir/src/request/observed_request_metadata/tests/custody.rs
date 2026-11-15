// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn whole_actual_diagnostics_child_batch_is_captured_before_first_parent_fee() {
    let b = bad();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, 1, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let cut = base
        .events
        .iter()
        .position(|p| p.phase == ExecutionPhase::Publication && p.copy_bytes == size_of::<Vec<E>>())
        .unwrap()
        + 2;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    let result = st.run(&b, 1, &mut w);
    assert!(result.is_err());
    let rows = st.batch.as_ref().unwrap().as_slice();
    assert_eq!(rows.len(), 3);
    assert!(
        rows.iter()
            .all(|e| matches!(e, E::InvalidDiagnosticsPolicy { .. }))
    );
    assert_eq!(st.errors.len(), 2);
    assert!(st.pending.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn full_pending_prior_output_and_remaining_child_tail_consume_after_stop() {
    let b = bad();
    let (_, _, end) = observed(&b, 1);
    let mut found = false;
    for cut in 1..end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.run(&b, 1, &mut w);
        if result.is_err()
            && matches!(
                st.pending,
                Some(E::InvalidDiagnosticsPolicy {
                    field: "include_source_spans",
                    ..
                })
            )
            && st.batch.as_ref().is_some_and(|r| r.len() == 2)
        {
            assert_eq!(st.errors.len(), 2);
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn held_local_error_precedes_later_retirement_refusal_and_drains_full_capacity() {
    let mut rows = Vec::with_capacity(41);
    rows.extend([E::EmptyRequests, E::EmptyRequests]);
    let capacity = rows.capacity();
    let mut st = State {
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
        batch: Some(rows.into_iter()),
        batch_capacity: capacity,
    };
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == capacity * size_of::<E>())
    );
}
#[test]
fn occupied_child_slot_refuses_before_any_new_child_or_owning_overwrite() {
    let mut st = State {
        batch: Some(vec![E::EmptyRequests].into_iter()),
        batch_capacity: 1,
        ..State::default()
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(st.prepare(&mut w), Err(ObservedValueError::InvalidRange));
    assert_eq!(st.batch.as_ref().unwrap().len(), 1);
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
}
#[test]
fn original_whole_request_and_bundle_remain_exact_after_stop() {
    let b = bad();
    let requests = b.requests.clone();
    let before = b.stable_digest();
    let mut o = Observer {
        stop: Some(31),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_metadata_errors_observed(1, &mut s, site())
            .is_err()
    );
    assert_eq!(b.requests, requests);
    assert_eq!(b.stable_digest(), before);
}
#[test]
fn healthy_and_stopped_caller_cleanup_keep_original_terminal_contract() {
    let b = bad();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_metadata_errors_observed(1, &mut s, site())
        .unwrap();
    let first = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    let healthy_end = calls.get();
    let rows = b
        .request_metadata_errors_observed(1, &mut s, site())
        .unwrap();
    let second = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        b.request_metadata_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[first..healthy_end - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(o.events[healthy_end - 1].phase, ExecutionPhase::Publication);
    assert_eq!(
        (
            o.events[healthy_end - 1].work,
            o.events[healthy_end - 1].copy_bytes
        ),
        (0, 0)
    );
    assert!(
        o.events[second..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
