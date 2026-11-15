// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_child_return_is_held_before_first_parent_flush_fee() {
    let b = bad();
    let e = &b.evidence_bundles[1];
    let expected = {
        let mut v = Vec::new();
        crate::request::validate_evidence_artifacts(e, &mut v);
        v
    };
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    artifact_child(&mut st, e, &mut w).unwrap();
    drain(&mut st, &mut w);
    let child_end = base
        .events
        .iter()
        .position(|p| p.phase == ExecutionPhase::Publication && p.copy_bytes == size_of::<Vec<E>>())
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(child_end + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    let result = artifact_child(&mut st, e, &mut w);
    assert!(result.is_err());
    assert_eq!(st.batch.as_ref().unwrap().as_slice(), &expected[..]);
    assert!(st.pending.is_none() && st.errors.is_empty());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn whole_next_pending_and_remaining_child_tail_survive_output_refusal() {
    let b = bad();
    let e = &b.evidence_bundles[1];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    artifact_child(&mut st, e, &mut w).unwrap();
    drain(&mut st, &mut w);
    let mut found = false;
    for cut in 1..=base.events.len() {
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
        let result = artifact_child(&mut st, e, &mut w);
        if result.is_err()
            && st.pending.is_some()
            && !st.errors.is_empty()
            && st.batch.as_ref().is_some_and(|b| !b.as_slice().is_empty())
        {
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
fn full_child_spare_capacity_is_retired_after_every_actual_error() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    let mut rows = Vec::with_capacity(121);
    rows.push(E::RustReferenceAsPermissionBorrow {
        location: "whole".repeat(500),
    });
    let capacity = rows.capacity();
    st.prepare(&mut w).unwrap();
    st.capture(rows);
    st.flush(&mut w).unwrap();
    assert!(st.batch.is_none() && st.batch_capacity == 0);
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.copy_bytes == capacity * size_of::<E>())
    );
}
#[test]
fn prepare_refuses_to_overwrite_an_existing_owned_batch_or_pending_error() {
    for pending in [false, true] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        if pending {
            st.pending = Some(E::EmptyRequests);
        } else {
            st.batch = Some(vec![E::EmptyRequests].into_iter());
            st.batch_capacity = 1;
        }
        assert_eq!(st.prepare(&mut w), Err(ObservedValueError::InvalidRange));
        assert_eq!(st.pending.is_some(), pending);
        assert_eq!(st.batch.is_some(), !pending);
        drain(&mut st, &mut w);
        empty(&st);
    }
}
#[test]
fn held_operational_error_keeps_precedence_while_all_child_owners_drain() {
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
        batch: Some(
            vec![E::RustReferenceAsPermissionBorrow {
                location: "full".repeat(300),
            }]
            .into_iter(),
        ),
        batch_capacity: 1,
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn original_input_borrow_and_source_content_survive_interior_stop() {
    let b = minimal();
    let before = b.clone();
    let mut o = Observer {
        stop: Some(11),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    assert_eq!(b, before);
}
#[test]
fn successful_caller_retirement_keeps_its_mandatory_terminal_receipt() {
    let b = minimal();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.evidence_errors_observed(&mut s, site()).unwrap();
    let bound = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[bound..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    assert_eq!(o.events.last().unwrap().work, 0);
}
#[test]
fn stopped_successful_caller_retirement_consumes_whole_result_and_keeps_first_cause() {
    let b = minimal();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.evidence_errors_observed(&mut s, site()).unwrap();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(b.evidence_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
