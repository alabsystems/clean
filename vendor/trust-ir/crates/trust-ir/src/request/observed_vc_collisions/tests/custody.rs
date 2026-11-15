// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_fixed_collision_pending_precedes_output_reserve_and_transport() {
    let i = fixture();
    let (_, _, end) = observed(&i);
    let mut found = 0;
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
        let result = st.run(&i.requests, &mut w);
        if result.is_err()
            && st.errors.is_empty()
            && matches!(st.pending,Some(E::TrustVcObligationBothImportedAndDischarged{obligation,..})if obligation==ProofId::new(1))
        {
            found += 1;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(found >= 2);
}
#[test]
fn prior_rows_ids_and_whole_spare_capacity_are_consumed_after_stop() {
    let mut st = State {
        ids: Vec::with_capacity(73),
        pending: Some(E::EmptyRequests),
        errors: Vec::with_capacity(31),
    };
    st.ids.push(ProofId::new(1));
    st.errors.push(E::EmptyRequests);
    let ids = st.ids.capacity();
    let errors = st.errors.capacity();
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == ids * size_of::<ProofId>())
    );
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == errors * size_of::<E>())
    );
}
#[test]
fn held_local_error_wins_over_later_scratch_refusal() {
    let mut st = State {
        ids: vec![ProofId::new(1)],
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
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
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn actual_whole_borrowed_requests_remain_unchanged_after_stop() {
    let i = fixture();
    let requests = i.requests.clone();
    let mut o = Observer {
        stop: Some(17),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        i.trust_vc_mode_collision_errors_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(i.requests, requests);
}
#[test]
fn healthy_returned_result_consumption_ends_in_zero_publication() {
    let i = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = i
        .trust_vc_mode_collision_errors_observed(&mut s, site())
        .unwrap();
    let end = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[end..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    let last = o.events.last().unwrap();
    assert_eq!(last.phase, ExecutionPhase::Publication);
    assert_eq!((last.work, last.copy_bytes), (0, 0));
}
#[test]
fn stopped_returned_result_consumption_drains_and_keeps_original_refusal() {
    let i = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = i
        .trust_vc_mode_collision_errors_observed(&mut s, site())
        .unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        i.trust_vc_mode_collision_errors_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
