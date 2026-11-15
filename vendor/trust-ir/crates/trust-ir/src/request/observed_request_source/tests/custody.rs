// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_returned_whole_lineage_child_is_held_before_first_parent_fee() {
    let (b, r) = bad();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    body(&mut st, &b, &r, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let cut = base
        .events
        .iter()
        .position(|p| {
            p.phase == ExecutionPhase::Publication
                && p.copy_bytes == size_of::<NativeRequestLineage<'_>>()
        })
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
    let result = body(&mut st, &b, &r, &mut w);
    assert!(result.is_err());
    assert!(st.lineage.is_some());
    assert!(st.ids.is_empty());
    assert!(st.errors.len() >= 4);
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn complete_fixed_pending_error_is_owned_before_output_reserve_or_transport() {
    let (b, r) = bad();
    let (_, _, end) = observed(&b, &r);
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
        let result = body(&mut st, &b, &r, &mut w);
        if result.is_err()
            && st.errors.is_empty()
            && matches!(st.pending, Some(E::RequestLineageRootTargetMismatch { .. }))
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
fn completed_prior_rows_and_sorted_ids_stay_held_when_later_checks_refuse() {
    let (b, r) = bad();
    let (_, _, end) = observed(&b, &r);
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
        let result = body(&mut st, &b, &r, &mut w);
        if result.is_err()
            && st.ids == vec![ProofId::new(0), ProofId::new(1), ProofId::new(77)]
            && st
                .errors
                .iter()
                .any(|e| matches!(e, E::MissingObligationSourceAssertion { .. }))
        {
            assert!(st.lineage.is_some());
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
fn held_local_error_survives_full_child_pending_and_prior_disposal_refusal() {
    let (b, r) = fixture();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let lineage = b
        .lineage
        .request_lineage_observed(r.lineage_roots(), b.source_digest(), &mut s, site())
        .unwrap();
    let mut st = State {
        lineage: Some(lineage),
        ids: vec![ProofId::new(1)],
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
    };
    arm.set(true);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn full_sorted_ids_and_output_spare_capacities_consume_after_stop() {
    let mut st = State {
        lineage: None,
        ids: Vec::with_capacity(71),
        pending: Some(E::EmptyRequests),
        errors: Vec::with_capacity(37),
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
fn full_original_bundle_and_request_remain_unchanged_after_stop() {
    let (b, r) = bad();
    let before = b.stable_digest();
    let request = r.clone();
    let mut o = Observer {
        stop: Some(17),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(b.stable_digest(), before);
    assert_eq!(r, request);
}
#[test]
fn healthy_result_caller_retirement_ends_scratch_then_zero_publication() {
    let (b, r) = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_source_errors_observed(&r, &mut s, site())
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
fn stopped_result_caller_retirement_drains_without_new_publication() {
    let (b, r) = bad();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_source_errors_observed(&r, &mut s, site())
        .unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
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
