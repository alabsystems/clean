// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn an_interrupted_actual_id_shift_keeps_the_full_backing_vector_owned() {
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut rows = ids(&[2, 5, 9]);
    rows.reserve_exact(4);
    w.insert_id(&mut rows, ProofId::new(1)).unwrap();
    w.copy_rows(rows);
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
        st.requested = ids(&[2, 5, 9]);
        st.requested.reserve_exact(4);
        let result = w.insert_id(&mut st.requested, ProofId::new(1));
        if result.is_err()
            && st.requested.len() == 4
            && st.requested.windows(2).any(|p| p[0] == p[1])
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
fn full_requested_set_and_partial_supplied_set_are_retained_until_finish() {
    let (r, e) = fixture();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&r, &e, &mut w).unwrap();
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
        let result = st.run(&r, &e, &mut w);
        if result.is_err()
            && st.requested == ids(&[0, 1, 2, 5, 7, 9])
            && !st.supplied.is_empty()
            && st.supplied.len() < 4
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
fn full_spare_copy_vector_capacity_is_retired_not_only_live_ids() {
    let mut rows = Vec::with_capacity(121);
    rows.extend(ids(&[2, 3]));
    let capacity = rows.capacity();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.copy_rows(rows);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.copy_bytes == capacity * size_of::<ProofId>())
    );
}
#[test]
fn each_whole_pending_difference_error_precedes_output_allocation_and_transfer() {
    let (r, e) = fixture();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&r, &e, &mut w).unwrap();
    drain(&mut st, &mut w);
    let mut found = 0;
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
        let result = st.run(&r, &e, &mut w);
        if result.is_err()
            && st.errors.is_empty()
            && matches!(st.pending,Some(E::EvidenceObligationMismatch{obligation,..}) if obligation==ProofId::new(1))
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
fn held_local_error_keeps_precedence_while_cleanup_still_refuses_and_drains() {
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
        requested: ids(&[1, 2, 3]),
        supplied: ids(&[4, 5]),
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn successful_and_stopped_caller_disposal_keep_original_terminal_and_first_cause() {
    let (r, e) = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.obligation_errors_observed(&r, &mut s, site()).unwrap();
    let bound = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
    assert_eq!(o.events.last().unwrap().phase, ExecutionPhase::Publication);
    assert_eq!(o.events.last().unwrap().work, 0);
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.obligation_errors_observed(&r, &mut s, site()).unwrap();
    arm.set(true);
    assert_eq!(
        retire_native_bundle_errors_observed(rows, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        e.obligation_errors_observed(&r, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
