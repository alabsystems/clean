// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_pending_row_is_owned_before_reserve_and_transport() {
    let input = bad();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    body(&mut st, &input, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    let mut hits = 0;
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
        let result = body(&mut st, &input, &mut w);
        if result.is_err()
            && st.errors.is_empty()
            && matches!(
                st.pending,
                Some(E::InvalidTrustMcChcOptions {
                    field: "chc.pdr.enabled",
                    ..
                })
            )
        {
            hits += 1;
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(hits >= 2);
}
#[test]
fn prior_completed_rows_survive_until_later_guard_refusal_and_full_cleanup() {
    let input = bad();
    let (_, _, end) = observed(&input);
    let mut found = false;
    for cut in 1..=end {
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
        let result = body(&mut st, &input, &mut w);
        if result.is_err() && st.errors.len() == 2 && st.pending.is_none() {
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
fn held_local_operational_error_precedes_later_cleanup_refusal() {
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
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn whole_prior_vector_spare_capacity_is_retired_after_stop() {
    let mut rows = Vec::with_capacity(63);
    rows.push(E::EmptyRequests);
    let capacity = rows.capacity();
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
        errors: rows,
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes >= capacity * size_of::<E>())
    );
}
#[test]
fn actual_original_inputs_remain_whole_after_interior_stop() {
    let r = wp();
    let before = r.clone();
    let mut o = Observer {
        stop: Some(2),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(r.mode_errors_observed(&mut s, site()).is_err());
    assert_eq!(r, before);
}
#[test]
fn successful_caller_retirement_keeps_terminal_receipt_and_sticky_stop() {
    let input = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = input.observed(&mut s).unwrap();
    let end = calls.get();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    assert!(
        o.events[end..o.events.len() - 1]
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
    let rows = input.observed(&mut s).unwrap();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(bad_wp().observed(&mut s).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
