// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_whole_fixed_pending_row_precedes_reserve_and_transport() {
    let (r, e) = bad();
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
            && matches!(
                st.pending,
                Some(E::EvidenceProvenanceMismatch {
                    field: "verifier",
                    ..
                })
            )
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
fn verifier_mismatch_stays_owned_while_later_solver_child_refuses() {
    let (r, e) = bad();
    let (_, _, end) = observed(&r, &e);
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
        let result = st.run(&r, &e, &mut w);
        if result.is_err()
            && st.errors
                == vec![E::EvidenceProvenanceMismatch {
                    request: r.id(),
                    field: "verifier",
                }]
            && st.pending.is_none()
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
fn caller_keeps_both_full_input_records_after_interior_stop() {
    let (r, e) = bad();
    let before_r = r.clone();
    let before_e = e.clone();
    let mut o = Observer {
        stop: Some(11),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        e.provenance_binding_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(r, before_r);
    assert_eq!(e, before_e);
}
#[test]
fn held_operational_error_keeps_precedence_over_later_cleanup_refusal() {
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
fn nonzero_cleanup_copy_stop_drains_both_pending_and_prior_rows() {
    let mut o = Observer {
        byte_cap: Some(0),
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
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
#[test]
fn successful_caller_cleanup_keeps_terminal_receipt_and_original_stopped_cause() {
    let (r, e) = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e
        .provenance_binding_errors_observed(&r, &mut s, site())
        .unwrap();
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
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e
        .provenance_binding_errors_observed(&r, &mut s, site())
        .unwrap();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        e.provenance_binding_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
