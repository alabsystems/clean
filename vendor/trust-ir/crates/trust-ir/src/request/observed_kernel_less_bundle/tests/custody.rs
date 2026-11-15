// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn complete_prefix_batch_is_captured_before_first_outer_callback() {
    let b = bad();
    let group = super::super::children::Group::Prefix;
    let end = child_bound(&b, group);
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
        let result = st.child(&b, group, &mut w);
        if result.is_err()
            && st.batch.as_ref().is_some_and(|v| !v.as_slice().is_empty())
            && st.pending.is_none()
        {
            found = true;
            assert!(st.errors.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn complete_request_and_evidence_batches_keep_pending_row_and_unconsumed_tail() {
    let b = bad();
    for group in [
        super::super::children::Group::Requests,
        super::super::children::Group::Evidence,
    ] {
        let end = child_bound(&b, group);
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
            let result = st.child(&b, group, &mut w);
            if result.is_err()
                && st.pending.is_some()
                && st.batch.as_ref().is_some_and(|v| !v.as_slice().is_empty())
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
}
#[test]
fn complete_inner_failure_is_held_before_final_publication_refusal() {
    let expected = vec![E::TrustIrModuleHasNoWireIdentity {
        location: "full raw λ\0尾".into(),
        construct: "raw",
    }];
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        errors: expected.clone(),
        ..State::default()
    };
    st.ready(&mut w).unwrap();
    let end = c.get();
    drain(&mut st, &mut w);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        errors: expected.clone(),
        ..State::default()
    };
    assert!(st.ready(&mut w).is_err());
    assert_eq!(st.output, Some(Err(expected)));
    assert_eq!(st.errors.capacity(), 0);
    drain(&mut st, &mut w);
    empty(&st);
}
#[test]
fn held_local_error_wins_while_output_pending_and_batch_allocation_are_fully_drained() {
    let mut rows = Vec::with_capacity(31);
    rows.push(E::EmptyRequests);
    let capacity = rows.capacity();
    let mut st = State {
        batch: Some(rows.into_iter()),
        batch_capacity: capacity,
        pending: Some(E::EmptyRequests),
        errors: vec![E::EmptyRequests],
        output: Some(Err(vec![E::EmptyRequests])),
    };
    let mut o = Observer {
        retirement_stop: true,
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
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == capacity * size_of::<E>())
    );
}
#[test]
fn stale_output_is_never_replaced_by_smaller_healthy_result() {
    let error = E::MissingReplayIdentity(NativeRequestId::new(91));
    let mut st = State {
        output: Some(Err(vec![error.clone()])),
        ..State::default()
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(st.ready(&mut w), Err(ObservedValueError::InvalidRange));
    assert_eq!(st.output, Some(Err(vec![error])));
    drain(&mut st, &mut w);
    empty(&st);
}
#[test]
fn original_caller_always_consumes_whole_inner_result_even_after_a_later_stop() {
    for b in [good(), bad()] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let result = b.validate_kernel_less_observed(&mut s, site()).unwrap();
        let end = c.get();
        arm.set(true);
        assert!(
            NativeVerificationBundle::retire_kernel_less_validation_observed(
                result,
                &mut s,
                site()
            )
            .is_err()
        );
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
