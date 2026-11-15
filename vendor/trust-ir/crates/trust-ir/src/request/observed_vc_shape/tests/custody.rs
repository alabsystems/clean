// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_partial_long_unicode_prover_prefix_remains_owned_until_cleanup() {
    let mut b = bad();
    vc(&mut b).certificates[0].prover = "a".repeat(1024) + &"尾".repeat(700);
    let (_, _, end) = observed(&b, 0);
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
        let result = st.run(&b, 0, &mut w);
        if result.is_err() && st.text.len() == 1024 {
            assert_eq!(st.text, "a".repeat(1024));
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
fn complete_carried_prover_pending_error_precedes_output_reserve_and_transport() {
    let b = bad();
    let (_, _, end) = observed(&b, 0);
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
        let result = st.run(&b, 0, &mut w);
        if result.is_err()
            && matches!(&st.pending,Some(E::TrustVcDischargeRequestCarriesCertificate{prover,..})if prover=="trust_vc")
        {
            assert_eq!(st.errors.len(), 2);
            assert!(st.text.is_empty());
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
fn held_local_error_and_all_partial_or_prior_capacities_are_consumed_after_stop() {
    let mut text = String::with_capacity(2048);
    text.push_str("partial");
    let text_capacity = text.capacity();
    let mut ids = Vec::with_capacity(71);
    ids.push(ProofId::new(1));
    let ids_capacity = ids.capacity();
    let mut st = State {
        ids,
        text,
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
    drop(w);
    drop(s);
    for bytes in [text_capacity, ids_capacity * size_of::<ProofId>()] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == bytes)
        );
    }
}
#[test]
fn actual_borrowed_whole_module_sidecars_and_request_remain_exact_after_stop() {
    let b = bad();
    let before = b.stable_digest();
    let requests = b.requests.clone();
    let mut o = Observer {
        stop: Some(29),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_vc_shape_errors_observed(0, &mut s, site())
            .is_err()
    );
    assert_eq!(b.stable_digest(), before);
    assert_eq!(b.requests, requests);
}
#[test]
fn healthy_original_caller_disposal_retains_final_zero_publication() {
    let b = bad();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_vc_shape_errors_observed(0, &mut s, site())
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
fn stopped_original_caller_disposal_drains_without_normal_publication() {
    let b = bad();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_vc_shape_errors_observed(0, &mut s, site())
        .unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(
        b.request_vc_shape_errors_observed(1, &mut s, site())
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
