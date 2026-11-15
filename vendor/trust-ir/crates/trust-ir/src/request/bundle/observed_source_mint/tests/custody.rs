// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn full_actual_invalid_diagnostics_are_captured_before_inner_error_conversion() {
    let b = bad();
    let expected = b.validate();
    let end = private_bound(&b);
    let cut = end; // Invalid path ends at actual conversion fee.
    let mut b = b;
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
    let result = st.run(&b, &mut w);
    assert!(result.is_err());
    assert_eq!(st.validation, Some(expected));
    assert!(st.output.is_none());
    assert!(st.finish(&mut b, result, &mut w).is_err());
    empty(&st);
    assert!(b.source_generation_live.0.is_none());
}
#[test]
fn fresh_nonce_and_then_cloned_marker_stay_held_before_the_next_fallible_operation() {
    let b = good();
    let end = private_bound(&b);
    for (cut, marker) in [(end - 1, false), (end, true)] {
        let mut b = good();
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
        let result = st.run(&b, &mut w);
        assert!(result.is_err());
        assert!(st.nonce.is_some());
        assert_eq!(st.marker.is_some(), marker);
        assert!(st.output.is_none());
        assert!(b.source_generation_live.0.is_none());
        assert!(st.finish(&mut b, result, &mut w).is_err());
        empty(&st);
        assert!(b.source_generation_live.0.is_none());
    }
}
#[test]
fn complete_matching_candidates_remain_uninstalled_until_actual_final_publication() {
    let b = good();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, &mut w).unwrap();
    st.ready(&mut w).unwrap();
    let a = st.output.as_ref().unwrap().as_ref().unwrap();
    assert!(st.marker.as_ref().unwrap().matches(&a.nonce));
    assert!(b.source_generation_live.0.is_none());
    st.retire_transient(&mut w);
    arm.set(true);
    assert!(w.publication().is_err());
    assert!(b.source_generation_live.0.is_none());
    st.retire_candidates(&mut w);
    empty(&st);
}
#[test]
fn held_local_error_wins_and_all_private_nonce_candidates_and_error_backing_are_retired() {
    let b = good();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, &mut w).unwrap();
    let mut rows = Vec::with_capacity(23);
    rows.push(NativeVerificationBundleError::EmptyRequests);
    let cap = rows.capacity();
    st.validation = Some(Err(rows));
    let mut b = b;
    assert!(matches!(
        st.finish(&mut b, Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    ));
    empty(&st);
    assert!(b.source_generation_live.0.is_none());
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes == cap * size_of::<NativeVerificationBundleError>())
    );
}
#[test]
fn mismatched_private_candidate_shapes_refuse_and_never_install_or_escape() {
    let mut b = good();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, &mut w).unwrap();
    let marker = st.marker.take().unwrap();
    if let Some(nonce) = marker.0 {
        w.release(nonce);
    }
    assert_eq!(st.ready(&mut w), Err(ObservedValueError::InvalidRange));
    assert!(matches!(
        st.finish(&mut b, Ok(()), &mut w),
        Err(ObservedValueError::InvalidRange)
    ));
    empty(&st);
    assert!(b.source_generation_live.0.is_none());
}
#[test]
fn cleanup_only_stop_after_complete_candidates_prevents_live_commit() {
    let mut b = good();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&b, &mut w).unwrap();
    arm.set(true);
    assert!(st.finish(&mut b, Ok(()), &mut w).is_err());
    empty(&st);
    assert!(b.source_generation_live.0.is_none());
}
