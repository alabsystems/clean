// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn exact_partial_unicode_detail_prefix_is_held_on_interior_copy_refusal() {
    let mut input = fixture();
    input.context.atoms.clear();
    input
        .context
        .unsupported_modes
        .push(NativeUnsupportedMode::new(
            NativeUnsupportedModeReason::Other,
            "a".repeat(1024) + &"尾".repeat(700),
        ));
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
        let result = body(&mut st, &input, &mut w);
        if result.is_err() && st.text.len() == 1024 {
            assert_eq!(st.text, "a".repeat(1024));
            assert!(st.pending.is_none());
            assert!(st.errors.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
            found = true;
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn complete_owned_detail_is_pending_before_error_reserve_and_transport() {
    let input = bad();
    let (_, _, end) = observed(&input);
    let mut found = 0;
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
        if result.is_err()
            && st.errors.is_empty()
            && matches!(&st.pending,Some(E::UnsupportedNativeRequestMode{detail,..})if detail=="raw detail")
        {
            found += 1;
            assert!(st.text.is_empty());
            assert!(st.finish(result, &mut w).is_err());
            empty(&st);
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(found >= 2);
}
#[test]
fn full_prior_unsupported_row_is_retained_when_actual_formula_child_refuses() {
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
        if result.is_err()
            && matches!(
                st.errors.as_slice(),
                [E::UnsupportedNativeRequestMode { .. }]
            )
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
fn held_local_error_precedes_refusal_while_full_text_pending_and_prior_drain() {
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
        text: "whole scratch".into(),
        pending: Some(E::UnsupportedNativeRequestMode {
            request: request(),
            reason: NativeUnsupportedModeReason::Other,
            detail: "whole pending".into(),
        }),
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
fn complete_text_and_prior_vector_spare_capacity_retire_after_stop() {
    let mut text = String::with_capacity(2048);
    text.push_str("partial");
    let text_capacity = text.capacity();
    let mut rows = Vec::with_capacity(37);
    rows.push(E::EmptyRequests);
    let row_capacity = rows.capacity();
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
        text,
        pending: None,
        errors: rows,
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    drop(w);
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes >= text_capacity)
    );
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::ScratchRetirement
                && p.copy_bytes >= row_capacity * size_of::<E>())
    );
}
#[test]
fn all_actual_original_borrowed_records_remain_unchanged_after_stop() {
    let input = bad();
    let before = input.clone();
    let mut o = Observer {
        stop: Some(11),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(input.observed(&mut s).is_err());
    assert_eq!(input.context, before.context);
    assert_eq!(input.obligations, before.obligations);
    assert_eq!(input.facts, before.facts);
    assert_eq!(input.module.stable_digest(), before.module.stable_digest());
}
#[test]
fn successful_caller_consumption_has_final_zero_publication_after_all_scratch() {
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
    let last = o.events.last().unwrap();
    assert_eq!(last.phase, ExecutionPhase::Publication);
    assert_eq!((last.work, last.copy_bytes), (0, 0));
}
#[test]
fn stopped_caller_consumption_drains_full_result_without_new_publication() {
    let input = bad();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = input.observed(&mut s).unwrap();
    let end = calls.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(input.observed(&mut s).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
