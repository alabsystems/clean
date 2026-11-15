// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn first_ascii_storage_reservation_is_refused_before_allocation() {
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut text = String::new();
    w.byte(b'a', &mut text).unwrap();
    w.text_drop(text);
    drop(w);
    drop(s);
    let cut = base
        .events
        .iter()
        .position(|p| p.work == 1 && p.copy_bytes == 1)
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut text = String::new();
    assert_eq!(
        w.byte(b'a', &mut text),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(text.capacity(), 0);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[cut - 1]
    );
    w.text_drop(text);
}
#[test]
fn full_normalized_and_partial_rewritten_strings_stay_owned_together() {
    let name = names()[0].clone();
    let expected = crate::request::canonical_tool_name(&name);
    let full_normalized = expected.replacen("trust_mc", "trust-mc", 1);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&name, &mut w).unwrap();
    drain(&mut st, &mut w);
    drop(w);
    drop(s);
    // Normalization writes individual bytes. These are the actual whole
    // family append (after its distinct equal-size reserve admission) and
    // each actual 1024-byte suffix-copy admission.
    let family = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.work == 8 && p.copy_bytes == 8)
        .nth(1)
        .unwrap()
        .0;
    let mut cuts = vec![family + 2];
    cuts.extend(
        base.events
            .iter()
            .enumerate()
            .filter(|(_, p)| p.work == 1024 && p.copy_bytes == 1024)
            .map(|(i, _)| i + 1),
    );
    assert!(cuts.len() >= 3);
    for cut in cuts {
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
        let result = st.run(&name, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        assert_eq!(st.normalized, full_normalized);
        assert!(st.canonical.len() >= 8 && st.canonical.len() < expected.len());
        assert!(expected.starts_with(&st.canonical));
        assert!(st.finish(result, &mut w).is_err());
        empty(&st);
    }
}
#[test]
fn interrupted_byte_normalization_retains_its_full_partial_buffer() {
    let name = names()[1].clone();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.run(&name, &mut w).unwrap();
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
        let result = st.run(&name, &mut w);
        if result.is_err() && st.normalized.len() > 32 && st.canonical.is_empty() {
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
fn cleanup_refusal_does_not_replace_an_earlier_local_error() {
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
        normalized: "whole".repeat(400),
        canonical: "held".repeat(400),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "interior");
}
#[test]
fn nonzero_retirement_copy_refusal_drops_both_spare_allocations() {
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
        normalized: String::with_capacity(991),
        canonical: String::with_capacity(992),
    };
    assert_eq!(
        st.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
#[test]
fn caller_cleanup_of_a_successful_owned_name_keeps_original_first_cause() {
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = canonical_tool_name_observed("trustmc", &mut s, site()).unwrap();
    arm.set(true);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.text_drop(out);
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    arm.set(false);
    assert_eq!(
        canonical_tool_name_observed("trustmc", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
