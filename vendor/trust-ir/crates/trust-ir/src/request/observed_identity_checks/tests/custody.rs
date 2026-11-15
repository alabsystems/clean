// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_raw_and_canonical_labels_are_pending_before_both_output_fees() {
    let raw = "WRONG'\0λ🦀".repeat(700);
    let canonical = crate::request::canonical_tool_name(&raw);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        canonical: canonical.clone(),
        ..State::default()
    };
    st.named(&raw, Kind::Verifier(request(), Suite::TrustMc), &mut w)
        .unwrap();
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
        let mut st = State {
            canonical: canonical.clone(),
            ..State::default()
        };
        let result = st.named(&raw, Kind::Verifier(request(), Suite::TrustMc), &mut w);
        if matches!(&st.pending,Some(E::ExpectedVerifierIdentityMismatch{verifier,canonical:actual,..}) if verifier==&raw&&actual==&canonical)
        {
            assert!(result.is_err());
            assert!(st.errors.is_empty());
            assert_eq!(st.text.capacity() + st.canonical.capacity(), 0);
            found += 1;
        }
        drain(&mut st, &mut w);
        empty(&st);
    }
    assert!(found >= 2);
}
#[test]
fn child_canonical_string_is_captured_before_any_later_parent_fee() {
    let f = named("WRONG");
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.verifier(request(), Suite::TrustMc, &f.tool, &mut w)
        .unwrap();
    drain(&mut st, &mut w);
    let cut = base
        .events
        .iter()
        .position(|p| p.phase == ExecutionPhase::Publication && p.copy_bytes == size_of::<String>())
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
    let result = st.verifier(request(), Suite::TrustMc, &f.tool, &mut w);
    assert!(result.is_err());
    assert_eq!(st.canonical, "wrong");
    assert!(st.pending.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn partial_raw_label_and_whole_child_name_both_drain_after_copy_stop() {
    let raw = "WRONGλ🦀".repeat(700);
    let canonical = crate::request::canonical_tool_name(&raw);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State {
        canonical: canonical.clone(),
        ..State::default()
    };
    st.named(&raw, Kind::Replay(request(), Suite::TrustMc), &mut w)
        .unwrap();
    drain(&mut st, &mut w);
    let cut = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.work == 1024 && p.copy_bytes == 1024)
        .nth(2)
        .unwrap()
        .0
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
    let mut st = State {
        canonical: canonical.clone(),
        ..State::default()
    };
    let result = st.named(&raw, Kind::Replay(request(), Suite::TrustMc), &mut w);
    assert!(result.is_err());
    assert_eq!(st.canonical, canonical);
    assert_eq!(st.text, &raw[..1024]);
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn held_local_error_has_precedence_over_later_cleanup_refusal() {
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
        canonical: "full".repeat(400),
        text: "partial".repeat(400),
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
fn nonzero_retirement_copy_stop_consumes_every_owned_store() {
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
        canonical: String::with_capacity(991),
        text: String::with_capacity(992),
        pending: Some(E::DuplicateEvidenceArtifact {
            request: request(),
            name: "full".repeat(100),
        }),
        errors: vec![E::EmptyRequests],
    };
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
#[test]
fn successful_caller_retirement_keeps_terminal_receipt_and_stopped_cause() {
    let f = fixture();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = run(check(&f, Case::Replay, Suite::TrustMc), &mut s, site()).unwrap();
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
    let rows = run(check(&f, Case::Certificate, Suite::TrustMc), &mut s, site()).unwrap();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(run(check(&f, Case::Verifier, Suite::TrustMc), &mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
