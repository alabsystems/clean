// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn full_actual_valid_text_remains_pending_before_original_publication() {
    let a = minimal();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Writer::new(&mut s, site()).unwrap();
    let mut pending = None;
    produce(&a, &mut pending, &mut out).unwrap();
    assert_eq!(pending, Some(Ok(a.to_canonical_text())));
    assert!(out.text.is_empty());
    let result = finish(&mut pending, Ok(()), &mut out).unwrap();
    assert!(pending.is_none());
    drop(out);
    SignatureAbi::retire_encoding_result_observed(result, &mut s, site()).unwrap();
}
#[test]
fn complete_limit_diagnostic_remains_pending_as_data_not_operational_error() {
    let a = too_many_bytes();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Writer::new(&mut s, site()).unwrap();
    let mut pending = None;
    produce(&a, &mut pending, &mut out).unwrap();
    assert_eq!(
        pending,
        Some(Err("ABI identity exceeds wire byte limit".into()))
    );
    assert!(out.text.is_empty());
    drain(&mut pending, &mut out);
    assert!(pending.is_none());
}
#[test]
fn held_local_failure_wins_later_cleanup_stop_and_consumes_all_payload_capacities() {
    let mut residue = String::with_capacity(4097);
    residue.push_str("partial");
    let rc = residue.capacity();
    let mut owned = String::with_capacity(1009);
    owned.push_str("complete held result");
    let oc = owned.capacity();
    let mut pending = Some(Ok(owned));
    let mut o = Observer {
        record: true,
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Writer {
        session: &mut s,
        site: site(),
        text: residue,
    };
    assert_eq!(
        finish(
            &mut pending,
            Err(ObservedValueError::InvalidRange),
            &mut out
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(pending.is_none());
    assert_eq!(out.text.capacity(), 0);
    drop(out);
    drop(s);
    for n in [rc, oc] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == n)
        );
    }
}
#[test]
fn partial_actual_canonical_text_is_held_and_drained_after_an_interior_stop() {
    let a = minimal();
    let mut base = Observer::default();
    let c = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut out = Writer::new(&mut s, site()).unwrap();
    let mut pending = None;
    produce(&a, &mut pending, &mut out).unwrap();
    let end = c.get();
    drain(&mut pending, &mut out);
    drop(out);
    drop(s);
    let mut found = false;
    for n in 1..64 {
        let cut = end * n / 64 + 1;
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut out = Writer::new(&mut s, site()).unwrap();
        let mut pending = None;
        let result = produce(&a, &mut pending, &mut out);
        if result.is_err() && !out.text.is_empty() {
            assert!(pending.is_none());
            found = true;
            assert!(finish(&mut pending, result, &mut out).is_err());
            assert_eq!(out.text.capacity(), 0);
            break;
        }
        drain(&mut pending, &mut out);
    }
    assert!(found);
}
#[test]
fn public_retirement_drains_both_result_variants_after_stop_without_new_publication() {
    for a in [minimal(), too_many_bytes()] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            record: true,
            arm: Some(arm.clone()),
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let reply = a
            .canonical_text_encoding_result_observed(&mut s, site())
            .unwrap();
        let end = c.get();
        arm.set(true);
        assert!(SignatureAbi::retire_encoding_result_observed(reply, &mut s, site()).is_err());
        arm.set(false);
        assert!(
            a.canonical_text_encoding_result_observed(&mut s, site())
                .is_err()
        );
        drop(s);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn original_healthy_caller_retirement_ends_zero_publication_and_keeps_source_exact() {
    for a in [minimal(), too_many_bytes()] {
        let before = a.clone();
        let mut o = Observer {
            record: true,
            ..Observer::default()
        };
        let c = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let reply = a
            .canonical_text_encoding_result_observed(&mut s, site())
            .unwrap();
        let end = c.get();
        SignatureAbi::retire_encoding_result_observed(reply, &mut s, site()).unwrap();
        assert_eq!(a, before);
        drop(s);
        assert!(
            o.events[end..o.events.len() - 1]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
        let last = o.events.last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 0, 0)
        );
    }
}
