// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn actual_partial_and_complete_preimage_and_full_prover_stay_parent_owned() {
    let c = rich();
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.reference(&c, &mut w).unwrap();
    let end = calls.get();
    state.retire(&mut w);
    drop(w);
    drop(s);
    let (mut partial, mut full_prover, mut full_bytes) = (false, false, false);
    let original = ordinary_bytes(&c);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut state = State::default();
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            state.reference(&c, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        partial |= !state.bytes.is_empty();
        full_prover |= state.prover == c.prover;
        full_bytes |= state.bytes == original;
        assert!(original.starts_with(&state.bytes));
        state.retire(&mut w);
        assert!(state.reference.is_none());
        assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
        assert_eq!(w.session.first_refusal().unwrap().cause, "identity stop");
    }
    assert!(partial && full_prover && full_bytes);
}
#[test]
fn complete_reference_stays_held_when_actual_public_cleanup_refuses() {
    let c = rich();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.reference(&c, &mut w).unwrap();
    arm.set(true);
    state.retire_bytes(&mut w);
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
    assert_eq!(state.reference.as_ref().unwrap(), &c.lineage_ref());
    assert!(w.publication().is_err());
    state.retire(&mut w);
    assert!(state.reference.is_none());
    assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn successful_owned_selector_requires_original_caller_terminal_or_sticky_retirement() {
    let c = rich();
    for refuse in [false, true] {
        let arm = Rc::new(Cell::new(false));
        let mut o = Observer {
            cleanup: Some(arm.clone()),
            ..Observer::default()
        };
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = c.lineage_ref_observed(&mut s, site()).unwrap();
        assert_eq!(out, c.lineage_ref());
        let begin = calls.get();
        arm.set(refuse);
        let result = out.retire_observed(&mut s, site());
        if refuse {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        } else {
            result.unwrap();
        }
        drop(s);
        let tail = &o.events[begin..];
        assert!(tail.iter().all(|e| e.site == site()));
        if refuse {
            assert!(
                tail.iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        } else {
            assert!(!tail[..tail.len() - 1].is_empty());
            assert!(
                tail[..tail.len() - 1]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
            assert_eq!(
                (
                    tail.last().unwrap().phase,
                    tail.last().unwrap().work,
                    tail.last().unwrap().copy_bytes
                ),
                (ExecutionPhase::Publication, 0, 0)
            );
        }
    }
}
