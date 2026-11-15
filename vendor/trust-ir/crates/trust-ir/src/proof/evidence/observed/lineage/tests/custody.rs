// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn complete_content_is_caller_owned_until_explicit_original_retirement() {
    let (m, row, _) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let bytes = row
        .clean_cic_lineage_content_v8_observed(&c, &mut s, site())
        .unwrap()
        .unwrap();
    assert_eq!(Some(bytes.clone()), original_content(&row, &c));
    let begin = calls.get();
    ProofDigest::retire_canonical_bytes_observed(bytes, &mut s, site()).unwrap();
    drop(s);
    let tail = &o.events[begin..];
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
#[test]
fn every_partial_content_stop_leaves_actual_prefix_owned_until_full_cleanup() {
    let (m, row, _) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let expected = original_content(&row, &c).unwrap();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(state.content_v8(&row, &c, &mut w).unwrap());
    let end = calls.get();
    state.retire(&mut w);
    drop(w);
    drop(s);
    let mut saw = false;
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
            state.content_v8(&row, &c, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(expected.starts_with(&state.bytes));
        saw |= !state.bytes.is_empty();
        state.retire(&mut w);
        assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
        assert!(state.reference.is_none());
    }
    assert!(saw);
}
#[test]
fn actual_constructor_and_field_continuations_stay_owned_before_sort_cleanup() {
    let sort = ClauseSort::Datatype {
        name: "D".into(),
        constructors: vec![
            (
                "a".into(),
                vec![(
                    "f".into(),
                    ClauseSort::Array(Box::new(ClauseSort::Bool), Box::new(ClauseSort::Int)),
                )],
            ),
            ("b".into(), vec![]),
        ],
    };
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut machine = super::super::sorts::Machine::default();
    machine.run(&mut state, &sort, &mut w).unwrap();
    let end = calls.get();
    machine.retire(&mut w);
    state.retire(&mut w);
    drop(w);
    drop(s);
    let mut saw = false;
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
        let mut machine = super::super::sorts::Machine::default();
        assert_eq!(
            machine.run(&mut state, &sort, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        let (len, cap) = machine.storage();
        saw |= len > 0 && cap >= len;
        machine.retire(&mut w);
        assert_eq!(machine.storage(), (0, 0));
        state.retire(&mut w);
        assert_eq!(state.bytes.capacity(), 0);
        assert_eq!(w.session.first_refusal().unwrap().cause, "lineage stop");
    }
    assert!(saw);
}
#[test]
fn full_owned_preimage_retirement_keeps_original_stop_and_never_returns_a_suffix() {
    let bytes = vec![7; 2501];
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    ProofDigest::retire_canonical_bytes_observed(bytes.clone(), &mut s, site()).unwrap();
    drop(s);
    for cut in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            ProofDigest::retire_canonical_bytes_observed(bytes.clone(), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "lineage stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
