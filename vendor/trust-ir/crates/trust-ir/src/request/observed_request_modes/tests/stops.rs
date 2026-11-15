// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_mode_scan_error_transport_cleanup_and_publication_can_stop() {
    for input in [bad(), bad_wp(), bad_diagnostics()] {
        let (_, base, end) = observed(&input);
        for (i, expected) in base.events[..end].iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                input.observed(&mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, *expected);
            assert_eq!(s.first_refusal().unwrap().cause, "interior");
            assert_eq!(&o.events[..=i], &base.events[..=i]);
            assert!(
                o.events[i + 1..]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn cumulative_work_and_copy_remain_one_original_budget_across_distinct_guards() {
    let input = bad_wp();
    let (_, base, _) = observed(&input);
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                byte_cap: Some(base.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(base.work),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = input.observed(&mut s).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert_eq!(
            bad_diagnostics().observed(&mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_cannot_be_reset_for_the_second_guard() {
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(bad_wp().observed(&mut s).is_err());
    arm.set(false);
    assert!(bad().observed(&mut s).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_mode_or_diagnostic_guards() {
    for input in [bad(), bad_wp(), bad_diagnostics()] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        let rows = input.observed(&mut s).unwrap();
        assert_eq!(rows, input.ordinary());
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert_eq!(s.remaining_fuel(), 0);
    }
}
#[test]
fn full_error_publication_refusal_never_returns_an_error_prefix() {
    for input in [bad(), bad_wp(), bad_diagnostics()] {
        let (_, base, end) = observed(&input);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            input.observed(&mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_second_independent_wp_scan_can_refuse_after_first_scan_fails() {
    let input = bad_wp();
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
    let shape = (
        3,
        size_of::<NativeReplayAtomKind>()
            + size_of::<Option<NativeAssertionId>>()
            + size_of::<bool>(),
    );
    let hits: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.phase == ExecutionPhase::Validation && (p.work, p.copy_bytes) == shape)
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(hits.len(), 24);
    let mut o = Observer {
        stop: Some(hits[18]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    let result = body(&mut st, &input, &mut w);
    assert!(result.is_err());
    assert!(st.errors.is_empty());
    assert!(st.pending.is_none());
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn successful_independent_search_short_circuits_before_unused_tail() {
    let mut r = wp();
    r.mode = WpMode::StrongestPostcondition;
    r.provenance.replay_context.atoms = vec![
        atom(NativeReplayAtomKind::Assumption, false),
        atom(NativeReplayAtomKind::Assertion, true),
    ];
    let (_, a, end) = observed(&Input::Wp(r.clone()));
    r.provenance
        .replay_context
        .atoms
        .extend(vec![atom(NativeReplayAtomKind::Assertion, false); 1000]);
    let (_, b, end_b) = observed(&Input::Wp(r));
    assert_eq!(&a.events[..end], &b.events[..end_b]);
}
#[test]
fn retirement_only_copy_refusal_is_checked_before_healthy_output() {
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    assert!(st.finish(Ok(()), &mut w).is_err());
    empty(&st);
    assert_eq!(w.session.first_refusal().unwrap().cause, "copy");
}
