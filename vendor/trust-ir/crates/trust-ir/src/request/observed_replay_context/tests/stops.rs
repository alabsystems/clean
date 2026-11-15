// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_scan_formula_digest_binding_error_and_publication_can_refuse() {
    let input = bad();
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
#[test]
fn all_children_share_one_original_cumulative_work_and_copy_budget() {
    let input = bad();
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
            input.observed(&mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_stays_stopped_across_all_actual_child_calls() {
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(bad().observed(&mut s).is_err());
    arm.set(false);
    assert!(fixture().observed(&mut s).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_still_checks_all_replay_metadata() {
    let input = bad();
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
#[test]
fn final_whole_error_publication_refusal_returns_no_prefix() {
    let input = bad();
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
}
#[test]
fn late_physical_sidecar_scan_refuses_after_full_earlier_errors_remain_owned() {
    let mut input = bad();
    let target = input.facts.obligation_sources.pop().unwrap();
    input.facts.obligation_sources = vec![source(0); 20];
    input.facts.obligation_sources.push(target);
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
    let compare = (1, 2 * size_of::<ProofId>() + size_of::<bool>());
    let cuts: Vec<_> = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, p)| p.phase == ExecutionPhase::Validation && (p.work, p.copy_bytes) == compare)
        .map(|(i, _)| i + 1)
        .collect();
    assert!(cuts.len() > 20);
    let cut = cuts[cuts.len() - 5];
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
    assert!(result.is_err());
    assert!(
        st.errors
            .iter()
            .any(|e| matches!(e, E::ReplayAtomObligationNotRequested { .. }))
    );
    assert!(
        !st.errors
            .iter()
            .any(|e| matches!(e, E::ReplayAtomAssertionMismatch { .. }))
    );
    assert!(st.finish(result, &mut w).is_err());
    empty(&st);
}
#[test]
fn child_payload_digest_publication_can_refuse_before_binding_errors() {
    let input = bad();
    let (_, base, end) = observed(&input);
    let cut = base.events[..end]
        .iter()
        .position(|p| {
            p.phase == ExecutionPhase::CanonicalDigest
                && p.work == 128
                && p.copy_bytes == size_of::<ProofDigest>()
        })
        .unwrap()
        + 2;
    assert_eq!(base.events[cut - 1].phase, ExecutionPhase::Publication);
    assert_eq!(
        (base.events[cut - 1].work, base.events[cut - 1].copy_bytes),
        (0, 0)
    );
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(input.observed(&mut s).is_err());
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn cleanup_only_refusal_is_checked_before_healthy_empty_output() {
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
