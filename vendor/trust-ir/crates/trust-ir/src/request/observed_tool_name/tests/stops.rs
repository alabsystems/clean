// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    clippy::needless_borrow,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_byte_growth_alias_suffix_cleanup_and_publication_callback_can_stop() {
    for name in [
        " !TRUST_MC_NaTiVe-V2 ",
        "other tool--9",
        " \u{2003}--🦀",
        "trust-ir",
    ] {
        let (_, base, end) = observed(name);
        for (i, expected) in base.events[..end].iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                canonical_tool_name_observed(&name, &mut s, site()),
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
fn cumulative_original_work_cap_cannot_restart_between_normalizations() {
    let name = "TRUST_MC-native";
    let (_, base, _) = observed(name);
    let mut o = Observer {
        work_cap: Some(base.work),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = canonical_tool_name_observed(name, &mut s, site()).unwrap();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.record(1, size_of::<String>());
    w.text_drop(out);
    drop(w);
    assert_eq!(
        canonical_tool_name_observed(name, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "work");
}
#[test]
fn cumulative_original_copy_cap_cannot_restart_between_normalizations() {
    let name = "TRUST_MC-native";
    let (_, base, _) = observed(name);
    let mut o = Observer {
        byte_cap: Some(base.bytes),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = canonical_tool_name_observed(name, &mut s, site()).unwrap();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.record(1, size_of::<String>());
    w.text_drop(out);
    drop(w);
    assert_eq!(
        canonical_tool_name_observed(name, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "copy");
}
#[test]
fn original_armed_interrupt_remains_sticky_after_disarming() {
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        canonical_tool_name_observed("trustmc", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        canonical_tool_name_observed("trustmc", &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_disable_structural_normalization() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let out = canonical_tool_name_observed("TRUST_MC-native", &mut s, site()).unwrap();
    assert_eq!(out, "trust_mc-native");
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.text_drop(out);
    drop(w);
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_publication_refusal_never_returns_a_partial_name() {
    for name in names() {
        let (_, base, end) = observed(&name);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            canonical_tool_name_observed(&name, &mut s, site()),
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
