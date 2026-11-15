// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_child_name_field_growth_cleanup_and_publication_can_stop() {
    let f = fixture();
    for c in cases() {
        let (_, base, end) = observed(&f, c, Suite::TrustMc);
        for (i, expected) in base.events[..end].iter().enumerate() {
            let mut o = Observer {
                stop: Some(i + 1),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                run(check(&f, c, Suite::TrustMc), &mut s, site()),
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
fn work_and_copy_caps_remain_cumulative_across_all_four_checks() {
    let f = fixture();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    for c in cases() {
        let rows = run(check(&f, c, Suite::TrustMc), &mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
    for copy in [false, true] {
        let mut o = if copy {
            Observer {
                byte_cap: Some(base.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(base.work - 1),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut stopped = false;
        for c in cases() {
            match run(check(&f, c, Suite::TrustMc), &mut s, site()) {
                Ok(rows) => {
                    if retire_native_bundle_errors_observed(rows, &mut s, site()).is_err() {
                        stopped = true;
                    }
                }
                Err(_) => stopped = true,
            }
        }
        assert!(stopped);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        assert!(run(check(&f, Case::Tool, Suite::TrustMc), &mut s, site()).is_err());
    }
}
#[test]
fn original_interrupt_is_sticky_even_after_disarming() {
    let f = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(run(check(&f, Case::Replay, Suite::TrustMc), &mut s, site()).is_err());
    arm.set(false);
    assert!(run(check(&f, Case::Verifier, Suite::TrustMc), &mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_is_unchanged_through_all_metadata_children() {
    let f = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    for c in cases() {
        let rows = run(check(&f, c, Suite::TrustMc), &mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn every_full_diagnostic_publication_can_be_refused_without_a_prefix() {
    let f = fixture();
    for c in cases() {
        let (_, base, end) = observed(&f, c, Suite::TrustMc);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(run(check(&f, c, Suite::TrustMc), &mut s, site()).is_err());
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn long_whitespace_fields_poll_the_original_owner_inside_the_scan() {
    let mut f = named("tool");
    f.tool.version = Some(" \u{2003}".repeat(400));
    let (_, base, end) = observed(&f, Case::Tool, Suite::TrustMc);
    let cut = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, p)| p.work == 64)
        .nth(333)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(run(check(&f, Case::Tool, Suite::TrustMc), &mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
