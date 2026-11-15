// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_small_collector_writer_and_publication_callback_can_refuse() {
    let m = Module::new("small");
    let (_, base, end) = run(&m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            m.wire_image_refusals_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn actual_whole_mixed_classes_keep_original_refusal_at_all_changed_stages() {
    let m = all();
    let (_, base, end) = run(&m);
    let mut cuts = vec![1, 2, 3, end];
    for n in 1..48 {
        cuts.push(end * n / 48 + 1);
    }
    for (at, p) in base.events[..end].iter().enumerate() {
        if matches!(
            p.phase,
            ExecutionPhase::Publication | ExecutionPhase::ScratchRetirement
        ) {
            cuts.push(at + 1);
        }
    }
    cuts.sort_unstable();
    cuts.dedup();
    for cut in cuts {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            m.wire_image_refusals_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
        drop(s);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
#[cfg(target_pointer_width = "64")]
fn every_direct_six_class_capture_rank_growth_transfer_and_drop_callback_refuses() {
    let mut base = Observer::default();
    let rows = direct(&mut base).unwrap();
    assert_eq!(rows, ordinary_feed());
    for cut in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        assert_eq!(direct(&mut o), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn both_complete_calls_and_output_retirement_share_original_cumulative_budgets() {
    let m = module();
    let (_, base, _) = run(&m);
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
        let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
        retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
        assert_eq!(
            m.wire_image_refusals_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn a_cleared_interrupt_cannot_start_a_new_collector_on_the_original_session() {
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(all().wire_image_refusals_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(
        module()
            .wire_image_refusals_observed(&mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_skip_raw_writer_refusal_rules() {
    let m = all();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = m.wire_image_refusals_observed(&mut s, site()).unwrap();
    assert_eq!(rows, m.wire_image_refusals());
    retire_wire_image_refusals_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn whole_output_publication_cut_hides_all_previously_collected_classes() {
    let m = all();
    let (_, base, end) = run(&m);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        m.wire_image_refusals_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn retirement_only_stop_never_becomes_empty_or_partial_refusal_success() {
    for m in [module(), all()] {
        let mut o = Observer {
            retirement_stop: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            m.wire_image_refusals_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    }
}
