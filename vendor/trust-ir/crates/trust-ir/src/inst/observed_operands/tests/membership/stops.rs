// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_case_operand_metadata_retirement_and_publication_callback_refuses() {
    for inst in all() {
        for needle in [v(1), v(4), v(99)] {
            let (_, baseline) = run(&inst, needle);
            for cut in 1..=baseline.events.len() {
                let mut o = Observer {
                    stop_at: Some(cut),
                    ..Observer::default()
                };
                let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
                assert_eq!(
                    inst.uses_value_operand_observed(needle, &mut s, site()),
                    Err(ObservedValueError::AdmissionRefused)
                );
                assert_eq!(s.first_refusal().unwrap().cause, "original stop");
                drop(s);
                assert_eq!(&o.events[..cut], &baseline.events[..cut]);
                assert!(
                    o.events[cut..]
                        .iter()
                        .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
                );
            }
        }
    }
}
#[test]
fn repeated_queries_share_original_cumulative_work_and_copy_without_regrant() {
    let inst = switch(false, 3);
    let (_, baseline) = run(&inst, v(99));
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes)
        } else {
            o.work_cap = Some(baseline.work)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            !inst
                .uses_value_operand_observed(v(99), &mut s, site())
                .unwrap()
        );
        assert_eq!(
            inst.uses_value_operand_observed(v(99), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_keep_original_site_and_cause() {
    let inst = Inst::Return {
        values: ids(&[1, 2]),
    };
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert!(
        inst.uses_value_operand_observed(v(2), &mut s, site())
            .unwrap()
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        inst.uses_value_operand_observed(v(1), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original stop");
}
#[test]
fn cancelled_empty_case_iteration_is_not_semantic_false() {
    let inst = switch(true, 100);
    let (_, baseline) = run(&inst, v(99));
    let cut = baseline.events.len() / 2;
    let mut o = Observer {
        stop_at: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        inst.uses_value_operand_observed(v(99), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
