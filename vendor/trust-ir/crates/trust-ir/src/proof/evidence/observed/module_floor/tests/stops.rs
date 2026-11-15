// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_false_floor_and_false_publication_callback_is_refusable() {
    let (m, row, mut c) = fixture();
    c.obligation = ProofId::new(99);
    let (_, base, end) = observed(&m, &row, &c);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn actual_module_lineage_child_and_every_publication_can_refuse() {
    let (m, row, c) = fixture();
    let (_, base, end) = observed(&m, &row, &c);
    let mut cuts = vec![1, end];
    for n in 1..65 {
        cuts.push(n * end / 65 + 1);
    }
    for (at, p) in base.events[..end].iter().enumerate() {
        if p.phase == ExecutionPhase::Publication {
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
        assert!(
            c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
                .is_err()
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn one_cumulative_original_work_and_copy_limit_covers_two_complete_floors() {
    let (m, row, c) = fixture();
    let (_, base, _) = observed(&m, &row, &c);
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
        assert!(
            c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
                .unwrap()
        );
        assert!(
            c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_is_sticky_and_zero_instruction_fuel_is_not_renewed() {
    let (m, row, c) = fixture();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert!(
        c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
            .is_err()
    );
    assert_eq!(s.remaining_fuel(), 0);
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
