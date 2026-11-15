// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_schema_wire_empty_guarded_count_hash_compare_and_publication_fee_refuses() {
    let b = clean();
    let (_, base, end) = observed(&b);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.identity_prefix_errors_observed(&mut s, site()),
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
fn every_actual_unencodable_ordered_diagnostic_and_tail_cleanup_fee_refuses() {
    let b = bad();
    let (_, base, end) = observed(&b);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.identity_prefix_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
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
fn child_writer_real_hash_and_caller_retirement_share_one_cumulative_work_copy() {
    let b = clean();
    let (_, base, _) = observed(&b);
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
        let rows = b.identity_prefix_errors_observed(&mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(b.identity_prefix_errors_observed(&mut s, site()).is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn clearing_interrupt_does_not_renew_original_owner_and_zero_fuel_stays_zero() {
    let b = clean();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b.identity_prefix_errors_observed(&mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.identity_prefix_errors_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(b.identity_prefix_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn final_whole_result_publication_cut_never_transfers_any_prefix() {
    for b in [clean(), bad()] {
        let (_, base, end) = observed(&b);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(b.identity_prefix_errors_observed(&mut s, site()).is_err());
        drop(s);
        assert!(
            o.events[end..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn cleanup_only_refusal_prevents_empty_or_partial_result_without_hashing_bad_module() {
    for b in [clean(), bad()] {
        let mut o = Observer {
            retirement_stop: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.identity_prefix_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    }
}
