// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_private_lookup_raw_name_decimal_and_output_fee_can_stop() {
    let m = module();
    let row = node(900);
    let (_, base, end) = mapped(&m, &row);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut r = Render::default();
        assert_eq!(
            r.map(&m, &row, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        drain(&mut r, &mut w);
        empty(&r);
        drop(w);
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
fn actual_complete_child_and_parent_capture_mapping_retirement_publication_refuse() {
    let b = actual();
    let (_, base, end) = observed(&b);
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
            b.wire_identity_errors_observed(&mut s, site()),
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
fn work_and_copy_accumulate_across_child_mapping_and_original_caller_disposal() {
    let b = actual();
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
        let rows = b.wire_identity_errors_observed(&mut s, site()).unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(b.wire_identity_errors_observed(&mut s, site()).is_err());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_remains_sticky_after_flag_clears_and_zero_fuel_stays_zero() {
    let b = actual();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b.wire_identity_errors_observed(&mut s, site()).unwrap();
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.wire_identity_errors_observed(&mut s, site()).is_err());
    arm.set(false);
    assert!(b.wire_identity_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn final_whole_error_vector_publication_refusal_never_exposes_prefix() {
    let b = actual();
    let (_, base, end) = observed(&b);
    assert_eq!(base.events[end - 1].copy_bytes, size_of::<Vec<E>>());
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.wire_identity_errors_observed(&mut s, site()).is_err());
    drop(s);
    assert!(
        o.events[end..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn late_fallback_lookup_is_observed_inside_actual_rows_before_picking_a_name() {
    let mut m = Module::new("");
    m.functions = (0..35).map(|_| function(7, "not target")).collect();
    m.functions.push(function(900, "late"));
    let row = node(900);
    let (_, base, end) = mapped(&m, &row);
    let hits: Vec<_> = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, p)| {
            p.phase == ExecutionPhase::Validation
                && p.copy_bytes == 2 * size_of::<FuncId>() + size_of::<bool>()
        })
        .map(|(at, _)| at + 1)
        .collect();
    assert_eq!(hits.len(), 36);
    let mut o = Observer {
        stop: Some(hits[24]),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut r = Render::default();
    assert!(r.map(&m, &row, &mut w).is_err());
    assert_eq!(r.text, "function '");
    assert!(r.pending.is_none() && r.errors.is_empty());
    drain(&mut r, &mut w);
    empty(&r);
}
