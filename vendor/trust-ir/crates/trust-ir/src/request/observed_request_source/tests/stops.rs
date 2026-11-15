// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_actual_root_child_membership_sidecar_function_and_publication_callback_can_stop() {
    let (b, r) = bad();
    let (_, base, end) = observed(&b, &r);
    for (at, p) in base.events[..end].iter().enumerate() {
        let mut o = Observer {
            stop: Some(at + 1),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            b.request_source_errors_observed(&r, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, *p);
        assert_eq!(&o.events[..=at], &base.events[..=at]);
        assert!(
            o.events[at + 1..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn all_child_and_parent_work_and_copy_use_one_original_cumulative_budget() {
    let (b, r) = bad();
    let (_, base, _) = observed(&b, &r);
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
        let rows = b
            .request_source_errors_observed(&r, &mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
        assert!(
            b.request_source_errors_observed(&r, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_stays_sticky_across_parent_and_child_calls() {
    let (b, r) = bad();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn zero_instruction_fuel_does_not_skip_full_source_checks() {
    let (b, r) = bad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let rows = b
        .request_source_errors_observed(&r, &mut s, site())
        .unwrap();
    assert_eq!(rows, ordinary(&b, &r));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
}
#[test]
fn final_whole_result_publication_refusal_never_exposes_prior_error_prefix() {
    let (b, r) = bad();
    let (_, base, end) = observed(&b, &r);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn actual_whole_lineage_child_publication_can_refuse_without_parent_continuation() {
    let (b, r) = bad();
    let (_, base, end) = observed(&b, &r);
    let cut = base.events[..end]
        .iter()
        .position(|p| {
            p.phase == ExecutionPhase::Publication
                && p.copy_bytes == size_of::<NativeRequestLineage<'_>>()
        })
        .unwrap()
        + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    assert!(
        o.events[cut..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn genuine_sparse_function_fallback_uses_observed_rows_and_can_refuse_late() {
    let (mut b, mut r) = fixture();
    let mut last = b.module.functions[0].clone();
    last.id = FuncId::new(999);
    let other = b.module.functions[0].clone();
    b.module.functions = vec![other; 24];
    b.module.functions.push(last);
    function(&mut r, Some(FuncId::new(999)));
    let (_, base, end) = observed(&b, &r);
    let shape = (1, 2 * size_of::<FuncId>() + size_of::<bool>());
    let cuts: Vec<_> = base.events[..end]
        .iter()
        .enumerate()
        .filter(|(_, p)| p.phase == ExecutionPhase::Validation && (p.work, p.copy_bytes) == shape)
        .map(|(at, _)| at + 1)
        .collect();
    assert!(cuts.len() >= 24);
    let cut = cuts[cuts.len() - 5];
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        b.request_source_errors_observed(&r, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
}
#[test]
fn cleanup_only_refusal_is_checked_before_empty_output_publication() {
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
}
