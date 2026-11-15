// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(a: &SignatureAbi, request: Request<'_>) {
    let original_request = match &request {
        Request::Validate(sig) => Request::Validate(sig),
        Request::Target(target) => Request::Target(*target),
        Request::Function(f) => Request::Function(f),
    };
    let (_, baseline, end) = run(a, original_request);
    let start = semantic_start(&baseline.events[..end]);
    // Every actual semantic/cleanup/publication callback after the unchanged
    // real wire child, plus dispersed actual wire-interior boundaries. No
    // exhaustive unchanged codec rerun or artificial prewalk is claimed.
    let mut cuts: Vec<usize> = (start + 1..=end).collect();
    cuts.extend([1, 2]);
    for n in 1..=16 {
        if start != 0 {
            cuts.push((start * n / 16).max(1));
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
        let result = match &request {
            Request::Validate(sig) => a.validate_observed(sig, &mut s, site()),
            Request::Target(t) => a.validate_target_observed(*t, &mut s, site()),
            Request::Function(f) => a.reconcile_function_observed(f, &mut s, site()),
        };
        assert_eq!(
            result,
            Err(ObservedValueError::AdmissionRefused),
            "cut {cut}"
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original signature semantic stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_semantic_validation_callback_after_real_wire_and_selected_wire_custody_refuses() {
    let (a, s) = minimal();
    every(&a, Request::Validate(&s));
    let (mut a, s) = direct();
    a.arguments[0].bindings[0].carrier_bytes = 4;
    every(&a, Request::Validate(&s));
}
#[test]
fn every_target_chunk_and_every_matching_legacy_owner_callback_refuses() {
    let (a, _) = minimal();
    let mut t = target(&a);
    t.triple.push('x');
    every(&a, Request::Target(Some(&t)));
    let (a, _) = packed();
    let mut f = function();
    f.attrs.params.push(ParamAttrs {
        ext: ArgExt::SignExt,
        ..ParamAttrs::default()
    });
    every(&a, Request::Function(&f));
}
#[test]
fn complete_repeated_semantic_calls_share_original_cumulative_work_and_copy() {
    let (a, sig) = minimal();
    let (_, base, end) = run(&a, Request::Validate(&sig));
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(a.validate_observed(&sig, &mut s, site()).unwrap(), Ok(()));
        assert_eq!(
            a.validate_observed(&sig, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_zero_fuel_and_sticky_interruption_preserve_all_three_public_routes() {
    let (a, sig) = minimal();
    let t = target(&a);
    let f = function();
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        interrupt: Some(arm.clone()),
        ..Observer::default()
    };
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    assert!(a.validate_observed(&sig, &mut s, site()).unwrap().is_ok());
    assert_eq!(s.remaining_fuel(), 0);
    arm.set(true);
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
        a.validate_observed(&sig, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        a.validate_target_observed(Some(&t), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        a.reconcile_function_observed(&f, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
