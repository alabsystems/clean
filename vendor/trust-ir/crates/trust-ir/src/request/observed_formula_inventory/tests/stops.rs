// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_inventory_child_copy_and_outer_publication_callback_can_stop() {
    let mut m = Module::new("");
    m.proof_obligations.push(obligation(1, Some(bad())));
    let mut spec = SpecModule::new("M λ\0");
    spec.invariants
        .push(SpecInvariant::new("I 尾\0", "ignored").with_typed(bad()));
    m.spec_modules.push(spec);
    let (_, baseline, bound) = run(&m);
    for cut in 1..=bound {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
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
fn empty_and_absent_carrier_paths_never_convert_stop_into_empty_success() {
    let mut absent = Module::new("");
    absent.proof_obligations.push(obligation(2, None));
    absent.functions.push(function(9, vec![], vec![], vec![]));
    for m in [Module::new(""), absent] {
        let (_, baseline, bound) = run(&m);
        for cut in 1..=bound {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert!(s.first_refusal().is_some());
        }
        assert!(baseline.events.len() >= bound);
    }
}
#[test]
fn successive_complete_groups_and_caller_retirement_share_original_caps() {
    let m = fixture();
    let (_, baseline, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(baseline.bytes + 1)
        } else {
            o.work_cap = Some(baseline.work + 1)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = bundle(m.clone())
            .formula_text_errors_observed(&mut s, site())
            .unwrap();
        retire_native_bundle_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(s.first_refusal().is_some());
    }
}
#[test]
fn final_outer_vector_publication_refusal_does_not_transfer_prior_errors() {
    let m = fixture();
    let (_, baseline, bound) = run(&m);
    assert_eq!(baseline.events[bound - 1].copy_bytes, size_of::<Vec<E>>());
    let mut o = Observer {
        stop: Some(bound),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(s.first_refusal().is_some());
    drop(s);
    assert!(o.events.len() > bound);
    assert!(
        o.events[bound..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn original_site_zero_fuel_and_prior_cause_stay_unchanged() {
    let m = fixture();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(options, &mut o);
    let out = bundle(m.clone())
        .formula_text_errors_observed(&mut s, site())
        .unwrap();
    retire_native_bundle_errors_observed(out, &mut s, site()).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    let mut o = Observer {
        stop: Some(1),
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
        bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original formula inventory stop"
    );
}
#[test]
fn later_leads_to_leaf_is_observed_after_the_first_leaf_and_error() {
    let mut m = Module::new("");
    let mut spec = SpecModule::new("M");
    spec.temporal
        .push(SpecTemporal::new("T", TemporalForm::LeadsTo(bad(), bad())));
    m.spec_modules.push(spec);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    let source = FormulaSiteRef::SpecTemporal {
        machine: "M",
        property: "T",
    };
    state.formula(source, &bad(), &m, &mut w).unwrap();
    let first = calls.get();
    state.formula(source, &bad(), &m, &mut w).unwrap();
    drain(&mut state, &mut w);
    drop(w);
    drop(s);
    let cut = first + 1;
    let mut o = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.formula(source, &bad(), &m, &mut w).unwrap();
    assert_eq!(
        state.formula(source, &bad(), &m, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.errors.len(), 1);
    assert_eq!(
        state.errors[0],
        E::FormulaTextsDisagree {
            site: source.into_owned()
        }
    );
    drain(&mut state, &mut w);
    assert!(empty(&state));
}
#[test]
fn any_cleanup_refusal_prevents_complete_group_success_and_drains_prior_errors() {
    let mut m = Module::new("");
    m.proof_obligations.push(obligation(1, Some(bad())));
    let mut o = Observer {
        cleanup_after: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        bundle(m.clone()).formula_text_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(s.first_refusal().is_some());
    drop(s);
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 8
    );
    assert_eq!(
        o.events.last().unwrap().phase,
        ExecutionPhase::ScratchRetirement
    );
}

#[test]
fn interrupt_cause_is_sticky_for_later_full_inventory_calls_without_new_owner() {
    let b = bundle(fixture());
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        b.formula_text_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    arm.set(false);
    assert_eq!(
        b.formula_text_errors_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
