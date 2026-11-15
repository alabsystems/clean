// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn source<'a>(machine: &'a str, label: &'a str) -> FormulaSiteRef<'a> {
    FormulaSiteRef::SpecInvariant {
        machine,
        invariant: label,
    }
}
fn end(machine: &str, label: &str) -> usize {
    let m = Module::new("");
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.formula(source(machine, label), &bad(), &m, &mut w)
        .unwrap();
    let n = c.get();
    drain(&mut st, &mut w);
    n
}
#[test]
fn both_full_raw_labels_in_pending_error_survive_reserve_and_transport_cuts() {
    let machine = "whole M λ\0尾";
    let label = "whole I 尾\0λ";
    let m = Module::new("");
    let limit = end(machine, label);
    let mut found = 0;
    for cut in 1..=limit {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.formula(source(machine, label), &bad(), &m, &mut w);
        if result.is_err() && st.pending.is_some() {
            assert_eq!(
                st.pending,
                Some(E::FormulaTextsDisagree {
                    site: FormulaSite::SpecInvariant {
                        machine: machine.into(),
                        invariant: label.into()
                    }
                })
            );
            assert!(st.machine.is_empty() && st.label.is_empty() && st.errors.is_empty());
            found += 1;
            assert!(st.finish(result, &mut w).is_err());
            assert!(empty(&st));
        } else {
            drain(&mut st, &mut w);
        }
    }
    assert!(found >= 2);
}
#[test]
fn actual_partial_machine_copy_is_owned_before_every_later_fee() {
    let machine = "a".repeat(1024) + &"λ".repeat(700);
    let m = Module::new("");
    let limit = end(&machine, "I");
    let mut found = false;
    for cut in 1..=limit {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.formula(source(&machine, "I"), &bad(), &m, &mut w);
        if result.is_err() && st.machine.len() == 1024 {
            assert_eq!(st.machine, "a".repeat(1024));
            assert_eq!(st.label.capacity(), 0);
            assert!(st.pending.is_none());
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            assert!(empty(&st));
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn full_machine_and_partial_label_keep_prior_errors_until_consuming_cleanup() {
    let machine = "M λ\0尾";
    let label = "b".repeat(1024) + &"尾".repeat(700);
    let m = Module::new("");
    let limit = end(machine, &label);
    let mut found = false;
    for cut in 1..=limit {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State {
            errors: vec![prior()],
            ..State::default()
        };
        let result = st.formula(source(machine, &label), &bad(), &m, &mut w);
        if result.is_err() && st.label.len() == 1024 {
            assert_eq!(st.machine, machine);
            assert_eq!(st.label, "b".repeat(1024));
            assert_eq!(st.errors, vec![prior()]);
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            assert!(empty(&st));
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
#[test]
fn held_local_error_wins_cleanup_refusal_and_all_spare_stores_are_drained() {
    let mut machine = String::with_capacity(4011);
    machine.push_str("partial");
    let mc = machine.capacity();
    let mut label = String::with_capacity(2009);
    label.push_str("label");
    let lc = label.capacity();
    let mut errors = Vec::with_capacity(27);
    errors.push(prior());
    let ec = errors.capacity();
    let mut st = State {
        machine,
        label,
        pending: Some(prior()),
        errors,
    };
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        st.finish(Err(ObservedValueError::InvalidRange), &mut w),
        Err(ObservedValueError::InvalidRange)
    );
    assert!(empty(&st));
    drop(w);
    drop(s);
    for n in [mc, lc, ec * size_of::<E>()] {
        assert!(
            o.events
                .iter()
                .any(|p| p.phase == ExecutionPhase::ScratchRetirement && p.copy_bytes == n)
        );
    }
}
#[test]
fn healthy_success_keeps_all_owned_output_until_original_caller_retirement() {
    let b = bundle(fixture());
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.formula_text_errors_observed(&mut s, site()).unwrap();
    let n = c.get();
    assert_eq!(rows, ordinary(&b.module));
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    drop(s);
    let last = o.events.last().unwrap();
    assert_eq!(
        (last.phase, last.work, last.copy_bytes),
        (ExecutionPhase::Publication, 0, 0)
    );
    assert!(
        o.events[n..o.events.len() - 1]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn stopped_caller_retirement_keeps_original_cause_and_never_publishes_success() {
    let b = bundle(fixture());
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.formula_text_errors_observed(&mut s, site()).unwrap();
    let n = c.get();
    arm.set(true);
    assert!(retire_native_bundle_errors_observed(rows, &mut s, site()).is_err());
    arm.set(false);
    assert!(b.formula_text_errors_observed(&mut s, site()).is_err());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
    drop(s);
    assert!(
        o.events[n..]
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn whole_source_and_formula_payloads_are_unchanged_after_interior_refusal() {
    let b = bundle(fixture());
    let module = b.module.clone();
    let mut o = Observer {
        stop: Some(17),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(b.formula_text_errors_observed(&mut s, site()).is_err());
    assert_eq!(b.module, module);
}
#[test]
fn complete_labels_precede_error_header_admission_without_uncustodied_site() {
    let machine = "M λ\0";
    let label = "I 尾\0";
    let m = Module::new("");
    let limit = end(machine, label);
    let mut found = false;
    for cut in 1..=limit {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut st = State::default();
        let result = st.formula(source(machine, label), &bad(), &m, &mut w);
        if result.is_err() && st.machine == machine && st.label == label && st.pending.is_none() {
            assert!(st.errors.is_empty());
            found = true;
            assert!(st.finish(result, &mut w).is_err());
            assert!(empty(&st));
            break;
        }
        drain(&mut st, &mut w);
    }
    assert!(found);
}
