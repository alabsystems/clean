// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_nonce_short_circuit_and_false_publication_callback_can_refuse() {
    let (a, b) = minted();
    let b = b.clone();
    let (_, base, end) = observed(&a, &b);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            a.authorizes_bundle_kernel_less_observed(&b, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn actual_digest_validation_retirement_and_each_publication_are_refusable() {
    let (a, b) = tampered();
    let (_, base, end) = observed(&a, &b);
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
            a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
                .is_err()
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn one_cumulative_work_and_copy_budget_spans_digest_whole_validation_and_second_query() {
    let (a, b) = minted();
    let (_, base, _) = observed(&a, &b);
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
            a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
                .unwrap()
        );
        assert!(
            a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
                .is_err()
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_is_sticky_and_never_turns_into_a_false_or_true_answer() {
    let (a, b) = minted();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
            .is_err()
    );
    arm.set(false);
    assert!(
        a.authorizes_bundle_kernel_less_observed(&b, &mut s, site())
            .is_err()
    );
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn both_true_and_false_answers_require_the_final_owning_publication() {
    let (a, b) = minted();
    for source in [&b, &b.clone()] {
        let (_, base, end) = observed(&a, source);
        let mut o = Observer {
            stop: Some(end),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            a.authorizes_bundle_kernel_less_observed(source, &mut s, site())
                .is_err()
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
        assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    }
}
