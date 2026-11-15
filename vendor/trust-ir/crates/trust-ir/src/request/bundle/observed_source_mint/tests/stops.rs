// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_already_minted_guard_inner_error_and_publication_callback_can_refuse() {
    let mut b = good();
    let original = SourceGenerationAuthority::mint_from_live_lowering(&mut b).unwrap();
    let (_, base, end) = observed(&mut b);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
                &mut b,
                &mut s,
                site()
            )
            .is_err()
        );
        assert!(b.source_generation_live.matches(&original.nonce));
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn full_validation_digest_and_each_publication_refusal_leave_live_marker_uninstalled() {
    let mut base_b = good();
    let (_, base, end) = observed(&mut base_b);
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
        let mut b = good();
        let before = b.clone();
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(
            SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
                &mut b,
                &mut s,
                site()
            )
            .is_err()
        );
        assert!(b.source_generation_live.0.is_none());
        assert_eq!(b, before);
        assert_eq!(s.first_refusal().unwrap().progress, base.events[cut - 1]);
    }
}
#[test]
fn one_original_work_and_copy_budget_spans_issuance_retirement_and_another_issuance() {
    let mut first = good();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let a = SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
        &mut first,
        &mut s,
        site(),
    )
    .unwrap()
    .unwrap();
    a.retire_observed(&mut s, site()).unwrap();
    for copy in [false, true] {
        let mut b = good();
        let mut c = good();
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
        let a = SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
            &mut b,
            &mut s,
            site(),
        )
        .unwrap()
        .unwrap();
        a.retire_observed(&mut s, site()).unwrap();
        assert!(
            SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
                &mut c,
                &mut s,
                site()
            )
            .is_err()
        );
        assert!(c.source_generation_live.0.is_none());
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_interrupt_remains_sticky_and_never_installs_a_candidate_identity() {
    let mut b = good();
    let arm = Rc::new(Cell::new(true));
    let mut o = Observer {
        arm: Some(arm.clone()),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
            &mut b,
            &mut s,
            site()
        )
        .is_err()
    );
    arm.set(false);
    assert!(
        SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
            &mut b,
            &mut s,
            site()
        )
        .is_err()
    );
    assert!(b.source_generation_live.0.is_none());
    assert_eq!(s.first_refusal().unwrap().cause, "interrupt");
}
#[test]
fn final_success_publication_refusal_discards_both_candidates_before_return() {
    let mut sample = good();
    let (_, base, end) = observed(&mut sample);
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
    let mut b = good();
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(
            &mut b,
            &mut s,
            site()
        )
        .is_err()
    );
    assert!(b.source_generation_live.0.is_none());
    assert_eq!(s.first_refusal().unwrap().progress, base.events[end - 1]);
}
#[test]
fn stopped_authority_or_inner_error_retirement_consumes_without_resetting_marker() {
    for mut b in [good(), bad()] {
        let (result, _, _) = observed(&mut b);
        let had_marker = b.source_generation_live.0.is_some();
        let mut o = Observer {
            retirement_stop: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let stopped = match result {
            Ok(a) => a.retire_observed(&mut s, site()),
            Err(e) => e.retire_observed(&mut s, site()),
        };
        assert!(stopped.is_err());
        assert_eq!(b.source_generation_live.0.is_some(), had_marker);
        assert!(
            o.events
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
