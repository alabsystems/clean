// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn nonempty_term_contents_are_not_claimed_checked_by_identity_floor() {
    let (m, row, mut c) = fixture();
    for raw in [vec![0], vec![255, 255, 255], vec![1, 2, 3, 4]] {
        if let ProofEvidence::CleanCic { term, .. } = &mut c.evidence {
            *term = raw;
        }
        assert!(observed(&m, &row, &c).0);
        let k = CountingRejector(Cell::new(0));
        let a = CleanCicModuleProofAuthority { clean_cic: &k };
        assert!(!ModuleProofAuthority::replays_authority(&a, &m, &row, &c));
        assert_eq!(k.0.get(), 1);
    }
}
#[test]
fn borrowed_source_module_obligation_and_certificate_stay_exact_after_real_child_stop() {
    let (m, row, c) = fixture();
    let before = (m.clone(), row.clone(), c.clone());
    let (_, _, end) = observed(&m, &row, &c);
    let mut o = Observer {
        stop: Some(end / 2),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
            .is_err()
    );
    assert_eq!((&m, &row, &c), (&before.0, &before.1, &before.2));
}
#[test]
fn true_identity_floor_still_requires_its_final_publication() {
    let (m, row, c) = fixture();
    let (_, base, end) = observed(&m, &row, &c);
    let mut o = Observer {
        stop: Some(end),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(base.events[end - 1].phase, ExecutionPhase::Publication);
}
#[test]
fn healthy_zero_fuel_runs_the_real_identity_child_and_keeps_the_same_source_site() {
    let (m, row, c) = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert!(
        c.clean_cic_module_identity_floor_observed(&m, &row, &mut s, site())
            .unwrap()
    );
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
}
