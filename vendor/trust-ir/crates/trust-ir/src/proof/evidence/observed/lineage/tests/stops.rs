// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_lineage_sort_lookup_hash_cleanup_and_final_publication_refuses() {
    let (m, row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let expected = row
        .clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site())
        .unwrap();
    let end = calls.get();
    assert_eq!(expected, original_v8(&row, &c, Some(&b)));
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "lineage stop");
        drop(s);
        assert_eq!(&o.events[..cut], &base.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn repeated_lineages_use_both_unchanged_original_cumulative_limits() {
    let (m, row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site())
        .unwrap();
    drop(s);
    for copy in [false, true] {
        let cap = base
            .events
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site())
            .unwrap();
        assert_eq!(
            row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn unknown_v8_symbol_does_not_convert_a_prior_or_new_admission_stop_to_none() {
    let (m, mut row, _) = fixture();
    row.function = Some(FuncId::new(999));
    let c = ModuleFunctionCatalog::new(&m);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    assert!(
        row.clean_cic_lineage_content_v8_observed(&c, &mut s, site())
            .unwrap()
            .is_none()
    );
    let end = calls.get();
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            row.clean_cic_lineage_content_v8_observed(&c, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn zero_instruction_fuel_and_sticky_original_first_cause_are_preserved() {
    let (m, row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    row.clean_cic_lineage_digest_v8_observed(&c, Some(&b), &mut s, site())
        .unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
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
        row.clean_cic_lineage_digest_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "lineage stop");
}

#[derive(Clone, Copy)]
enum Decision {
    Index,
    Binds,
    V8,
}
fn decision(
    row: &ProofObligation,
    e: &ProofEvidence,
    c: &ModuleFunctionCatalog<'_>,
    which: Decision,
    s: &mut ObservedSession<'_, Observer>,
) -> R {
    match which {
        Decision::Index => assert_eq!(
            row.clean_cic_lineage_digest_observed(s, site())?,
            super::super::super::super::clean_cic_lineage_digest(row)
        ),
        Decision::Binds => assert!(e.clean_cic_lineage_binds_observed(row, c, s, site())?),
        Decision::V8 => assert!(e.clean_cic_lineage_is_v8_observed(row, c, s, site())?),
    }
    Ok(())
}
#[test]
fn every_actual_index_and_full_v8_binding_decision_callback_refuses() {
    let (m, row, b) = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let e = ProofEvidence::CleanCic {
        term: vec![],
        context: vec![],
        lineage: original_v8(&row, &c, Some(&b)).unwrap(),
        kernel_recheck: Some(CleanCicKernelRecheck {
            module: "unknown".into(),
            theorems: vec![],
            anchor: "unknown".into(),
            allowed_axioms: vec![],
            binding: Some(Box::new(b)),
        }),
    };
    for which in [Decision::Index, Decision::Binds, Decision::V8] {
        let mut base = Observer::default();
        let calls = base.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
        decision(&row, &e, &c, which, &mut s).unwrap();
        let end = calls.get();
        drop(s);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                decision(&row, &e, &c, which, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "lineage stop");
            drop(s);
            assert_eq!(&o.events[..cut], &base.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
