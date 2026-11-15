// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(
    clippy::unnecessary_lazy_evaluations,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn empty_context_preserves_no_diagnostics_but_observes_final_publication() {
    let mut i = fixture();
    i.context.atoms.clear();
    assert!(observed(&i).0.is_empty());
}
#[test]
fn all_unsupported_reasons_and_full_raw_details_preserve_physical_order() {
    let mut i = fixture();
    i.context.atoms.clear();
    i.context.unsupported_modes = [
        NativeUnsupportedModeReason::UnsupportedVerifierMode,
        NativeUnsupportedModeReason::UnsupportedFormulaSchema,
        NativeUnsupportedModeReason::UnsupportedCompilerFact,
        NativeUnsupportedModeReason::MissingSourceSpan,
        NativeUnsupportedModeReason::MissingReplayTranscript,
        NativeUnsupportedModeReason::Other,
    ]
    .into_iter()
    .enumerate()
    .map(|(at, r)| NativeUnsupportedMode::new(r, format!("{at}: raw λ\0{}", "尾".repeat(900))))
    .collect();
    let rows = observed(&i).0;
    assert_eq!(rows.len(), 6);
    for (row, u) in rows.iter().zip(&i.context.unsupported_modes) {
        assert!(
            matches!(row,E::UnsupportedNativeRequestMode{request:id,reason,detail}if *id==request()&&*reason==u.reason&&detail==&u.detail)
        );
    }
}
#[test]
fn every_physical_duplicate_atom_id_is_reported_even_with_different_roles() {
    let mut i = fixture();
    for kind in [
        NativeReplayAtomKind::Assertion,
        NativeReplayAtomKind::Assumption,
    ] {
        let mut a = atom();
        a.kind = kind;
        a.obligation = Some(ProofId::new(1));
        fixed_digest(&mut a);
        i.context.atoms.push(a);
    }
    let rows = observed(&i).0;
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::DuplicateReplayAtomId { .. }))
            .count(),
        2
    );
}
#[test]
fn exact_unicode_trim_rules_apply_independently_to_schema_and_payload() {
    for text in [
        "",
        " \t\r\n",
        "\u{85}\u{a0}\u{1680}\u{2000}\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}\u{3000}",
        " \u{2003}x",
        "\u{200b}",
    ] {
        let mut i = fixture();
        i.context.atoms[0].formula = ProofFormula::new(text, text);
        fixed_digest(&mut i.context.atoms[0]);
        let rows = observed(&i).0;
        let blank = rows
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    E::InvalidReplayAtom {
                        field: "formula.schema" | "formula.payload",
                        ..
                    }
                )
            })
            .count();
        assert_eq!(blank, if text.trim().is_empty() { 2 } else { 0 });
    }
}
#[test]
fn actual_smtlib_predicate_claim_and_opaque_two_text_rules_are_preserved() {
    for (schema, payload, rendering) in [
        ("smtlib2", "true", "true"),
        ("smtlib2", "true", "false"),
        ("trust_ir.pred.v1", "pred.0", "true"),
        ("opaque", "payload", "other"),
    ] {
        let mut i = fixture();
        let mut f = ProofFormula::new(schema, payload);
        f.smtlib = Some(rendering.into());
        i.context.atoms[0].formula = f;
        fixed_digest(&mut i.context.atoms[0]);
        observed(&i);
    }
    for schema in crate::proof::formula_schema::OwnedFormulaSchema::ALL {
        let mut i = fixture();
        let mut f = ProofFormula::new(schema.name(), "pred.0");
        f.smtlib = Some("true".into());
        i.context.atoms[0].formula = f;
        fixed_digest(&mut i.context.atoms[0]);
        observed(&i);
    }
    let mut i = fixture();
    let mut f = ProofFormula::new(crate::pred::PRED_FORMULA_SCHEMA, "pred.1");
    f.smtlib = Some("true".into());
    i.context.atoms[0].formula = f;
    fixed_digest(&mut i.context.atoms[0]);
    assert!(observed(&i).0.iter().any(|e| matches!(
        e,
        E::InvalidReplayAtom {
            field: "formula.smtlib",
            ..
        }
    )));
}
#[test]
fn zero_digest_wins_algorithm_then_nonzero_algorithm_then_actual_mismatch() {
    let mut i = fixture();
    i.context.atoms.clear();
    for (at, d) in [
        ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        },
        ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [1; 32],
        },
        ProofDigest::sha256([1; 32]),
    ]
    .into_iter()
    .enumerate()
    {
        let mut a = atom();
        a.id = NativeReplayAtomId::new(at as u32);
        a.payload_digest = d;
        i.context.atoms.push(a);
    }
    let rows = observed(&i).0;
    assert!(matches!(
        rows.as_slice(),
        [
            E::InvalidReplayAtom {
                field: "payload_digest",
                ..
            },
            E::InvalidReplayAtom {
                field: "payload_digest.algorithm",
                ..
            },
            E::ReplayAtomDigestMismatch { .. }
        ]
    ));
}
#[test]
fn payload_digest_is_actual_kind_plus_whole_formula_not_binding_metadata() {
    let mut i = fixture();
    let a = &mut i.context.atoms[0];
    a.obligation = Some(ProofId::new(1));
    a.assertion_id = Some(NativeAssertionId::new(7));
    a.span = Some(SourceSpan {
        file: 0,
        line: 1,
        col: 2,
    });
    assert!(observed(&i).0.is_empty());
    i.context.atoms[0].kind = NativeReplayAtomKind::Assertion;
    assert!(
        observed(&i)
            .0
            .iter()
            .any(|e| matches!(e, E::ReplayAtomDigestMismatch { .. }))
    );
    fixed_digest(&mut i.context.atoms[0]);
    assert!(observed(&i).0.is_empty());
}
#[test]
fn all_assertion_obligation_assertionid_and_span_presence_combinations_match_original() {
    for kind in [
        NativeReplayAtomKind::Assumption,
        NativeReplayAtomKind::Assertion,
    ] {
        for bits in 0..8 {
            let mut i = fixture();
            let a = &mut i.context.atoms[0];
            a.kind = kind;
            a.obligation = (bits & 1 != 0).then(|| ProofId::new(1));
            a.assertion_id = (bits & 2 != 0).then(|| NativeAssertionId::new(7));
            a.span = (bits & 4 != 0).then(|| SourceSpan {
                file: 0,
                line: 1,
                col: 2,
            });
            fixed_digest(a);
            observed(&i);
        }
    }
}
#[test]
fn requested_obligation_membership_is_set_semantics_even_with_duplicate_unsorted_ids() {
    let mut i = fixture();
    i.obligations = vec![ProofId::new(9), ProofId::new(1), ProofId::new(1)];
    i.context.atoms[0].obligation = Some(ProofId::new(1));
    assert!(observed(&i).0.is_empty());
    i.obligations.retain(|id| *id != ProofId::new(1));
    assert!(
        observed(&i)
            .0
            .iter()
            .any(|e| matches!(e, E::ReplayAtomObligationNotRequested { .. }))
    );
}
#[test]
fn absent_source_row_skips_only_source_specific_comparisons() {
    let mut i = fixture();
    i.context.atoms[0].obligation = Some(ProofId::new(2));
    i.context.atoms[0].assertion_id = Some(NativeAssertionId::new(99));
    i.context.atoms[0].span = Some(SourceSpan {
        file: 0,
        line: 99,
        col: 4,
    });
    let rows = observed(&i).0;
    assert!(matches!(
        rows.as_slice(),
        [E::ReplayAtomObligationNotRequested { .. }]
    ));
}
#[test]
fn first_physical_sidecar_row_wins_over_later_exact_or_wrong_duplicate() {
    let mut i = fixture();
    let a = &mut i.context.atoms[0];
    a.obligation = Some(ProofId::new(1));
    a.assertion_id = Some(NativeAssertionId::new(99));
    i.facts.obligation_sources.push(source(1));
    i.facts.obligation_sources[1].assertion_id = Some(NativeAssertionId::new(99));
    assert!(observed(&i).0.iter().any(|e|matches!(e,E::ReplayAtomAssertionMismatch{expected:Some(id),..}if *id==NativeAssertionId::new(7))));
    i.facts.obligation_sources.swap(0, 1);
    assert!(observed(&i).0.is_empty());
}
#[test]
fn expected_none_assertion_id_is_a_mismatch_when_actual_is_some() {
    let mut i = fixture();
    let a = &mut i.context.atoms[0];
    a.obligation = Some(ProofId::new(1));
    a.assertion_id = Some(NativeAssertionId::new(7));
    i.facts.obligation_sources[0].assertion_id = None;
    assert!(matches!(
        observed(&i).0.as_slice(),
        [E::ReplayAtomAssertionMismatch { expected: None, .. }]
    ));
}
#[test]
fn spans_compare_only_when_both_some_and_follow_assertion_mismatch() {
    for expected in [
        None,
        Some(SourceSpan {
            file: 0,
            line: 1,
            col: 2,
        }),
    ] {
        for actual in [
            None,
            Some(SourceSpan {
                file: 1,
                line: 9,
                col: 7,
            }),
        ] {
            let mut i = fixture();
            let a = &mut i.context.atoms[0];
            a.obligation = Some(ProofId::new(1));
            a.assertion_id = Some(NativeAssertionId::new(99));
            a.span = actual;
            i.facts.obligation_sources[0].span = expected;
            let rows = observed(&i).0;
            assert!(matches!(rows[0], E::ReplayAtomAssertionMismatch { .. }));
            assert_eq!(
                rows.len(),
                if expected.is_some() && actual.is_some() {
                    2
                } else {
                    1
                }
            );
        }
    }
}
#[test]
fn unrequested_obligation_does_not_suppress_real_source_mismatches() {
    let rows = observed(&bad()).0;
    let relevant: Vec<_> = rows
        .iter()
        .filter(|e| {
            matches!(
                e,
                E::ReplayAtomObligationNotRequested { .. }
                    | E::ReplayAtomAssertionMismatch { .. }
                    | E::ReplayAtomSourceSpanMismatch { .. }
            )
        })
        .collect();
    assert!(matches!(
        relevant.as_slice(),
        [
            E::ReplayAtomObligationNotRequested { .. },
            E::ReplayAtomAssertionMismatch { .. },
            E::ReplayAtomSourceSpanMismatch { .. }
        ]
    ));
}
#[test]
fn metadata_success_never_replaces_obligation_or_whole_bundle_validation() {
    let mut i = fixture();
    i.facts.obligation_sources.clear();
    assert!(i.module.proof_obligations.is_empty());
    assert!(observed(&i).0.is_empty());
}
#[test]
fn full_owned_unsupported_details_outlive_original_context() {
    let mut i = fixture();
    i.context.unsupported_modes.push(NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::Other,
        "raw λ\0尾".repeat(1000),
    ));
    let expected = i.ordinary();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = i.observed(&mut s).unwrap();
    drop(i);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
