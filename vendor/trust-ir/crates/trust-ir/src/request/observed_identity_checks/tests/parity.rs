// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_complete_original_helper_matches_actual_oracle() {
    let f = fixture();
    for suite in suites() {
        for c in cases() {
            observed(&f, c, suite);
        }
    }
}
#[test]
fn all_alias_families_and_suffixes_are_checked_against_each_real_suite() {
    for name in [
        "TRUST_VC.Native",
        "trustmc",
        "trust-wp-x",
        "trust-ir",
        "ay-v1",
        "Trust.Native",
        "wrong",
        "trustmc2",
    ] {
        let f = named(name);
        for suite in suites() {
            for c in [Case::Verifier, Case::Replay, Case::Certificate] {
                observed(&f, c, suite);
            }
        }
    }
}
#[test]
fn empty_canonical_verifier_and_certificate_keep_their_original_different_rules() {
    for raw in ["", "---", "🦀", " \u{3000}"] {
        let f = named(raw);
        assert!(observed(&f, Case::Verifier, Suite::TrustMc).0.is_empty());
        assert_eq!(observed(&f, Case::Certificate, Suite::TrustMc).0.len(), 1);
    }
}
#[test]
fn punctuation_only_replay_engine_keeps_existing_nonblank_empty_canonical_exception() {
    let f = named("---");
    assert!(observed(&f, Case::Replay, Suite::TrustMc).0.is_empty());
}
#[test]
fn tool_empty_name_version_revision_zero_digest_and_algorithm_keep_exact_order() {
    let f = fixture();
    let (rows, _, _) = observed(&f, Case::Tool, Suite::TrustMc);
    assert_eq!(
        rows,
        vec![
            E::EmptyProvenanceField("evidence.verifier"),
            E::InvalidToolIdentityField {
                field: "evidence.verifier",
                component: "version"
            },
            E::InvalidToolIdentityField {
                field: "evidence.verifier",
                component: "revision"
            },
            E::EmptyDigest {
                field: "evidence.verifier"
            },
            E::InvalidToolIdentityField {
                field: "evidence.verifier",
                component: "digest.algorithm"
            }
        ]
    );
}
#[test]
fn absent_tool_fields_skip_while_present_blank_fields_refuse() {
    let mut f = named("tool");
    assert!(observed(&f, Case::Tool, Suite::Unknown).0.is_empty());
    f.tool.version = Some(" ".into());
    f.tool.revision = Some("\u{2003}".into());
    assert_eq!(observed(&f, Case::Tool, Suite::Unknown).0.len(), 2);
}
#[test]
fn replay_engine_suite_invocation_and_transcript_checks_keep_exact_order() {
    let f = fixture();
    let (rows, _, _) = observed(&f, Case::Replay, Suite::TrustMc);
    assert!(matches!(
        &rows[0],
        E::ReplayIdentityVerifierSuiteMismatch { .. }
    ));
    assert!(matches!(
        &rows[1],
        E::InvalidReplayIdentity {
            field: "invocation",
            ..
        }
    ));
    assert!(matches!(
        &rows[2],
        E::InvalidReplayIdentity {
            field: "transcript_digest",
            ..
        }
    ));
}
#[test]
fn replay_transcript_zero_precedes_algorithm_and_none_is_distinct() {
    let mut f = named("trustmc");
    for digest in [
        None,
        Some(ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        }),
        Some(ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [1; 32],
        }),
        Some(ProofDigest::sha256([1; 32])),
    ] {
        f.replay.transcript_digest = digest;
        observed(&f, Case::Replay, Suite::TrustMc);
    }
}
#[test]
fn unknown_family_certificate_skip_does_not_read_or_normalize_its_prover() {
    let short = named("x");
    let long = named(&"λ🦀".repeat(3000));
    for suite in [Suite::Unknown, Suite::Other] {
        let (a, oa, ea) = observed(&short, Case::Certificate, suite);
        let (b, ob, eb) = observed(&long, Case::Certificate, suite);
        assert!(a.is_empty() && b.is_empty());
        assert_eq!(&oa.events[..ea], &ob.events[..eb]);
    }
}
#[test]
fn full_raw_and_canonical_labels_outlive_all_original_metadata_inputs() {
    for c in [Case::Verifier, Case::Replay, Case::Certificate] {
        let f = named(&("WRONG.Native'\0λ🦀".repeat(500)));
        let expected = ordinary(&f, c, Suite::TrustMc);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = run(check(&f, c, Suite::TrustMc), &mut s, site()).unwrap();
        drop(f);
        assert_eq!(rows, expected);
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
}
#[test]
fn arbitrary_static_diagnostic_label_is_preserved_without_becoming_authority() {
    let f = fixture();
    for field in [
        "provenance.toolchain",
        "evidence.verifier",
        "evidence.solvers",
        "request.expected_verifier",
    ] {
        let mut expected = Vec::new();
        crate::request::validate_tool_identity(field, &f.tool, &mut expected);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let rows = f
            .tool
            .validation_errors_observed(field, &mut s, site())
            .unwrap();
        assert_eq!(rows, expected);
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
}
#[test]
fn inherent_methods_cover_all_four_real_data_routes() {
    let f = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for rows in [
        f.tool
            .validation_errors_observed("evidence.verifier", &mut s, site())
            .unwrap(),
        f.tool
            .verifier_suite_errors_observed(request(), Suite::TrustMc, &mut s, site())
            .unwrap(),
        f.replay
            .validation_errors_observed(request(), Suite::TrustMc, &mut s, site())
            .unwrap(),
        f.cert
            .verifier_suite_errors_observed(request(), Suite::TrustMc, &mut s, site())
            .unwrap(),
    ] {
        retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
    }
}
