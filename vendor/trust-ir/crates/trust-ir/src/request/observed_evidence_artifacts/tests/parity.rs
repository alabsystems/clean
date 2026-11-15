// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_nine_modes_and_fourteen_artifact_kinds_match_the_whole_ordinary_leaf() {
    for mode in modes() {
        for kind in kinds() {
            observed(&evidence(mode, vec![artifact("full", kind)]));
        }
    }
}
#[test]
fn every_empty_artifact_list_has_one_full_missing_artifact_error() {
    for mode in modes() {
        let e = evidence(mode, vec![]);
        let (rows, _, _) = observed(&e);
        assert_eq!(
            rows,
            vec![E::MissingEvidenceArtifacts {
                request: e.request(),
                suite: e.verifier_suite()
            }]
        );
    }
}
#[test]
fn invalid_name_zero_digest_algorithm_duplicate_then_kind_keep_original_order() {
    let e = fixture();
    let (rows, _, _) = observed(&e);
    assert!(matches!(
        &rows[0],
        E::InvalidEvidenceArtifact { field: "name", .. }
    ));
    assert!(matches!(
        &rows[1],
        E::InvalidEvidenceArtifact {
            field: "digest",
            ..
        }
    ));
    assert!(matches!(
        &rows[2],
        E::InvalidEvidenceArtifact {
            field: "digest.algorithm",
            ..
        }
    ));
    assert!(matches!(&rows[3], E::EvidenceArtifactSuiteMismatch { .. }));
    let later: Vec<_> = rows
        .iter()
        .filter(|e| matches!(e, E::DuplicateEvidenceArtifact { .. }))
        .collect();
    assert_eq!(later.len(), 2);
}
#[test]
fn names_are_byte_exact_without_trim_case_or_unicode_normalization() {
    let e = evidence(
        Mode::Mc(Mc::Chc),
        ["a", " a ", "A", "é", "e\u{301}", "\0"]
            .into_iter()
            .map(|n| artifact(n, Kind::Other))
            .collect(),
    );
    assert!(observed(&e).0.is_empty());
}
#[test]
fn long_same_length_names_differing_only_at_last_byte_remain_distinct() {
    let a = "λ".repeat(3000) + "a";
    let b = "λ".repeat(3000) + "b";
    let e = evidence(
        Mode::Mc(Mc::Chc),
        vec![artifact(a, Kind::Other), artifact(b, Kind::Other)],
    );
    assert!(observed(&e).0.is_empty());
}
#[test]
fn every_physical_repeat_after_first_is_duplicate_even_with_different_kind_digest() {
    let e = evidence(
        Mode::Mc(Mc::Pdr),
        vec![
            artifact("same", Kind::Other),
            artifact("same", Kind::ReplayTranscript),
            artifact("same", Kind::NativeCompiledArtifact),
        ],
    );
    let (rows, _, _) = observed(&e);
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|e| matches!(e, E::DuplicateEvidenceArtifact { .. }))
    );
}
#[test]
fn discharge_does_not_relabel_imported_or_merged_certificates_as_acceptable_kinds() {
    let e = evidence(
        Mode::Vc(Vc::DischargeProofObligations),
        vec![
            artifact("import", Kind::TrustVcCertificateImport),
            artifact("merge", Kind::TrustVcMergedCertificate),
        ],
    );
    let (rows, _, _) = observed(&e);
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|e| matches!(e, E::EvidenceArtifactSuiteMismatch { .. }))
    );
}
#[test]
fn returned_whole_names_outlive_original_evidence_source() {
    let e = fixture();
    let expected = ordinary(&e);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = e.artifact_errors_observed(&mut s, site()).unwrap();
    drop(e);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn unicode_whitespace_matches_actual_trim_and_nonwhite_tail_is_not_empty() {
    for name in [
        "",
        " \t\r\n",
        "\u{85}\u{a0}\u{1680}\u{2000}\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}\u{3000}",
        " \u{2003}x",
        "\u{200b}",
    ] {
        let e = evidence(Mode::Wp(Wp::Abduction), vec![artifact(name, Kind::Other)]);
        let (rows, _, _) = observed(&e);
        assert_eq!(
            rows.iter()
                .any(|e| matches!(e, E::InvalidEvidenceArtifact { field: "name", .. })),
            name.trim().is_empty()
        );
    }
}
#[test]
fn successful_metadata_checks_do_not_authenticate_missing_replay_or_solver_inputs() {
    let e = evidence(
        Mode::Mc(Mc::Chc),
        vec![artifact("metadata only", Kind::Other)],
    );
    assert!(e.solvers().is_empty());
    assert!(e.replay().transcript_digest.is_none());
    assert!(observed(&e).0.is_empty());
}
