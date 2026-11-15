// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn all_provenance_digest_tool_language_and_import_diagnostics_match_original_order() {
    let bundle = fixture();
    let actual = observed(&bundle, Case::Provenance);
    assert_eq!(actual, ordinary(&bundle, Case::Provenance));
    assert_eq!(actual.len(), 14);
    assert_eq!(
        actual[0],
        E::EmptyProvenanceField("provenance.producer_version")
    );
    assert!(matches!(
        actual[1],
        E::EmptyDigest {
            field: "provenance.source_digest"
        }
    ));
    assert!(matches!(
        actual[2],
        E::NonCryptographicDigest {
            field: "provenance.source_digest"
        }
    ));
    assert!(matches!(
        actual[3],
        E::InputDigestMismatch {
            field: "provenance.source_digest",
            ..
        }
    ));
    assert!(matches!(
        actual[9],
        E::BundlePrimaryLanguageUncovered { .. }
    ));
    assert!(matches!(
        &actual[10],
        E::BundleLanguageUncovered {
            producer: Some(Producer::TRust),
            ..
        }
    ));
    assert!(
        matches!(&actual[11], E::BundleLanguageUncovered { producer: Some(Producer::Other(_)), functions, .. }
                    if functions == &[FuncId::new(13), FuncId::new(5)])
    );
    assert!(
        matches!(&actual[12], E::BundleImportLanguageUncovered { import, .. } if *import == ImportId::new(1))
    );
    assert!(
        matches!(&actual[13], E::BundleImportLanguageUncovered { import, .. } if *import == ImportId::new(2))
    );
}

#[test]
fn input_identity_guards_preserve_none_zero_legacy_match_and_mismatch_cases() {
    for input in [
        NativeAdapterInput::TrustIrModule,
        NativeAdapterInput::RustMir {
            body_digest: ProofDigest::sha256([7; 32]),
        },
    ] {
        for source in [
            None,
            Some(ProofDigest::zero()),
            Some(ProofDigest::sha256([7; 32])),
            Some(ProofDigest::sha256([8; 32])),
            Some(ProofDigest {
                algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                bytes: [0; 32],
            }),
        ] {
            let mut bundle = fixture();
            bundle.input = input;
            bundle.provenance.source_digest = source;
            assert_eq!(
                observed(&bundle, Case::Provenance),
                ordinary(&bundle, Case::Provenance)
            );
        }
    }
}

#[test]
fn unicode_tool_whitespace_matches_trim_and_optional_fields_are_not_defaulted() {
    for text in ["", " \t\n", "\u{2003}\u{202f}", "\u{200b}", " λ ", "\0"] {
        for optional in [None, Some(text.to_owned())] {
            let mut bundle = fixture();
            bundle.provenance.toolchain = vec![NativeToolIdentity {
                name: text.into(),
                version: optional.clone(),
                revision: optional,
                digest: None,
            }];
            assert_eq!(
                observed(&bundle, Case::Provenance),
                ordinary(&bundle, Case::Provenance)
            );
        }
    }
}

#[test]
fn long_actual_unicode_whitespace_scans_and_nonempty_version_keep_original_behavior() {
    let mut bundle = fixture();
    bundle.provenance.producer_version = " \u{2003}".into();
    bundle.provenance.source_artifact = Some(String::new());
    bundle.provenance.toolchain = vec![NativeToolIdentity {
        name: "\u{2003}".repeat(3000),
        version: Some("\u{202f}".repeat(3000)),
        revision: Some("\t".repeat(3000)),
        digest: None,
    }];
    let actual = observed(&bundle, Case::Provenance);
    assert_eq!(actual, ordinary(&bundle, Case::Provenance));
    assert!(!actual.contains(&E::EmptyProvenanceField("provenance.producer_version")));
}

#[test]
fn all_language_clones_preserve_exact_original_fixed_enum_membership() {
    for languages in [
        vec![],
        vec![NativeSourceLanguage::Unknown],
        vec![NativeSourceLanguage::Rust],
        vec![NativeSourceLanguage::Lean],
        vec![NativeSourceLanguage::Clean],
        vec![NativeSourceLanguage::Other, NativeSourceLanguage::Rust],
        vec![
            NativeSourceLanguage::Unknown,
            NativeSourceLanguage::Rust,
            NativeSourceLanguage::Swift,
            NativeSourceLanguage::C,
            NativeSourceLanguage::TrustIr,
            NativeSourceLanguage::Other,
            NativeSourceLanguage::Lean,
            NativeSourceLanguage::Clean,
        ],
    ] {
        let mut bundle = fixture();
        bundle.provenance.source_languages = languages.into_iter().collect();
        assert_eq!(
            observed(&bundle, Case::Provenance),
            ordinary(&bundle, Case::Provenance)
        );
    }
}

#[test]
fn serialization_policy_matrix_matches_all_ordinary_guard_combinations() {
    for bits in 0..16 {
        for unknown in [
            NativeUnknownFieldPolicy::Reject,
            NativeUnknownFieldPolicy::Preserve,
            NativeUnknownFieldPolicy::Ignore,
        ] {
            for schema in [NativeVerificationBundle::SCHEMA_VERSION, 0] {
                let mut bundle = fixture();
                bundle.serialization.schema_version = schema;
                bundle.serialization.canonical_order = bits & 1 != 0;
                bundle.serialization.sort_unordered_sets = bits & 2 != 0;
                bundle.serialization.messagepack_named_fields = bits & 4 != 0;
                bundle.serialization.unknown_fields = if bits & 8 != 0 {
                    unknown
                } else {
                    NativeUnknownFieldPolicy::Reject
                };
                assert_eq!(
                    observed(&bundle, Case::Serialization),
                    ordinary(&bundle, Case::Serialization)
                );
            }
        }
    }
}

#[test]
fn diagnostics_policy_matrix_keeps_emit_counterexample_and_zero_limit_guard() {
    for bits in 0..8 {
        for maximum in [0, 1] {
            let mut bundle = fixture();
            bundle.diagnostics.include_source_spans = bits & 1 != 0;
            bundle.diagnostics.include_lineage = bits & 2 != 0;
            bundle.diagnostics.emit_counterexamples = bits & 4 != 0;
            bundle.diagnostics.max_counterexamples = maximum;
            bundle.diagnostics.level = NativeDiagnosticLevel::Off;
            bundle.diagnostics.emit_unsat_cores = false;
            bundle.diagnostics.emit_proof_traces = true;
            assert_eq!(
                observed(&bundle, Case::Diagnostics),
                ordinary(&bundle, Case::Diagnostics)
            );
        }
    }
}

#[test]
fn empty_component_diagnostics_do_not_establish_whole_bundle_validity() {
    let mut bundle = crate::request::tests::native_bundle();
    bundle.schema_version = 0;
    bundle.requests.clear();
    for case in [Case::Provenance, Case::Serialization, Case::Diagnostics] {
        assert!(observed(&bundle, case).is_empty());
    }
    assert!(bundle.validate().is_err());
}
