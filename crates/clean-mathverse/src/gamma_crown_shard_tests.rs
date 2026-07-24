// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`crate::gamma_crown_shard`].
//!
//! Split out of the production file (#3379) to keep the shard builder
//! under the 500-line cap; re-attached as a `#[cfg(test)]` submodule of
//! `gamma_crown_shard` via `#[path]`.

use crate::gamma_crown_shard::{
    build_gamma_crown_shard_library, GammaCrownExportStats, GammaCrownShardBuilder,
    GammaCrownShardEntry, GAMMA_CROWN_NAMESPACE_PREFIXES,
};
use crate::trust::gamma_crown::{format_trust_report, ProofQuality, TrustClassification};
use crate::types::{AxiomProfile, ContentDomain, SourceSystem, TrustLevel};

fn make_constructive(name: &str) -> GammaCrownShardEntry {
    GammaCrownShardEntry {
        name: name.to_string(),
        proof_quality: ProofQuality::Constructive,
        has_sorry: false,
    }
}

fn make_axiom_dependent(name: &str, axioms: Vec<String>) -> GammaCrownShardEntry {
    GammaCrownShardEntry {
        name: name.to_string(),
        proof_quality: ProofQuality::AxiomDependent {
            axiom_count: axioms.len(),
            axioms,
        },
        has_sorry: false,
    }
}

fn make_axiom(name: &str) -> GammaCrownShardEntry {
    GammaCrownShardEntry {
        name: name.to_string(),
        proof_quality: ProofQuality::NotATheorem,
        has_sorry: false,
    }
}

fn make_sorry(name: &str) -> GammaCrownShardEntry {
    GammaCrownShardEntry {
        name: name.to_string(),
        proof_quality: ProofQuality::Constructive,
        has_sorry: true,
    }
}

#[test]
fn test_shard_builder_add_constructive() {
    let mut builder = GammaCrownShardBuilder::new();
    let idx = builder.add_entry(make_constructive("NNVerify.C002.zonotope_soundness"));
    assert_eq!(idx, 0);
    assert_eq!(builder.entry_count(), 1);

    let summaries = builder.trust_summaries();
    assert_eq!(
        summaries[0].classification,
        TrustClassification::Constructive
    );
    assert_eq!(summaries[0].axiom_profile, AxiomProfile::NONE);
}

#[test]
fn test_shard_builder_add_axiom_dependent() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_axiom_dependent(
        "NNVerify.C004.crown_backward_sound",
        vec!["crown_backward_eq_interval_hull_core".to_string()],
    ));

    let summaries = builder.trust_summaries();
    assert_eq!(summaries[0].classification, TrustClassification::Trusted);
    assert!(summaries[0].axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
    assert_eq!(summaries[0].domain_axiom_count, 1);
}

#[test]
fn test_shard_builder_add_axiom() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_axiom("NNVerify.C007.merge_sound_helper"));

    let summaries = builder.trust_summaries();
    assert_eq!(summaries[0].classification, TrustClassification::Axiom);
    assert!(summaries[0].axiom_profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_shard_builder_add_sorry() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_sorry("NNVerify.C003.wip_lemma"));

    let summaries = builder.trust_summaries();
    assert_eq!(summaries[0].classification, TrustClassification::Pending);
    assert!(summaries[0].has_sorry);
}

#[test]
fn test_shard_builder_trust_report() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_constructive("NNVerify.C002.theorem_a"));
    builder.add_entry(make_constructive("NNVerify.C002.theorem_b"));
    builder.add_entry(make_axiom_dependent(
        "NNVerify.C004.theorem_c",
        vec!["ax1".to_string()],
    ));
    builder.add_entry(make_axiom("NNVerify.C004.axiom_d"));

    let report = builder.trust_report();
    assert_eq!(report.total_constructive, 2);
    assert_eq!(report.total_trusted, 1);
    assert_eq!(report.total_axioms, 1);

    // C002 should be fully constructive
    let c002 = &report.conjecture_summaries["C002"];
    assert!(c002.is_fully_constructive);

    // C004 should not be (has trusted + axiom)
    let c004 = &report.conjecture_summaries["C004"];
    assert!(!c004.is_fully_constructive);
}

#[test]
fn test_shard_builder_format_report_not_empty() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_constructive("NNVerify.C006.blockwise_soundness"));
    let md = builder.format_report();
    assert!(md.contains("# Gamma-Crown Trust Report"));
    assert!(md.contains("C006"));
}

#[test]
fn test_shard_builder_write_bytes() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_constructive("NNVerify.C001.compress_soundness"));
    builder.add_entry(make_axiom("NNVerify.C001.compress_tightness_helper"));

    let bytes = builder.write_to_bytes().expect("write should succeed");
    // Shard should start with OMEG magic
    assert!(bytes.len() > 256);
    assert_eq!(&bytes[0..4], &[0x47, 0x45, 0x4D, 0x4F]); // "OMEG" little-endian
}

#[test]
fn test_export_stats_from_report() {
    let mut builder = GammaCrownShardBuilder::new();
    builder.add_entry(make_constructive("NNVerify.C002.a"));
    builder.add_entry(make_constructive("NNVerify.C006.b"));
    builder.add_entry(make_axiom_dependent(
        "NNVerify.C004.c",
        vec!["ax".to_string()],
    ));

    let report = builder.trust_report();
    let stats = GammaCrownExportStats::from(&report);

    assert_eq!(stats.total_entries, 3);
    assert_eq!(stats.constructive_count, 2);
    assert_eq!(stats.trusted_count, 1);
    assert!(*stats.conjecture_status.get("C002").unwrap_or(&false));
    assert!(*stats.conjecture_status.get("C006").unwrap_or(&false));
    assert!(!(*stats.conjecture_status.get("C004").unwrap_or(&false)));
}

#[test]
fn test_empty_builder() {
    let builder = GammaCrownShardBuilder::new();
    assert_eq!(builder.entry_count(), 0);
    let report = builder.trust_report();
    assert_eq!(report.total_constructive, 0);
    assert!(report.all_declarations.is_empty());
}

// ---------------------------------------------------------------------------
// End-to-end kernel bridge tests (issue #3379)
//
// These tests exercise the full pipeline:
//   1. Populate a real kernel `Environment` with gamma-crown declarations
//   2. Run trust audit via the kernel `proof_quality` API
//   3. Export declarations to an Mathverse shard with correct trust metadata
//   4. Round-trip the shard via ShardReader and verify headers are intact
// ---------------------------------------------------------------------------

/// Returns true iff every axiom in `domain_axioms` is a shared-infrastructure
/// axiom (e.g. algebra layer, LP dual, Rat oracle) rather than a
/// conjecture-specific domain axiom under `conjecture_prefix`.
///
/// This matches the axiom-counting methodology in
/// `data/axiom_audit.json` and `gamma_crown_verify::verify_conjecture`:
/// shared-infrastructure axioms are *not* counted as trust gaps for a
/// specific conjecture because they are common to all formalization work.
fn all_axioms_are_shared_infra(domain_axioms: &[String], conjecture_prefix: &str) -> bool {
    domain_axioms
        .iter()
        .all(|axiom| !axiom.starts_with(conjecture_prefix))
}

#[test]
fn test_add_environment_c002_constructive_roundtrip() {
    use crate::shard::ShardReader;
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C002").expect("C002 init should succeed");

    let mut builder = GammaCrownShardBuilder::new();
    let added = builder.add_environment(&env, &["NNVerify.C002."]);
    assert!(
        added > 0,
        "should harvest at least one NNVerify.C002 declaration"
    );

    let report = builder.trust_report();

    // C002 is certified fully constructive per data/axiom_audit.json: zero
    // conjecture-specific (namespace-matching) domain axioms. Trusted
    // entries may appear because the kernel audit walks ALL transitive
    // deps including shared infrastructure (algebra layer, etc.), but
    // none of those should be under `NNVerify.C002.*`.
    assert_eq!(
        report.total_pending, 0,
        "C002 should have no pending/unchecked declarations, got {}",
        report.total_pending
    );
    for summary in &report.all_declarations {
        if summary.classification == TrustClassification::Trusted {
            assert!(
                all_axioms_are_shared_infra(&summary.domain_axioms, "NNVerify.C002."),
                "declaration {} has conjecture-specific axiom dep, axioms={:?}",
                summary.name,
                summary.domain_axioms
            );
        }
    }

    // Exercise shard round-trip: write, re-read, verify constant count.
    let bytes = builder.write_to_bytes().expect("shard serialization");
    let reader = ShardReader::from_bytes(&bytes).expect("shard round-trip");
    assert_eq!(
        reader.constants.len(),
        added,
        "round-tripped shard must preserve every constant header"
    );
    // Every constant must carry the gamma-crown SourceSystem marker.
    for header in &reader.constants {
        assert_eq!(
            header.source_system,
            SourceSystem::GammaCrown as u8,
            "constant should carry GammaCrown source system"
        );
        assert_eq!(
            header.content_domain,
            ContentDomain::NnVerification as u8,
            "constant should carry NnVerification content domain"
        );
    }
}

#[test]
fn test_add_environment_c001_trust_classification() {
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C001").expect("C001 init should succeed");

    let mut builder = GammaCrownShardBuilder::new();
    let added = builder.add_environment(&env, &["NNVerify.C001."]);
    assert!(added > 0, "should harvest C001 declarations");

    let report = builder.trust_report();
    // No Pending (unchecked/sorry) declarations allowed.
    assert_eq!(
        report.total_pending, 0,
        "C001 should have no Pending (unchecked/sorry) theorems"
    );

    // Every Trusted theorem must depend ONLY on shared-infrastructure axioms
    // (nothing under NNVerify.C001.*), matching the zero-domain-axiom
    // guarantee in data/axiom_audit.json.
    for summary in &report.all_declarations {
        if summary.classification == TrustClassification::Trusted {
            assert!(
                all_axioms_are_shared_infra(&summary.domain_axioms, "NNVerify.C001."),
                "C001 declaration {} has a conjecture-specific axiom dep, axioms={:?}",
                summary.name,
                summary.domain_axioms
            );
        }
    }

    // Human-readable report should contain the C001 section.
    let md = format_trust_report(&report);
    assert!(
        md.contains("### C001"),
        "report should contain C001 section"
    );
    assert!(
        md.contains("# Gamma-Crown Trust Report"),
        "report should have top-level title"
    );
}

#[test]
fn test_add_environment_trust_levels_match_classification() {
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C002").expect("C002 init");

    let mut builder = GammaCrownShardBuilder::new();
    builder.add_environment(&env, &["NNVerify."]);

    // Every Constructive declaration must map to KernelVerified.
    // Every Axiom declaration must map to PartiallyAxiomatized.
    for summary in builder.trust_summaries() {
        match summary.classification {
            TrustClassification::Constructive => {
                assert_eq!(
                    summary.trust_level,
                    TrustLevel::KernelVerified,
                    "Constructive {} should map to KernelVerified",
                    summary.name
                );
            }
            TrustClassification::Axiom => {
                assert_eq!(
                    summary.trust_level,
                    TrustLevel::PartiallyAxiomatized,
                    "Axiom {} should map to PartiallyAxiomatized",
                    summary.name
                );
            }
            TrustClassification::Trusted => {
                assert_eq!(
                    summary.trust_level,
                    TrustLevel::AxiomDependent,
                    "Trusted {} should map to AxiomDependent",
                    summary.name
                );
            }
            TrustClassification::Pending => {
                assert_eq!(
                    summary.trust_level,
                    TrustLevel::TrustedOracle,
                    "Pending {} should map to TrustedOracle",
                    summary.name
                );
            }
        }
    }
}

#[test]
fn test_add_environment_empty_prefix_adds_nothing() {
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C001").expect("C001 init");

    let mut builder = GammaCrownShardBuilder::new();
    let added = builder.add_environment(&env, &["ThisPrefixDoesNotMatch."]);
    assert_eq!(added, 0, "non-matching prefix should add zero declarations");
    assert_eq!(builder.entry_count(), 0);
}

#[test]
fn test_proof_quality_from_kernel_constructive() {
    // Unit test on the From<clean_kernel::env::ProofQuality> impl.
    let kernel_pq = clean_kernel::env::ProofQuality::Constructive;
    let mathverse_pq: ProofQuality = kernel_pq.into();
    assert_eq!(mathverse_pq, ProofQuality::Constructive);
}

#[test]
fn test_proof_quality_from_kernel_axiom_dependent() {
    use clean_kernel::name::Name;
    let kernel_pq = clean_kernel::env::ProofQuality::AxiomDependent {
        axiom_count: 2,
        axioms: vec![
            Name::from_string("NNVerify.C009.hard_axiom_a"),
            Name::from_string("NNVerify.C009.hard_axiom_b"),
        ],
    };
    let mathverse_pq: ProofQuality = kernel_pq.into();
    match mathverse_pq {
        ProofQuality::AxiomDependent {
            axiom_count,
            axioms,
        } => {
            assert_eq!(axiom_count, 2);
            assert!(axioms.contains(&"NNVerify.C009.hard_axiom_a".to_owned()));
            assert!(axioms.contains(&"NNVerify.C009.hard_axiom_b".to_owned()));
        }
        other => panic!("expected AxiomDependent, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// build_gamma_crown_shard_library — thin-wrapper smoke tests (#3473)
// ---------------------------------------------------------------------------

/// The wrapper must override the `SourceSystem` tag on every shard header,
/// write to `gamma-crown.mathverse` (not `clean-native.mathverse`), and honour the
/// default namespace filter.
#[test]
fn test_build_gamma_crown_shard_library_tags_and_filename() {
    use crate::shard::ShardReader;
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C002").expect("C002 init");
    let tmp = tempfile::tempdir().expect("tempdir");
    let result =
        build_gamma_crown_shard_library(&env, tmp.path()).expect("gamma-crown shard build");

    // Output filename differs from the default native pipeline.
    assert!(
        result.shard_path.ends_with("gamma-crown.mathverse"),
        "shard should be named gamma-crown.mathverse, got {}",
        result.shard_path.display()
    );
    assert!(result.shard_path.exists(), "shard file should be written");
    assert!(result.sidecar_path.exists(), "sidecar should be written");

    // Every accepted header must carry the GammaCrown source-system tag.
    let reader = ShardReader::from_file(&result.shard_path).expect("read shard");
    for header in &reader.constants {
        assert_eq!(
            header.source_system,
            SourceSystem::GammaCrown as u8,
            "every wrapper-exported constant must carry SourceSystem::GammaCrown"
        );
        assert_eq!(
            header.content_domain,
            ContentDomain::NnVerification as u8,
            "every NNVerify.* declaration must carry NnVerification content domain"
        );
    }
}

/// The namespace filter must actually exclude out-of-scope declarations:
/// every decision-log entry must match one of the default prefixes.
#[test]
fn test_build_gamma_crown_shard_library_namespace_filter() {
    use clean_kernel::env::gamma_crown_verify::init_conjecture;

    let env = init_conjecture("C001").expect("C001 init");
    let tmp = tempfile::tempdir().expect("tempdir");
    let result = build_gamma_crown_shard_library(&env, tmp.path()).expect("build");

    for decision in &result.decisions {
        let matches = GAMMA_CROWN_NAMESPACE_PREFIXES
            .iter()
            .any(|p| decision.name.starts_with(p));
        assert!(
            matches,
            "decision log entry {} falls outside GAMMA_CROWN_NAMESPACE_PREFIXES",
            decision.name
        );
    }
    assert!(
        result.total_declarations > 0,
        "at least one NNVerify.* constant should be scanned for C001"
    );
}

/// `GAMMA_CROWN_NAMESPACE_PREFIXES` must stay a superset of the historical
/// prefixes used by `GammaCrownShardBuilder::add_environment` callers so
/// that wrapper + legacy paths scan the same corpus.
#[test]
fn test_gamma_crown_namespace_prefixes_includes_nnverify() {
    assert!(GAMMA_CROWN_NAMESPACE_PREFIXES.contains(&"NNVerify."));
    assert!(GAMMA_CROWN_NAMESPACE_PREFIXES.contains(&"GammaCrown."));
    assert!(GAMMA_CROWN_NAMESPACE_PREFIXES.contains(&"nn_verify."));
}
