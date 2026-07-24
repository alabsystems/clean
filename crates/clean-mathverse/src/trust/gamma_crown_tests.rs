// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [].
//!
//! Split out of the production file (#3379) to keep the trust accounting
//! module under the 500-line cap; re-attached as a  submodule
//! of  via .

use super::*;
use crate::types::{AxiomProfile, TrustLevel};

use super::*;

#[test]
fn test_classify_constructive_declaration() {
    let summary = classify_declaration(
        "NNVerify.C001.compress_soundness",
        &ProofQuality::Constructive,
        false,
    );

    assert_eq!(summary.name, "NNVerify.C001.compress_soundness");
    assert_eq!(summary.conjecture_id.as_deref(), Some("C001"));
    assert_eq!(summary.classification, TrustClassification::Constructive);
    assert_eq!(summary.domain_axiom_count, 0);
    assert!(summary.domain_axioms.is_empty());
    assert_eq!(summary.axiom_profile, AxiomProfile::NONE);
    assert_eq!(summary.trust_level, TrustLevel::KernelVerified);
    assert!(!summary.has_sorry);
}

#[test]
fn test_classify_trusted_declaration() {
    let summary = classify_declaration(
        "NNVerify.C011.softmax_width_monotone",
        &ProofQuality::AxiomDependent {
            axiom_count: 3,
            axioms: vec![
                "NNVerify.C011.lp_dual_sound".to_owned(),
                "NNVerify.C011.rat_exp".to_owned(),
                "NNVerify.C011.softmax_ibp_bridge".to_owned(),
            ],
        },
        false,
    );

    assert_eq!(summary.conjecture_id.as_deref(), Some("C011"));
    assert_eq!(summary.classification, TrustClassification::Trusted);
    assert_eq!(summary.domain_axiom_count, 3);
    assert_eq!(
        summary.domain_axioms,
        vec![
            "NNVerify.C011.lp_dual_sound".to_owned(),
            "NNVerify.C011.rat_exp".to_owned(),
            "NNVerify.C011.softmax_ibp_bridge".to_owned(),
        ]
    );
    assert_eq!(summary.trust_level, TrustLevel::AxiomDependent);
    assert!(summary.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
    assert!(summary.axiom_profile.has(AxiomProfile::REAL_AXIOMS));
    assert!(summary.axiom_profile.has(AxiomProfile::LRA_TRUSTED));
    assert!(summary.axiom_profile.has(AxiomProfile::BRIDGE_AXIOM));
    assert!(!summary.axiom_profile.has(AxiomProfile::AXIOMATIZED));
}

#[test]
fn test_classify_pending_declaration() {
    let unchecked = classify_declaration(
        "NNVerify.C002.layernorm_zonotope",
        &ProofQuality::Unchecked,
        false,
    );
    assert_eq!(unchecked.classification, TrustClassification::Pending);
    assert_eq!(unchecked.trust_level, TrustLevel::TrustedOracle);
    assert_eq!(unchecked.axiom_profile, AxiomProfile::AXIOMATIZED);
    assert!(!unchecked.has_sorry);

    let sorry = classify_declaration(
        "NNVerify.C002.correlation_firewall",
        &ProofQuality::Constructive,
        true,
    );
    assert_eq!(sorry.classification, TrustClassification::Pending);
    assert_eq!(sorry.trust_level, TrustLevel::TrustedOracle);
    assert_eq!(sorry.axiom_profile, AxiomProfile::AXIOMATIZED);
    assert!(sorry.has_sorry);
}

#[test]
fn test_classify_axiom_declaration() {
    let summary = classify_declaration("NNVerify.C007.BaBCert", &ProofQuality::NotATheorem, false);

    assert_eq!(summary.conjecture_id.as_deref(), Some("C007"));
    assert_eq!(summary.classification, TrustClassification::Axiom);
    assert_eq!(summary.domain_axiom_count, 0);
    assert!(summary.domain_axioms.is_empty());
    assert_eq!(summary.axiom_profile, AxiomProfile::AXIOMATIZED);
    assert_eq!(summary.trust_level, TrustLevel::PartiallyAxiomatized);
}

#[test]
fn test_build_report_with_mixed_declarations() {
    let declarations = vec![
        classify_declaration(
            "NNVerify.C001.compress_soundness",
            &ProofQuality::Constructive,
            false,
        ),
        classify_declaration(
            "NNVerify.C001.compress_tightness",
            &ProofQuality::AxiomDependent {
                axiom_count: 2,
                axioms: vec![
                    "NNVerify.C001.helper_axiom".to_owned(),
                    "NNVerify.C001.lp_dual_sound".to_owned(),
                ],
            },
            false,
        ),
        classify_declaration(
            "NNVerify.C001.helper_axiom",
            &ProofQuality::NotATheorem,
            false,
        ),
        classify_declaration(
            "NNVerify.C002.layernorm_zonotope",
            &ProofQuality::Unchecked,
            false,
        ),
    ];

    let report = build_trust_report(&declarations);

    assert_eq!(report.total_constructive, 1);
    assert_eq!(report.total_trusted, 1);
    assert_eq!(report.total_pending, 1);
    assert_eq!(report.total_axioms, 1);
    assert_eq!(report.total_domain_axioms, 2);
    assert_eq!(report.all_declarations.len(), 4);
}

#[test]
fn test_format_report_markdown() {
    let report = build_trust_report(&[
        classify_declaration(
            "NNVerify.C001.compress_soundness",
            &ProofQuality::Constructive,
            false,
        ),
        classify_declaration(
            "NNVerify.C001.compress_tightness",
            &ProofQuality::AxiomDependent {
                axiom_count: 1,
                axioms: vec!["NNVerify.C001.compress_tightness_helper".to_owned()],
            },
            false,
        ),
    ]);

    let markdown = format_trust_report(&report);

    assert!(markdown.contains("# Gamma-Crown Trust Report"));
    assert!(markdown.contains("## Summary"));
    assert!(markdown.contains("## Conjectures"));
    assert!(markdown.contains("### C001"));
    assert!(markdown.contains("## Declarations"));
    assert!(markdown.contains("| Declaration | Conjecture | Classification |"));
    assert!(markdown.contains("`NNVerify.C001.compress_tightness`"));
    assert!(markdown.contains("Mixed trust"));
}

#[test]
fn test_conjecture_grouping() {
    let report = build_trust_report(&[
        classify_declaration(
            "NNVerify.OrbitCROWN.C030a_equivariant_factors",
            &ProofQuality::Constructive,
            false,
        ),
        classify_declaration(
            "NNVerify.OrbitCROWN.C030b_quotient_crown_sound",
            &ProofQuality::AxiomDependent {
                axiom_count: 2,
                axioms: vec![
                    "NNVerify.OrbitCROWN.C030.bridge_axiom".to_owned(),
                    "NNVerify.OrbitCROWN.C030.bridge_axiom".to_owned(),
                ],
            },
            false,
        ),
        classify_declaration("NNVerify.C031.theorem", &ProofQuality::Constructive, false),
        classify_declaration("auxiliary_lemma", &ProofQuality::Constructive, false),
    ]);

    assert_eq!(report.conjecture_summaries.len(), 2);

    let c030 = report
        .conjecture_summaries
        .get("C030")
        .expect("C030 should be present");
    assert_eq!(
        c030.declarations,
        vec![
            "NNVerify.OrbitCROWN.C030a_equivariant_factors".to_owned(),
            "NNVerify.OrbitCROWN.C030b_quotient_crown_sound".to_owned(),
        ]
    );
    assert_eq!(c030.constructive_count, 1);
    assert_eq!(c030.trusted_count, 1);
    assert_eq!(c030.pending_count, 0);
    assert_eq!(c030.axiom_count, 0);
    assert!(!c030.is_fully_constructive);
    assert_eq!(
        c030.unique_domain_axioms,
        vec!["NNVerify.OrbitCROWN.C030.bridge_axiom".to_owned()]
    );

    let c031 = report
        .conjecture_summaries
        .get("C031")
        .expect("C031 should be present");
    assert!(c031.is_fully_constructive);
    assert_eq!(c031.declarations, vec!["NNVerify.C031.theorem".to_owned()]);
}

#[test]
fn test_empty_report() {
    let report = build_trust_report(&[]);

    assert!(report.conjecture_summaries.is_empty());
    assert!(report.all_declarations.is_empty());
    assert_eq!(report.total_constructive, 0);
    assert_eq!(report.total_trusted, 0);
    assert_eq!(report.total_pending, 0);
    assert_eq!(report.total_axioms, 0);
    assert_eq!(report.total_domain_axioms, 0);

    let markdown = format_trust_report(&report);
    assert!(markdown.contains("_No conjectures found._"));
    assert!(markdown.contains("_No declarations analyzed._"));
}
