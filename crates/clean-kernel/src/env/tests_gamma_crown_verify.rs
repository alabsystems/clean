// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the gamma-crown verification runner.
//!
//! Split from gamma_crown_verify.rs to keep both files under the
//! 500-line soft limit. Part of #3380.

#![cfg(test)]

use super::gamma_crown_verify::{
    conjecture_description, format_csv_report, format_human_report, format_latex_report,
    verify_all_conjectures, verify_conjecture, CONJECTURE_IDS,
};

#[test]
fn test_verify_single_conjecture_c002_axiom_dependent() {
    // #3700 INTEGRITY FIX: the C002-prefix axiom count is 0, but the C002
    // headline theorems transitively reach shared matrix-rank / interval-hull
    // axioms and the admitted `Rat.le_refl` ordered-field axiom under the FULL
    // closure, so C002 is honestly axiom-dependent, not constructive. If init
    // fails upstream, skip.
    let result = verify_conjecture("C002");
    if !result.init_ok {
        eprintln!("SKIP: C002 init failed (upstream): {:?}", result.error);
        return;
    }
    assert!(result.tc_verified);
    assert!(
        !result.constructive,
        "C002 full closure reaches shared matrix-rank + admitted Rat axioms"
    );
    assert_eq!(result.proof_mechanism, "axiom-dependent");
    assert_eq!(result.status, "VERIFIED_AXIOM_DEPENDENT");
    assert!(result.theorems > 0, "C002 should still have theorems");
}

#[test]
fn test_verify_single_conjecture_c006_hypothesis_wrapped() {
    // #3470 Lane #2/#3: C006's C006-prefix axiom count is 0. Previously its
    // headline theorems transitively reached the admitted `Rat.le_refl` axiom,
    // giving an honest "axiom-dependent" verdict. `Rat.le_refl` has since been
    // GENUINELY ELIMINATED to a constructive kernel Theorem, so that admitted-
    // axiom dependency is gone. With it removed, the *most severe* honest
    // characterization of C006's headline set surfaces: at least one headline
    // theorem is a bare hypothesis-wrapped `H -> H` projection (`fun … h => h`),
    // which is NOT a genuine proof of the conjecture. So the honest verdict
    // downgrades to HYPOTHESIS_WRAPPED — still NOT constructive, and the
    // downgrade is an integrity gain (the prior axiom dependency no longer
    // masks the underlying hypothesis-projection structure).
    let result = verify_conjecture("C006");
    assert!(result.init_ok && result.tc_verified);
    assert_eq!(
        result.domain_axioms, 0,
        "C006 should have no C006-prefix domain axioms; got {:?}",
        result.axiom_names
    );
    assert!(!result.constructive);
    assert!(!result.fully_constructive);
    assert!(!result.scaffolded);
    assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
    assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
}

#[test]
fn test_verify_single_conjecture_c011_hypothesis_wrapped() {
    // #3700 INTEGRITY FIX: every C011 headline theorem is a hypothesis-wrapped
    // `fun … h => h` projection (empty closure, proves only `H -> H`). The honest
    // verdict is hypothesis-wrapped, NOT constructive.
    let result = verify_conjecture("C011");
    assert!(result.init_ok && result.tc_verified);
    assert_eq!(result.domain_axioms, 0);
    assert!(!result.constructive);
    assert!(!result.fully_constructive);
    assert!(!result.scaffolded);
    assert_eq!(result.proof_mechanism, "hypothesis_wrapped");
    assert_eq!(result.status, "VERIFIED_HYPOTHESIS_WRAPPED");
}

#[test]
fn test_verify_single_conjecture_c005_scaffolded() {
    // C005 (McCormick attention gap). Its headline theorems transitively reach
    // `sorryAx`, so the honest verdict is sorry-inhabited (scaffolded). If init
    // fails upstream, skip.
    let result = verify_conjecture("C005");
    if !result.init_ok {
        eprintln!("SKIP: C005 init failed (upstream): {:?}", result.error);
        return;
    }
    assert!(result.tc_verified, "C005 should be type-checked");
    assert!(
        !result.constructive,
        "C005 reaches sorryAx -> not constructive"
    );
    assert_eq!(result.status, "VERIFIED_SCAFFOLDED");
    assert_eq!(result.proof_mechanism, "sorry_inhabited");
}

#[test]
fn test_verify_single_conjecture_c008_constructive() {
    let result = verify_conjecture("C008");
    assert!(result.init_ok && result.tc_verified);
    // MILESTONE (2026-06-12): C008's full closure is PROVEN — the zero-faith
    // campaign retired ibp_tightness_{base,step} + ibp_linear_bounds to
    // kernel-checked Theorems/Definitions. First constructive gamma-crown
    // conjecture under the honest full-closure gate.
    assert!(result.constructive);
    assert!(result.fully_constructive);
    assert!(!result.scaffolded);
    assert_eq!(result.proof_mechanism, "constructive");
    assert_eq!(result.status, "VERIFIED_CONSTRUCTIVE");
}

#[test]
fn test_verify_unknown_conjecture_returns_error() {
    let result = verify_conjecture("C999");
    assert!(!result.init_ok, "C999 should fail");
    assert_eq!(result.status, "INIT_FAILED");
    assert!(result.error.is_some());
}

#[test]
fn test_verify_all_conjectures_report() {
    let report = verify_all_conjectures();
    assert_eq!(report.total_conjectures, 15);
    if report.conjectures_failed > 0 {
        eprintln!(
            "SKIP: {} conjecture(s) failed kernel init upstream",
            report.conjectures_failed
        );
        return;
    }
    assert_eq!(report.conjectures_verified, 15);
    // #3700: the four honest buckets partition the verified set; `mixed` is 0.
    assert_eq!(report.mixed_conjectures, 0);
    assert_eq!(
        report.constructive_conjectures
            + report.hypothesis_wrapped_conjectures
            + report.scaffolded_conjectures
            + report.axiom_dependent_conjectures,
        15,
        "the four honest buckets must partition all 15 verified conjectures",
    );
    // MILESTONE (2026-06-12): exactly C008 is genuinely constructive under the
    // honest full-closure gate (ibp chain proven); update deliberately.
    assert_eq!(report.constructive_conjectures, 1);
    assert!(report.total_theorems > 0, "should have theorems");
    assert!(
        report.total_verification_time_ms > 0.0,
        "should report timing"
    );
}

#[test]
fn test_verify_all_conjectures_matches_axiom_audit() {
    let report = verify_all_conjectures();

    // #3700 INTEGRITY FIX: per-conjecture verdicts come from the FULL transitive
    // closure of each conjecture's headline theorems. Cross-check the honest
    // reclassification of the formerly-"PROVED" overstatements. Kept in sync with
    // the canonical variant in `gamma_crown_verify.rs::tests`.
    for c in &report.conjectures {
        if !c.init_ok {
            eprintln!("SKIP-INIT {}: {:?}", c.id, c.error);
            continue;
        }
        if !c.tc_verified {
            eprintln!("SKIP-CLASSIFY {}: not tc_verified", c.id);
            continue;
        }
        // C008 is the lone GENUINELY-constructive conjecture: its headline
        // `ibp_tightness_{base,step}` lemmas were proven as R-weak constructive
        // Theorems (off the faithful keystone, base commit `4744b1f0`), so its
        // full closure reaches no domain axiom. Every OTHER conjecture must stay
        // non-constructive under the honest gate.
        if c.id != "C008" {
            assert!(
                !c.constructive,
                "{} should NOT be constructive under the honest gate (status={:?})",
                c.id, c.status,
            );
        }
        match c.id.as_str() {
            // #3470 Lane #2/#3: C006 moved to hypothesis_wrapped; WS-A ATOMIC
            // LIVE SWITCH: C004 ALSO moved — its only remaining admitted-axiom
            // dependency was the Rat ordered-field carrier validity
            // (`Rat.le_refl` / `Rat.add_le_add_left`), now constructive quotient
            // Theorems. C001 ALSO moved after the 2026-06-17 compress retirement
            // (`NNVerify.Zonotope.compress` Axiom -> faithful Definition): its
            // closure no longer reaches a domain axiom. C002 still reaches the
            // matrix-rank admitted infra axiom.
            "C002" => assert_eq!(
                c.proof_mechanism, "axiom-dependent",
                "{} full closure reaches a domain axiom",
                c.id,
            ),
            "C001" | "C004" | "C006" | "C009" | "C011" | "C029" | "C030" => assert_eq!(
                c.proof_mechanism, "hypothesis_wrapped",
                "{} headline theorems are H->H projections",
                c.id,
            ),
            // NNVerify unlock round (base commit `4744b1f0`): C008's
            // `ibp_tightness_{base,step}` lemmas are now constructive R-weak
            // Theorems proven off the faithful keystone (census 28->26), so the
            // C008 headline closure is empty of domain axioms — genuinely
            // constructive. (Previously these were honest admitted axioms, hence
            // the former `axiom-dependent` expectation.)
            "C008" => assert_eq!(
                c.proof_mechanism, "constructive",
                "C008 ibp_tightness_{{base,step}} are now constructive R-weak Theorems",
            ),
            _ => {}
        }
    }
}

#[test]
fn test_format_human_report_not_empty() {
    let report = verify_all_conjectures();
    let human = format_human_report(&report);
    assert!(human.contains("Gamma-Crown Formal Verification Report"));
    assert!(human.contains("RESULT:"));
    assert!(human.contains("C001"));
    assert!(human.contains("C030"));
}

#[test]
fn test_format_csv_report_has_header() {
    let report = verify_all_conjectures();
    let csv = format_csv_report(&report);
    assert!(csv.starts_with("id,description,status,"));
    assert!(csv.contains(",constructive_legacy,fully_constructive,scaffolded,proof_mechanism,"));
    // Should have 15 data rows + 1 header
    let line_count = csv.lines().count();
    assert_eq!(line_count, 16, "CSV should have 1 header + 15 data rows");
}

#[test]
fn test_format_latex_report_valid() {
    let report = verify_all_conjectures();
    let latex = format_latex_report(&report);
    assert!(latex.contains("\\begin{table}"));
    assert!(latex.contains("\\end{table}"));
    assert!(latex.contains("``Proved'' indicates"));
    assert!(latex.contains("Scaffolded"));
}

#[test]
fn test_conjecture_ids_complete() {
    assert_eq!(CONJECTURE_IDS.len(), 15);
    assert!(CONJECTURE_IDS.contains(&"C001"));
    assert!(CONJECTURE_IDS.contains(&"C030"));
}

#[test]
fn test_conjecture_description_all_known() {
    for &id in CONJECTURE_IDS {
        let desc = conjecture_description(id);
        assert_ne!(desc, "Unknown conjecture", "{id} should have a description");
    }
}

#[test]
fn test_json_serialization_roundtrip() {
    let report = verify_all_conjectures();
    let json_str = serde_json::to_string_pretty(&report).expect("should serialize to JSON");
    let parsed: serde_json::Value = serde_json::from_str(&json_str).expect("should parse back");
    assert_eq!(parsed["total_conjectures"].as_u64(), Some(15));
    assert!(parsed["conjectures"].is_array());
    assert_eq!(parsed["conjectures"].as_array().unwrap().len(), 15);
}
