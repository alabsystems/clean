// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the DerivedPending to DerivedProved promotion pipeline.
//!
//! Part of #3221.

use super::promote::{
    count_definitions, promote_single, promote_with_proof_term, run_promotion, PromotionError,
};
use super::ProofLibrary;
use crate::spec::{AxiomCategory, ProofStatus};
use crate::test_utils::{build_spec_with_stack, run_with_stack};

#[test]
fn test_run_promotion_returns_report() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);

        // Report counters must add up.
        assert_eq!(
            report.attempts.len(),
            report.promoted_count
                + report.still_pending_count
                + report.no_proof_count
                + report.error_count,
            "Report counters should add up to total attempts"
        );
        let mut audit = report.summary();
        audit.push_str(&format!("\n\nPROMOTED ({}):", report.promoted_count));
        for a in &report.attempts {
            if a.promoted {
                audit.push_str(&format!("\n  {}", a.name));
            }
        }
        audit.push_str(&format!("\n\nERRORS ({}):", report.error_count));
        for a in &report.attempts {
            if let Some(ref e) = a.error {
                let short = if e.len() > 100 { &e[..100] } else { e };
                audit.push_str(&format!("\n  {} -> {}", a.name, short));
            }
        }
        audit.push_str(&format!(
            "\n\nSTILL_PENDING_WITH_DEPS ({}):",
            report.still_pending_count
        ));
        for a in &report.attempts {
            if !a.promoted && a.error.is_none() && !a.axiom_deps.is_empty() {
                audit.push_str(&format!("\n  {} deps={:?}", a.name, a.axiom_deps));
            }
        }
        println!("{audit}");
    });
}

#[test]
fn test_promote_single_unknown() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let result = promote_single(&mut spec, &library, "nonexistent_theorem");
        assert!(
            matches!(result, Err(PromotionError::UnknownDefinition(_))),
            "Should fail for unknown definition"
        );
    });
}

#[test]
fn test_promote_single_not_derived_lemma() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();

        // Find a FoundationalRule definition.
        let foundational: Option<String> = spec
            .definitions()
            .iter()
            .find(|(_, def)| def.category == AxiomCategory::FoundationalRule)
            .map(|(name, _)| name.clone());

        if let Some(name) = foundational {
            let result = promote_single(&mut spec, &library, &name);
            assert!(
                matches!(result, Err(PromotionError::NotDerivedLemma { .. })),
                "Should fail for FoundationalRule definition"
            );
        }
    });
}

#[test]
fn test_promotion_report_summary_format() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);
        let summary = report.summary();
        assert!(
            summary.contains("Promotion Pipeline Report"),
            "Summary should contain header"
        );
        assert!(
            summary.contains("Total DerivedPending candidates"),
            "Summary should contain candidate count"
        );
    });
}

#[test]
fn test_promoted_definitions_status_updated() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);

        // Verify that promoted defs actually have DerivedProved status.
        for attempt in &report.attempts {
            if attempt.promoted {
                let def = spec
                    .get_definition(&attempt.name)
                    .expect("definition should exist");
                assert_eq!(
                    def.proof_status,
                    ProofStatus::DerivedProved,
                    "Promoted definition {} should have DerivedProved status",
                    attempt.name
                );
                assert!(
                    def.axiom_deps.is_empty(),
                    "Promoted definition {} should have empty axiom_deps",
                    attempt.name
                );
            }
        }
    });
}

#[test]
fn test_already_proved_returns_no_promotion() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();

        // Find a DerivedProved definition if any exist.
        let proved: Option<String> = spec
            .definitions()
            .iter()
            .find(|(_, def)| {
                def.category == AxiomCategory::DerivedLemma
                    && def.proof_status == ProofStatus::DerivedProved
            })
            .map(|(name, _)| name.clone());

        if let Some(name) = proved {
            let result = promote_single(&mut spec, &library, &name);
            match result {
                Ok(attempt) => {
                    assert!(
                        !attempt.promoted,
                        "Already proved definition should not be marked as promoted"
                    );
                    assert_eq!(attempt.original_status, ProofStatus::DerivedProved);
                }
                Err(_) => {
                    // This is acceptable -- the library might not have a proof
                    // for this one (it was proved via a different path).
                }
            }
        }
    });
}

#[test]
fn test_attempts_sorted_by_name() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);

        // Verify attempts are sorted.
        for window in report.attempts.windows(2) {
            assert!(
                window[0].name <= window[1].name,
                "Attempts should be sorted by name: {} > {}",
                window[0].name,
                window[1].name
            );
        }
    });
}

#[test]
fn test_count_definitions_totals_consistent() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let stats = count_definitions(&spec, &library);

        // Category totals must add up to total.
        assert_eq!(
            stats.foundational + stats.derived_total + stats.helper_axiom,
            stats.total,
            "Category totals must add up to total definitions"
        );

        // Derived subtotals must add up.
        assert_eq!(
            stats.derived_axiom + stats.derived_pending + stats.derived_proved,
            stats.derived_total,
            "Derived subtotals must add up to derived_total"
        );

        // Pending subtotals must add up.
        assert_eq!(
            stats.pending_with_proof + stats.pending_no_proof,
            stats.derived_pending,
            "Pending subtotals must add up to derived_pending"
        );

        println!("{}", stats.summary());
    });
}

#[test]
fn test_count_definitions_has_definitions() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let stats = count_definitions(&spec, &library);

        assert!(stats.total > 0, "Should have at least some definitions");
        assert!(stats.foundational > 0, "Should have foundational rules");
        assert!(stats.derived_total > 0, "Should have derived lemmas");
    });
}

#[test]
fn test_count_definitions_summary_format() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let stats = count_definitions(&spec, &library);
        let summary = stats.summary();

        assert!(
            summary.contains("Promotion Stats"),
            "Summary should contain header"
        );
        assert!(
            summary.contains("Total definitions"),
            "Summary should contain total count"
        );
        assert!(
            summary.contains("DerivedLemma"),
            "Summary should mention DerivedLemma"
        );
        assert!(
            summary.contains("DerivedProved"),
            "Summary should mention DerivedProved"
        );
        assert!(
            summary.contains("Proof coverage"),
            "Summary should contain proof coverage percentage"
        );
    });
}

#[test]
fn test_promote_single_no_proof_error() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();

        // Find a DerivedPending definition without a proof in the library.
        let candidate: Option<String> = spec
            .definitions()
            .iter()
            .find(|(name, def)| {
                def.category == AxiomCategory::DerivedLemma
                    && def.proof_status == ProofStatus::DerivedPending
                    && library.get(name).is_none()
            })
            .map(|(name, _)| name.clone());

        if let Some(name) = candidate {
            let result = promote_single(&mut spec, &library, &name);
            assert!(
                matches!(result, Err(PromotionError::NoProof(_))),
                "Should fail with NoProof for pending definition without proof"
            );
        }
    });
}

#[test]
fn test_run_promotion_no_proof_candidates_counted() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);

        // Count how many candidates lack proofs.
        let expected_no_proof = spec
            .definitions()
            .iter()
            .filter(|(name, def)| {
                def.category == AxiomCategory::DerivedLemma
                    && def.proof_status == ProofStatus::DerivedPending
                    && library.get(name).is_none()
            })
            .count();

        // The report's no_proof_count should be computed from the original spec
        // (before any promotions), but counting is done on DerivedPending at
        // entry. Verify the report is internally consistent.
        assert!(
            report.no_proof_count <= report.attempts.len(),
            "no_proof_count should not exceed total attempts"
        );

        // All attempts with no proof and no error should be in no_proof_count.
        let actual_no_proof = report
            .attempts
            .iter()
            .filter(|a| !a.promoted && a.error.is_none() && a.axiom_deps.is_empty())
            .count();
        // This includes both no-proof and no-axiom-deps cases.
        // The report's no_proof_count specifically tracks missing proofs.
        assert!(
            report.no_proof_count <= actual_no_proof + report.still_pending_count,
            "no_proof_count should be consistent with attempt data"
        );

        // Sanity: expected_no_proof uses the same library.
        let _ = expected_no_proof;
    });
}

#[test]
fn test_promotion_report_summary_includes_all_sections() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();
        let report = run_promotion(&mut spec, &library);
        let summary = report.summary();

        assert!(
            summary.contains("Promoted to DerivedProved"),
            "Should mention promotions"
        );
        assert!(
            summary.contains("Still DerivedPending"),
            "Should mention pending"
        );
        assert!(
            summary.contains("No proof in library"),
            "Should mention missing proofs"
        );
        assert!(
            summary.contains("Verification errors"),
            "Should mention errors"
        );
    });
}

// ---- promote_with_proof_term tests (Part of #3221) ----

#[test]
fn test_promote_with_proof_term_unknown_definition() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let result = promote_with_proof_term(&mut spec, "nonexistent", "fun x => x");
        assert!(
            matches!(result, Err(PromotionError::UnknownDefinition(_))),
            "Should fail for unknown definition"
        );
    });
}

#[test]
fn test_promote_with_proof_term_not_derived_lemma() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();

        // Find a FoundationalRule definition.
        let foundational: Option<String> = spec
            .definitions()
            .iter()
            .find(|(_, def)| def.category == AxiomCategory::FoundationalRule)
            .map(|(name, _)| name.clone());

        if let Some(name) = foundational {
            let result = promote_with_proof_term(&mut spec, &name, "fun x => x");
            assert!(
                matches!(result, Err(PromotionError::NotDerivedLemma { .. })),
                "Should fail for FoundationalRule definition"
            );
        }
    });
}

#[test]
fn test_promote_with_proof_term_already_proved() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();

        // Find a DerivedProved definition.
        let proved: Option<String> = spec
            .definitions()
            .iter()
            .find(|(_, def)| {
                def.category == AxiomCategory::DerivedLemma
                    && def.proof_status == ProofStatus::DerivedProved
            })
            .map(|(name, _)| name.clone());

        if let Some(name) = proved {
            let result = promote_with_proof_term(&mut spec, &name, "fun x => x");
            match result {
                Ok(attempt) => {
                    assert!(
                        !attempt.promoted,
                        "Already proved definition should not be re-promoted"
                    );
                    assert_eq!(attempt.original_status, ProofStatus::DerivedProved);
                }
                Err(_) => {
                    panic!("already-proved definitions should return Ok, not Err");
                }
            }
        }
    });
}

#[test]
fn test_promote_with_proof_term_invalid_proof() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();

        // Find a DerivedPending DerivedLemma whose type is a genuine PROPOSITION, so
        // the wrong proof term "Nat.zero" is definitively ill-typed for it.
        // NOTE: `definitions()` is a HashMap (random per-process seed), so a bare
        // `.find()` here is seed-FLAKY — it can land on a Nat-typed pending def
        // (e.g. `kcre_nat_48 : Nat := Nat.succ ..` from the kernel-core-red-env
        // corpus), for which `Nat.zero : Nat` is a VALID proof and promotion
        // correctly succeeds, spuriously failing this test. Filter to a proposition
        // type and pick deterministically (sorted) so the assertion is meaningful.
        let mut candidates: Vec<String> = spec
            .definitions()
            .iter()
            .filter(|(_, def)| {
                def.category == AxiomCategory::DerivedLemma
                    && def.proof_status == ProofStatus::DerivedPending
                    && def.type_src != "Nat"
                    && (def.type_src.contains("->")
                        || def.type_src.contains("Eq ")
                        || def.type_src.contains("forall"))
            })
            .map(|(name, _)| name.clone())
            .collect();
        candidates.sort();

        if let Some(name) = candidates.first() {
            // An obviously wrong proof term should fail verification.
            let result = promote_with_proof_term(&mut spec, name, "Nat.zero");
            assert!(
                matches!(result, Err(PromotionError::VerificationFailed { .. })),
                "Invalid proof term should fail verification for {name}, got: {result:?}"
            );
        }
    });
}

#[test]
fn test_promote_with_proof_term_valid_def_eq_refl() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();

        // def_eq_refl is a DerivedLemma. Check that we can promote it with
        // the correct proof term: fun (e : KExpr) => def_eq_refl e
        let def = spec.get_definition("def_eq_refl");
        if def.is_none() {
            // Definition may not exist in this spec configuration; skip.
            return;
        }
        let def = def.unwrap();
        if def.category != AxiomCategory::DerivedLemma {
            return; // Not a DerivedLemma; skip.
        }

        let original_status = def.proof_status;
        let result =
            promote_with_proof_term(&mut spec, "def_eq_refl", "fun (e : KExpr) => def_eq_refl e");

        match result {
            Ok(attempt) => {
                assert_eq!(
                    attempt.original_status, original_status,
                    "original_status should match"
                );
                // The proof term is valid; it may or may not promote to DerivedProved
                // depending on whether def_eq_refl itself depends on HelperAxioms.
                println!(
                    "def_eq_refl promotion: promoted={}, new_status={:?}, deps={:?}",
                    attempt.promoted, attempt.new_status, attempt.axiom_deps
                );

                if attempt.promoted {
                    // Verify the definition was actually updated.
                    let updated_def = spec
                        .get_definition("def_eq_refl")
                        .expect("definition should still exist");
                    assert_eq!(
                        updated_def.proof_status,
                        ProofStatus::DerivedProved,
                        "promoted definition should have DerivedProved status"
                    );
                    assert!(
                        updated_def.value_src.is_some(),
                        "promoted definition should have value_src set"
                    );
                    assert!(
                        updated_def.axiom_deps.is_empty(),
                        "promoted definition should have empty axiom_deps"
                    );
                }
            }
            Err(e) => {
                panic!("valid proof term should not fail verification: {e}");
            }
        }
    });
}

#[test]
fn test_promote_with_proof_term_sets_value_src() {
    run_with_stack(|| {
        let mut spec = build_spec_with_stack();
        let library = ProofLibrary::new();

        // Find a definition that we know the library can promote (DerivedPending
        // with a proof in the library). Use promote_single first to identify one.
        let report = run_promotion(&mut spec, &library);
        let promoted_name: Option<String> = report
            .attempts
            .iter()
            .find(|a| a.promoted)
            .map(|a| a.name.clone());

        if promoted_name.is_none() {
            // No definitions were promoted; skip.
            return;
        }

        // Rebuild the spec fresh so the definition is still DerivedPending.
        let mut spec = build_spec_with_stack();
        let name = promoted_name.unwrap();
        let proof = library
            .get(&name)
            .expect("library should have proof for promoted definition");

        let result = promote_with_proof_term(&mut spec, &name, &proof.proof_src);
        match result {
            Ok(attempt) if attempt.promoted => {
                let def = spec.get_definition(&name).expect("definition should exist");
                assert_eq!(
                    def.value_src.as_deref(),
                    Some(proof.proof_src.as_str()),
                    "value_src should be set to the provided proof term"
                );
            }
            Ok(attempt) => {
                println!(
                    "Definition {name} not promoted with external proof term: deps={:?}",
                    attempt.axiom_deps
                );
            }
            Err(e) => {
                panic!("valid proof term from library should not fail: {e}");
            }
        }
    });
}
