// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ratchet tests for response contract shape (Part of #2515).
//!
//! Ensures:
//! 1. Every method with an outcome boolean has a non-None OutcomeContract.
//! 2. The registry's outcome_contract metadata is consistent.
//! 3. All ns timing aliases round-trip correctly via the conversion helpers.

use crate::handlers::types::{ns_from_ms, ns_from_us};
use crate::registry::all_method_contracts;

/// Every canonical method that reports success/failure MUST have a non-None
/// outcome contract. Methods that don't report success (admin/meta endpoints)
/// are expected to have `None` for both fields.
///
/// This test prevents adding new verification/proof methods without updating
/// the registry's outcome_contract metadata.
#[test]
fn test_registry_outcome_contracts_are_populated() {
    let contracts = all_method_contracts();

    // There should be at least 40 methods in the registry
    assert!(
        contracts.len() >= 40,
        "Expected >=40 methods in registry, found {}",
        contracts.len(),
    );

    // Methods known to have outcome booleans must have at least one contract field
    let methods_with_outcomes = [
        "check",
        "prove",
        "verifyProof",
        "verifyProofBatch",
        "verifyFile",
        "verifyCert",
        "batchVerifyCert",
        "verifyC",
        "proveTLA",
        "batchProveTLA",
        "fillSorries",
        "composeProof",
        "batchCheck",
    ];

    for method_name in &methods_with_outcomes {
        let contract = contracts
            .iter()
            .find(|(name, _)| *name == *method_name)
            .unwrap_or_else(|| panic!("method '{}' not found in registry", method_name));

        assert!(
            contract.1.top_level_field.is_some() || contract.1.item_field.is_some(),
            "method '{}' should have at least one outcome field in its OutcomeContract, \
             but both top_level_field and item_field are None",
            method_name,
        );
    }

    // Admin methods should NOT have outcome contracts
    let admin_methods = ["serverInfo", "getConfig", "getMetrics", "getCacheMetrics"];
    for method_name in &admin_methods {
        let contract = contracts
            .iter()
            .find(|(name, _)| *name == *method_name)
            .unwrap_or_else(|| panic!("method '{}' not found in registry", method_name));

        assert!(
            contract.1.top_level_field.is_none(),
            "admin method '{}' should have None top_level_field, but has {:?}",
            method_name,
            contract.1.top_level_field,
        );
    }
}

/// Batch methods that return per-item results MUST have item_field set.
#[test]
fn test_batch_methods_have_item_outcome_field() {
    let contracts = all_method_contracts();

    let batch_methods_with_items = [
        ("batchCheck", "valid"),
        ("batchVerifyCert", "success"),
        ("batchProveTLA", "proved"),
        ("verifyProofBatch", "verified"),
        ("batchApplyTactic", "success"),
    ];

    for (method_name, expected_field) in &batch_methods_with_items {
        let contract = contracts
            .iter()
            .find(|(name, _)| *name == *method_name)
            .unwrap_or_else(|| panic!("method '{}' not found in registry", method_name));

        assert_eq!(
            contract.1.item_field,
            Some(*expected_field),
            "batch method '{}' should have item_field = {:?}",
            method_name,
            expected_field,
        );
    }
}

/// Outcome field names must be one of the canonical set.
#[test]
fn test_outcome_fields_use_canonical_names() {
    // `closed` is the canonical outcome field name for proofState.close
    // (boolean: was the proof state closed?). `accepted` is the canonical
    // outcome for addDecl (boolean: did the swarm worker's decl land in the
    // session overlay?). The other names cover the standard
    // verification/discovery/proof completion outcomes.
    let canonical_outcome_names = [
        "valid", "found", "success", "proved", "verified", "closed", "retained", "accepted",
    ];

    let contracts = all_method_contracts();

    for (name, contract) in &contracts {
        if let Some(field) = contract.top_level_field {
            assert!(
                canonical_outcome_names.contains(&field),
                "method '{}' has non-canonical outcome field '{}'. \
                 Canonical names: {:?}",
                name,
                field,
                canonical_outcome_names,
            );
        }
        if let Some(field) = contract.item_field {
            assert!(
                canonical_outcome_names.contains(&field),
                "method '{}' has non-canonical item_field '{}'. \
                 Canonical names: {:?}",
                name,
                field,
                canonical_outcome_names,
            );
        }
    }
}

/// Conversion helpers must produce correct nanosecond values.
#[test]
fn test_ns_from_ms_conversion() {
    assert_eq!(ns_from_ms(0), 0);
    assert_eq!(ns_from_ms(1), 1_000_000);
    assert_eq!(ns_from_ms(1000), 1_000_000_000);
    // Saturating: no overflow
    assert_eq!(ns_from_ms(u64::MAX), u64::MAX);
}

#[test]
fn test_ns_from_us_conversion() {
    assert_eq!(ns_from_us(0), 0);
    assert_eq!(ns_from_us(1), 1_000);
    assert_eq!(ns_from_us(1_000_000), 1_000_000_000);
    // Saturating: no overflow
    assert_eq!(ns_from_us(u64::MAX), u64::MAX);
}
