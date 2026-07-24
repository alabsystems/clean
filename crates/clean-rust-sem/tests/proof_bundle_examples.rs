// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::examples::{inventory_restock_example, raw_write_invalidates_reader_example};
use clean_rust_sem::{ObligationKind, SourceProgram};

#[test]
fn test_inventory_restock_builds_clean_proof_bundle() {
    let bundle = inventory_restock_example()
        .build_proof_bundle()
        .expect("inventory_restock should build a proof bundle");

    assert!(
        bundle
            .borrow_results
            .values()
            .all(|result| result.errors.is_empty()),
        "inventory_restock should stay borrow-clean: {:?}",
        bundle
            .borrow_results
            .iter()
            .filter(|(_, result)| !result.errors.is_empty())
            .map(|(name, result)| (name, &result.errors))
            .collect::<Vec<_>>()
    );
    assert!(
        !bundle.obligations.is_empty(),
        "inventory_restock should emit ownership obligations"
    );
    assert!(
        !bundle.translated_types.is_empty(),
        "inventory_restock should expose translated Lean-facing function types"
    );
    assert!(
        bundle.aliasing_observation.passed,
        "inventory_restock should pass aliasing observation: {}",
        bundle.aliasing_observation.summary
    );
    assert!(
        bundle.aliasing_observation.translated_value.is_some(),
        "inventory_restock should translate the observed return value"
    );
}

#[test]
fn test_negative_example_bundle_preserves_aliasing_failure() {
    let bundle = raw_write_invalidates_reader_example()
        .build_proof_bundle()
        .expect("negative example should still build a proof bundle");

    assert!(
        !bundle.obligations.is_empty(),
        "negative example should still emit ownership obligations"
    );
    assert!(
        !bundle.aliasing_observation.passed,
        "negative example should record aliasing failure"
    );
    assert!(
        bundle.aliasing_observation.summary.contains("borrow error"),
        "negative example should preserve borrow-error wording, got: {}",
        bundle.aliasing_observation.summary
    );
    assert!(
        bundle.aliasing_observation.translated_value.is_none(),
        "negative example should not report a translated success value"
    );
}

#[test]
fn test_inline_bundle_captures_mut_borrow_and_move_sites() {
    let source = r#"
        struct Packet { value: u32 }

        fn main() -> u32 {
            let mut packet: Packet = Packet { value: 1u32 };
            let slot: &mut u32 = &mut packet.value;
            *slot = 2u32;
            let moved: Packet = packet;
            moved.value
        }
    "#;

    let bundle = SourceProgram::parse(source)
        .expect("inline source should parse")
        .build_proof_bundle()
        .expect("inline source should build a proof bundle");

    assert!(
        bundle
            .obligations
            .iter()
            .any(|obligation| obligation.kind == ObligationKind::BorrowValid),
        "bundle should include a borrow-valid obligation: {:?}",
        bundle
            .obligations
            .iter()
            .map(|obligation| (&obligation.kind, &obligation.source_location))
            .collect::<Vec<_>>()
    );
    assert!(
        bundle
            .obligations
            .iter()
            .any(|obligation| obligation.kind == ObligationKind::OwnershipTransfer),
        "bundle should include an ownership-transfer obligation: {:?}",
        bundle
            .obligations
            .iter()
            .map(|obligation| (&obligation.kind, &obligation.source_location))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_bundle_translated_types_cover_lowered_closure_functions() {
    let source = r#"
        fn main() -> u32 {
            let add_one = |x: u32| -> u32 { x + 1u32 };
            add_one(41u32)
        }
    "#;

    let bundle = SourceProgram::parse(source)
        .expect("closure source should parse")
        .build_proof_bundle()
        .expect("closure source should build a proof bundle");

    assert!(
        bundle.lowered.functions.len() > 1,
        "closure lowering should synthesize at least one extra lowered function"
    );
    assert_eq!(
        bundle.translated_types.len(),
        bundle.lowered.functions.len(),
        "translated function types should cover every lowered function, including closures"
    );
}
