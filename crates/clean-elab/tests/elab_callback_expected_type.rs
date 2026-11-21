// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::FileContext;
use clean_kernel::Environment;

const ORIGINAL: &str = include_str!("elab_callback_expected_type.lean");

fn check(source: &str) -> (bool, usize, String) {
    let declarations = clean_parser::parse_file(source).unwrap();
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &declarations,
    }];
    let outcome = elaborate_module(&mut env, &mut context, &units, BatchOptions::islands());
    (
        outcome.committed,
        outcome.all_rejections().len(),
        outcome.render_rejections(),
    )
}

#[test]
fn later_predicate_and_expected_result_determine_callback_arguments() {
    let (committed, refused, detail) = check(ORIGINAL);
    assert!(committed && refused == 0, "{detail}");
    let changed = ORIGINAL.replace("sound _ _ _ _ hb", "sound _ ⟨false, n + 1⟩ _ _ hb");
    let (committed, refused, detail) = check(&changed);
    assert!(
        !committed && refused == 1 && detail.contains("inferredFoldedCall"),
        "{detail}"
    );
}

#[test]
fn later_evidence_resolves_nested_callback_predicates() {
    let original = include_str!("elab_nested_callback_premise.lean");
    let (committed, refused, detail) = check(original);
    assert!(committed && refused == 0, "{detail}");
    let changed = original.replace("⟨false, n⟩", "⟨false, n + 1⟩");
    let (committed, refused, detail) = check(&changed);
    assert!(
        !committed && refused == 1 && detail.contains("nestedTypedCallback"),
        "{detail}"
    );
}
