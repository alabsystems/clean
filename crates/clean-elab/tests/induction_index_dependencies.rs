// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::FileContext;
use clean_kernel::Environment;

const ORIGINAL: &str = include_str!("induction_index_dependencies.lean");

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
fn induction_specializes_hypotheses_depending_on_local_indices() {
    let (committed, refused, detail) = check(ORIGINAL);
    assert!(committed && refused == 0, "{detail}");
    let named_recursor = ORIGINAL.replace("induction h with", "induction h using Reaches.rec with");
    let (committed, refused, detail) = check(&named_recursor);
    assert!(committed && refused == 0, "{detail}");
    for (original, changed, reason) in [
        ("⟨fuel, execution⟩", "⟨fuel + 1, execution⟩", "mismatch"),
        (
            "induction h with",
            "induction h generalizing execution with",
            "generalized automatically",
        ),
    ] {
        let source = ORIGINAL.replace(original, changed);
        let (committed, refused, detail) = check(&source);
        assert!(
            !committed && refused == 1 && detail.to_lowercase().contains(reason),
            "{detail}"
        );
    }
}
