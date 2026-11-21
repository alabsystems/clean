// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::FileContext;
use clean_kernel::Environment;

const ORIGINAL: &str = include_str!("simp_nested_lookup.lean");

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
fn nested_lookup_uses_all_three_equalities() {
    let (committed, refused, detail) = check(ORIGINAL);
    assert!(committed && refused == 0, "{detail}");
}

#[test]
fn changing_the_result_or_the_lookup_argument_leaves_a_goal() {
    for (old, new) in [("= view 3", "= view 4"), ("hy : next x", "hy : next y")] {
        let changed = ORIGINAL.replace(old, new);
        assert_ne!(changed, ORIGINAL);
        let (committed, refused, detail) = check(&changed);
        assert!(
            !committed && refused == 1 && detail.contains("unsolved goal"),
            "{detail}"
        );
    }
}
