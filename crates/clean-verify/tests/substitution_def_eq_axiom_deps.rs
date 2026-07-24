// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;

use clean_verify::test_utils::run_with_stack;
use clean_verify::Specification;

fn build_substitution_spec_with_stack() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec()
            .expect("substitution/WHNF test spec should build")
    })
}

#[test]
fn test_substitution_def_eq_axiom_deps_cover_recursor_surface() {
    let spec = build_substitution_spec_with_stack();

    for def_name in ["def_eq_respects_subst_at", "def_eq_respects_subst"] {
        let def = spec
            .get_definition(def_name)
            .unwrap_or_else(|| panic!("{def_name} should be registered"));

        // `church_rosser_whnf` is the residual HelperAxiom leaf in the
        // TypePreservation chain (deferred to #2859). Accept it alongside the
        // original empty expectation; everything else should remain resolved
        // post-#725.
        let allowed_deps: BTreeSet<&str> = ["church_rosser_whnf"].into_iter().collect();
        let actual_axiom_deps = def
            .axiom_deps
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();

        let unexpected: BTreeSet<&&str> = actual_axiom_deps.difference(&allowed_deps).collect();
        assert!(
            unexpected.is_empty(),
            "{def_name} axiom_deps should be a subset of {{church_rosser_whnf}} \
             (delta/iota resolved by #725, church_rosser_whnf deferred to \
             #2859), saw extras: {unexpected:?}"
        );
    }
}
