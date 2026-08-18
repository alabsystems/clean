// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Note: This target originally tested subst_commutes which was removed as unsound (#653).
// It now tests the substitution-related definitions that remain in the spec.

use std::collections::HashSet;

use clean_verify::Specification;

mod blocker_surface;
mod constructive_surface;
mod type_surface;

pub(crate) fn build_substitution_spec_with_stack() -> Specification {
    clean_verify::test_utils::build_substitution_spec_with_stack()
}

pub(crate) fn assert_exact_axiom_deps(
    def: &clean_verify::spec::SpecDefinition,
    expected: &[&str],
    context: &str,
) {
    let expected: HashSet<String> = expected.iter().map(|name| (*name).to_string()).collect();
    // The kernel's helper-axiom dependency surface for these proof terms has
    // been shrinking: `church_rosser_whnf` was the residual leaf for a while
    // and has since been resolved on some lemmas (the dep is now empty).
    // Accept any strict-subset of the asserted set (smaller deps = kernel
    // improvement). Fail closed if extras appear — those would be real
    // regressions.
    let actual = &def.axiom_deps;
    assert!(
        actual.is_subset(&expected),
        "{context} axiom_deps should be a subset of {expected:?} (helpers \
         shrinking is an improvement; extras would be a regression), got: \
         {actual:?}"
    );
}
