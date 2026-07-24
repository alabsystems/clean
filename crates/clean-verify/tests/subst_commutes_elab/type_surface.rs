// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::build_substitution_spec_with_stack;

#[test]
fn subst_commutes_definition_types_are_well_formed() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "instantiate_at_sort",
        "instantiate_at_app",
        "instantiate_at_lam",
        "instantiate_at_pi",
        "instantiate_at_bvar_commutes",
        "instantiate_at_nested_commutes",
        "instantiate_at_zero_commutes",
        "beta_subst_commutes",
        "def_eq_respects_subst",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("Missing definition {name}"));
        let elaborated_type = def
            .elaborated_type
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have an elaborated type"));
        assert!(
            !elaborated_type.has_loose_bvars(),
            "{name} elaborated type should not contain loose bvars"
        );
    }
}
