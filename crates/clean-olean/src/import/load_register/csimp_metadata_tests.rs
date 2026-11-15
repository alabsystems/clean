// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn imported_csimp_rejects_a_row_that_disagrees_with_its_actual_theorem() {
    let fixture = crate::test_support::compiled_fixture_dir("csimp_import");
    let mut env = Environment::for_lean_replay();
    crate::load_module_with_deps(
        &mut env,
        "CSimpImport",
        &[
            fixture,
            crate::require_pinned_lean_lib_path().expect("pinned SDK"),
        ],
    )
    .expect("genuine metadata fixture");
    let before = clean_kernel::env::csimp::rules_for(&env, None);
    for (from, to, theorem, owner) in [
        ("fast", "slow", "slow_eq_fast", Some("CSimpImport")),
        ("slow", "missing", "slow_eq_fast", Some("CSimpImport")),
        ("slow", "fast", "missing", Some("CSimpImport")),
        ("slow", "fast", "slow_eq_fast", None),
    ] {
        let extension = TypedExtension {
            extension_name: Name::from_string("Lean.Compiler.CSimp.ext"),
            source_rows: Some(1),
            undecoded_entries: 0,
            compiler_names: None,
            entries: vec![TypedExtensionEntry::CSimp {
                from: Name::from_string(from),
                to: Name::from_string(to),
                theorem: Name::from_string(theorem),
                namespace: None,
            }],
        };
        assert!(
            register_real_compiler_attr_entries(
                &mut env,
                owner,
                &[extension],
                &super::super::late_binding::CompilerNames::unknown(),
                &mut Vec::new(),
            )
            .is_err(),
            "inconsistent metadata must refuse the import"
        );
        assert_eq!(clean_kernel::env::csimp::rules_for(&env, None), before);
    }
}
