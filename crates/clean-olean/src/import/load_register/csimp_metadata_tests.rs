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
                &owner.map(str::to_owned),
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

#[test]
fn imported_inline_metadata_without_implemented_by_restores_only_genuine_modes() {
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
    .expect("genuine inline metadata without implementedBy");
    let name = Name::from_string("macroIgnore");
    clean_kernel::env::csimp::begin_source_module(
        &mut env,
        Name::from_string("UsesFixture"),
        vec![Name::from_string("CSimpImport")],
    );
    assert!(env.is_macro_inline(&name));
    assert!(
        clean_kernel::env::csimp::rules_for(&env, None)
            .iter()
            .any(|rule| rule.theorem == Name::from_string("slow_eq_fast")),
        "companion compiler rows must retain their semantic base-module owner"
    );
    for (rows, owner) in [
        (None, Some("CSimpImport")),
        (Some(vec![(name.clone(), 5)]), Some("CSimpImport")),
        (Some(vec![(name.clone(), 2)]), None),
        (Some(vec![(name.clone(), 1)]), Some("AnotherModule")),
    ] {
        let extension = TypedExtension {
            extension_name: Name::from_string("Lean.Compiler.inlineAttrs"),
            source_rows: Some(1),
            undecoded_entries: 1,
            entries: vec![],
            compiler_names: rows,
        };
        assert!(register_real_inline_entries(&mut env, owner, &[extension]).is_err());
        assert!(
            env.is_macro_inline(&name),
            "malformed metadata must not replace the genuine hint"
        );
    }
}

#[test]
fn a_mixed_owner_inline_table_refuses_before_installing_any_hint() {
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
    .expect("genuine fixture");
    let fast = Name::from_string("fast");
    assert!(!env.is_noinline(&fast));
    let extension = TypedExtension {
        extension_name: Name::from_string("Lean.Compiler.inlineAttrs"),
        source_rows: Some(2),
        undecoded_entries: 2,
        entries: vec![],
        compiler_names: Some(vec![(fast.clone(), 1), (Name::from_string("Nat"), 1)]),
    };
    assert!(register_real_inline_entries(&mut env, Some("CSimpImport"), &[extension]).is_err());
    assert!(
        !env.is_noinline(&fast),
        "a rejected mixed table must not install its earlier own row"
    );
}
