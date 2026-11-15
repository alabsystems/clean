// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{env::Environment, name::Name};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_typed_module_with_deps_cached, load_typed_module_with_deps_parallel, parse_typed_imports,
    typed_module_rel_path, ModuleCache, OleanExporter, TypedImportFlags,
};
use std::path::PathBuf;

/// The `module_twins` family compiled by the pinned Lean
/// (`tests/fixtures/lean/v4.30.0-rc2/module_twins/README.md`): `Root.lean` lists
/// `import «Module.part»` before `import Module.part`, so the rows of
/// `Root.olean` come out in that order. Fails closed when the toolchain is absent.
fn root() -> PathBuf {
    compiled_fixture_dir("module_twins")
}

fn bytes() -> Vec<u8> {
    std::fs::read(root().join("Root.olean")).expect("pinned-Lean compiled Root.olean")
}

#[test]
fn typed_paths_match_upstream_component_and_add_extension_semantics() {
    for (name, expected) in [
        (Name::anon().str("Module.part"), "Module.part.olean"),
        (Name::anon().str("Module").str("part"), "Module/part.olean"),
        (Name::anon().str("07"), "07.olean"),
        (Name::anon().str("7"), "7.olean"),
        (Name::anon().str("α.β"), "α.β.olean"),
    ] {
        assert_eq!(
            typed_module_rel_path(&name).expect("valid typed path"),
            PathBuf::from(expected)
        );
    }
}

#[test]
fn numeric_module_components_are_not_digit_strings() {
    assert!(typed_module_rel_path(&Name::anon().num(7)).is_err());
    assert!(typed_module_rel_path(&Name::anon().num(7).str("tail")).is_err());
    assert!(typed_module_rel_path(&Name::anon()).is_err());
    assert_eq!(
        typed_module_rel_path(&Name::anon().str("7")).unwrap(),
        PathBuf::from("7.olean")
    );
}

#[test]
fn legacy_export_flags_are_explicitly_not_modern_import_all() {
    for bit in [false, true] {
        let bytes = OleanExporter::export_with_env(
            &Environment::default(),
            &[("Module.part", bit)],
            &[],
            "0000000000000000000000000000000000000000",
        )
        .expect("legacy exporter");
        let imports = parse_typed_imports(&bytes).expect("typed legacy imports");
        assert_eq!(imports.len(), 1);
        assert_eq!(
            imports[0].module_name,
            Name::anon().str("Module").str("part")
        );
        assert_eq!(
            imports[0].flags,
            TypedImportFlags::CleanLegacy { runtime_only: bit }
        );
    }
}

#[test]
fn actual_import_rows_preserve_names_and_all_modern_flags() {
    let imports = parse_typed_imports(&bytes()).expect("actual raw imports");
    assert_eq!(imports.len(), 2);
    assert_eq!(imports[0].module_name, Name::anon().str("Module.part"));
    assert_eq!(
        imports[1].module_name,
        Name::anon().str("Module").str("part")
    );
    assert_ne!(imports[0].module_name, imports[1].module_name);
    for import in imports {
        assert_eq!(
            import.flags,
            TypedImportFlags::LeanV2 {
                import_all: false,
                is_exported: true,
                is_meta: false,
            }
        );
    }
}

#[test]
fn legacy_exported_digit_module_components_remain_strings() {
    for (spelling, expected) in [
        ("7", Name::anon().str("7")),
        ("07", Name::anon().str("07")),
        ("Pkg.7", Name::anon().str("Pkg").str("7")),
        ("Pkg.07", Name::anon().str("Pkg").str("07")),
    ] {
        let data = OleanExporter::export_with_env(
            &Environment::default(),
            &[(spelling, false)],
            &[],
            "0000000000000000000000000000000000000000",
        )
        .expect("export module import");
        let imports = parse_typed_imports(&data).expect("typed import roundtrip");
        assert_eq!(imports.len(), 1);
        assert_eq!(
            imports[0].module_name, expected,
            "module path identity changed for {spelling}"
        );
    }
}

/// The `import_flags` family (`tests/fixtures/lean/v4.30.0-rc2/import_flags/README.md`):
/// four `module` + `prelude` sources each importing exactly `Lean` under one
/// modifier, compiled by the pinned Lean on first use. Only each base `.olean`'s
/// single import row is read; the `.olean.server` / `.olean.private` / `.ir`
/// by-products beside it are ignored.
#[test]
fn actual_four_modern_flag_controls_have_distinct_meanings() {
    let flags = compiled_fixture_dir("import_flags");
    for (file, expected) in [
        ("FlagPlain", (false, false, false)),
        ("FlagAll", (true, false, false)),
        ("FlagPublic", (false, true, false)),
        ("FlagMeta", (false, false, true)),
    ] {
        let data =
            std::fs::read(flags.join(format!("{file}.olean"))).expect("pinned-Lean flag fixture");
        let imports = parse_typed_imports(&data).expect("actual flags");
        assert_eq!(imports.len(), 1);
        assert_eq!(imports[0].module_name, Name::anon().str("Lean"));
        assert_eq!(
            imports[0].flags,
            TypedImportFlags::LeanV2 {
                import_all: expected.0,
                is_exported: expected.1,
                is_meta: expected.2,
            }
        );
    }
}

#[test]
fn malformed_array_row_and_boolean_do_not_drop_imports() {
    fn word(bytes: &[u8], offset: usize) -> u64 {
        u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
    }
    let original = bytes();
    assert_eq!(original[5], 2);
    let base = word(&original, 80);
    let root = (word(&original, 88) - base) as usize;
    let array = (word(&original, root + 8) - base) as usize;
    let row = (word(&original, array + 24) - base) as usize;
    let cases = [
        (array + 7, vec![247]), // Reserved array tag, not an empty population.
        (array + 16, 0u64.to_le_bytes().to_vec()), // Capacity < two imports.
        (array + 24, 1u64.to_le_bytes().to_vec()), // Scalar row, never skip it.
        (row + 6, vec![0]),     // Missing module identity.
        (row + 16, vec![2]),    // Noncanonical importAll.
        (row + 17, vec![2]),    // Noncanonical isExported.
        (row + 18, vec![2]),    // Noncanonical isMeta.
    ];
    for (offset, mutation) in cases {
        let mut changed = original.clone();
        changed[offset..offset + mutation.len()].copy_from_slice(&mutation);
        assert!(
            parse_typed_imports(&changed).is_err(),
            "accepted mutation at {offset}"
        );
    }
}

#[test]
fn explicit_typed_roots_resolve_their_own_files_in_both_modes() {
    let paths = [root()];
    for parallel in [false, true] {
        let cache = ModuleCache::new();
        for _ in 0..2 {
            for (module, required, absent) in [
                (Name::anon().str("Module.part"), "quotedTag", "nestedTag"),
                (
                    Name::anon().str("Module").str("part"),
                    "nestedTag",
                    "quotedTag",
                ),
            ] {
                let mut env = Environment::default();
                let summaries = if parallel {
                    load_typed_module_with_deps_parallel(&mut env, &module, &paths, &cache)
                } else {
                    load_typed_module_with_deps_cached(&mut env, &module, &paths, &cache)
                }
                .expect("exact typed root");
                assert!(summaries.iter().all(|s| s.skipped_constants.is_empty()));
                assert_eq!(env.constants().count(), 1);
                assert!(env.get_const(&Name::anon().str(required)).is_some());
                assert!(env.get_const(&Name::anon().str(absent)).is_none());
            }
        }
        assert_eq!(cache.len(), 2);
    }
}
