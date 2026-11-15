// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn filesystem_module_names_preserve_one_component_per_directory() {
    let quoted = module_identity_for_relative_path(Path::new("A.B.lean")).expect("quoted file");
    let nested = module_identity_for_relative_path(Path::new("A/B.lean")).expect("nested file");
    assert_eq!(quoted, Name::anon().str("A.B"));
    assert_eq!(nested, Name::anon().str("A").str("B"));
    assert_ne!(quoted, nested);
    assert_eq!(
        module_identity_for_relative_path(Path::new("7.lean")),
        Some(Name::anon().str("7"))
    );
    assert!(module_identity_for_relative_path(Path::new("../A.lean")).is_none());
}

#[test]
fn project_import_scan_maps_quoted_and_nested_modules_independently() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::create_dir(dir.path().join("A")).expect("nested directory");
    fs::write(dir.path().join("A.B.lean"), "def quotedLeaf : Nat := 1\n").expect("quoted module");
    fs::write(dir.path().join("A/B.lean"), "def nestedLeaf : Nat := 2\n").expect("nested module");
    fs::write(
        dir.path().join("Entry.lean"),
        "import «A.B»\nimport A.B\nimport A.«B»\n",
    )
    .expect("entry");
    let sources = scan_project_sources(dir.path()).expect("source census");
    assert_eq!(sources.len(), 3);
    let by_module = sources
        .iter()
        .map(|source| (source.identity.clone(), source.relative_path.clone()))
        .collect();
    let entry = sources
        .iter()
        .find(|source| source.relative_path == "Entry.lean")
        .expect("entry record");
    let scan = parse_project_imports(entry, &by_module).expect("actual source imports");
    assert_eq!(
        scan.imports.len(),
        2,
        "deduplicate only equal structural names"
    );
    for (name, path) in [
        (Name::anon().str("A.B"), "A.B.lean"),
        (Name::anon().str("A").str("B"), "A/B.lean"),
    ] {
        let import = scan
            .imports
            .iter()
            .find(|import| import.identity == name)
            .expect("exact module");
        assert!(import.project_local);
        assert_eq!(import.source_path.as_deref(), Some(path));
    }
}
