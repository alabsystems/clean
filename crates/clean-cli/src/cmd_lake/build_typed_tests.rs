// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual source-closure paths and digest invalidation, not native compilation.

use super::*;
use clean_kernel::Name;
use clean_lake::{LakeConfig, LeanExe, PackageConfig, Workspace};

fn workspace(root: &Path) -> Workspace {
    let mut config = LakeConfig::default();
    config.package = PackageConfig::minimal("typed_native_closure");
    Workspace::from_config(root, config)
}

fn executable(root: &str) -> LeanExe {
    LeanExe {
        name: "typed_native_closure".to_owned(),
        root: root.to_owned(),
        ..Default::default()
    }
}

#[test]
fn import_header_preserves_quoted_components_and_real_comment_state() {
    let modules = import_modules(
        "/- header -/\nprelude\npublic import «A.B»\npublic import A.B\npublic import «A--B»\npublic import «A B»\ndef x := 0\nimport Later\n",
    );
    assert_eq!(
        modules,
        vec![
            Name::anon().str("A.B"),
            Name::anon().str("A").str("B"),
            Name::anon().str("A--B"),
            Name::anon().str("A B"),
        ]
    );
    assert_ne!(modules[0], modules[1]);
}

#[test]
fn native_source_closure_keeps_dotted_paths_and_quoted_comment_names_distinct() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir(dir.path().join("A")).unwrap();
    std::fs::write(
        dir.path().join("Main.lean"),
        "import «A.B»\nimport A.B\nimport «A--B»\nimport «A B»\ndef main := 0\n",
    )
    .unwrap();
    for (path, source) in [
        ("A.B.lean", "def atomic := 1\n"),
        ("A/B.lean", "def nested := 2\n"),
        ("A--B.lean", "def commentName := 3\n"),
        ("A B.lean", "def spaceName := 4\n"),
    ] {
        std::fs::write(dir.path().join(path), source).unwrap();
    }
    let ws = workspace(dir.path());
    let exe = executable("Main");
    let closure = executable_source_closure(&ws, &exe).unwrap();
    let expected: BTreeSet<_> = ["Main.lean", "A.B.lean", "A/B.lean", "A--B.lean", "A B.lean"]
        .iter()
        .map(|path| std::fs::canonicalize(dir.path().join(path)).unwrap())
        .collect();
    assert_eq!(closure.iter().cloned().collect::<BTreeSet<_>>(), expected);
    let initial = source_closure_digest(&closure);
    std::fs::write(dir.path().join("A.B.lean"), "def atomic := 11\n").unwrap();
    let changed_atomic = source_closure_digest(&executable_source_closure(&ws, &exe).unwrap());
    assert_ne!(initial, changed_atomic);
    std::fs::write(dir.path().join("A/B.lean"), "def nested := 22\n").unwrap();
    assert_ne!(
        changed_atomic,
        source_closure_digest(&executable_source_closure(&ws, &exe).unwrap())
    );
}

#[test]
fn quoted_executable_root_resolves_one_dotted_filesystem_component() {
    let dir = tempfile::tempdir().unwrap();
    std::fs::create_dir(dir.path().join("A")).unwrap();
    std::fs::write(dir.path().join("A.B.lean"), "def atomic := 1\n").unwrap();
    std::fs::write(dir.path().join("A/B.lean"), "def nested := 2\n").unwrap();
    let ws = workspace(dir.path());
    let atomic = executable_source_closure(&ws, &executable("«A.B»")).unwrap();
    let nested = executable_source_closure(&ws, &executable("A.B")).unwrap();
    assert_eq!(
        atomic,
        vec![std::fs::canonicalize(dir.path().join("A.B.lean")).unwrap()]
    );
    assert_eq!(
        nested,
        vec![std::fs::canonicalize(dir.path().join("A/B.lean")).unwrap()]
    );
    assert_ne!(atomic, nested);
}
