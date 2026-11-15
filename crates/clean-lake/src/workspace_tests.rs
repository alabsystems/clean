// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::fs;
use tempfile::TempDir;

#[test]
fn typed_module_paths_preserve_dotted_leaves_and_append_artifact_suffixes() {
    let leaf = Name::anon().str("A.B");
    let nested = Name::anon().str("A").str("B");
    assert_eq!(
        Workspace::path_to_module_name(Path::new("A.B.lean")).unwrap(),
        leaf
    );
    assert_eq!(
        Workspace::path_to_module_name(Path::new("A/B.lean")).unwrap(),
        nested
    );
    assert_ne!(leaf, nested);
    let tmp = TempDir::new().unwrap();
    let ws = Workspace::new(tmp.path(), "test");
    assert_eq!(
        ws.olean_path_name(&leaf).unwrap(),
        ws.lib_dir().join("A.B.olean")
    );
    assert_eq!(
        ws.olean_path("«A.B»").unwrap(),
        ws.lib_dir().join("A.B.olean")
    );
    assert_eq!(
        ws.olean_path("A.B").unwrap(),
        ws.lib_dir().join("A/B.olean")
    );
    assert_eq!(
        ws.olean_server_path("«A.B»").unwrap(),
        ws.lib_dir().join("A.B.olean.server")
    );
    assert_eq!(
        ws.olean_private_path("«A.B»").unwrap(),
        ws.lib_dir().join("A.B.olean.private")
    );
}

#[test]
fn typed_module_index_keeps_equal_display_files_and_source_spelling_roundtrips() {
    let (_tmp, ws) = workspace_with_modules("package p\n", &["A.B", "«A.B»", "«7»", "«λ 星»"]);
    let names = ws.all_module_names();
    assert_eq!(names.len(), 4);
    for spelling in ["A.B", "«A.B»", "«7»", "«λ 星»"] {
        let name = Workspace::parse_module_name(spelling).unwrap();
        assert!(names.contains(&name));
        assert_eq!(ws.find_module(spelling), ws.find_module_name(&name));
        assert!(ws.find_module_name(&name).unwrap().is_file());
    }
    assert_ne!(ws.find_module("A.B"), ws.find_module("«A.B»"));
    assert!(ws.find_module_name(&Name::anon().num(7)).is_none());
    let strings = ws.all_modules().unwrap();
    let reparsed: std::collections::HashSet<_> = strings
        .iter()
        .map(|text| Workspace::parse_module_name(text).unwrap())
        .collect();
    assert_eq!(reparsed.len(), 4);
    assert_eq!(reparsed, names.into_iter().collect());
}

#[test]
fn typed_import_graph_preserves_each_source_component_and_duplicate_import() {
    let (tmp, ws) = workspace_with_modules("package p\n", &["Main"]);
    fs::write(tmp.path().join("Main.lean"),
            "/- import Ignored -/\npublic import A.B\nimport «A.B»\nimport «7»\nimport A.B\ndef marker := \"import IgnoredToo\"\n").unwrap();
    let main = Name::anon().str("Main");
    let expected = vec![
        Name::anon().str("A").str("B"),
        Name::anon().str("A.B"),
        Name::anon().str("7"),
        Name::anon().str("A").str("B"),
    ];
    assert_eq!(ws.import_graph_names().unwrap()[&main], expected);
    let graph = ws.import_graph().unwrap();
    assert_eq!(
        graph["Main"]
            .iter()
            .map(|text| Workspace::parse_module_name(text).unwrap())
            .collect::<Vec<_>>(),
        expected
    );
}

/// One module per `import` (Lean 4.8.0): `import A B` imports `A`, and `B`
/// begins the body, so nothing after it is an import either.
#[test]
fn a_second_module_on_an_import_line_is_not_imported() {
    let (tmp, ws) = workspace_with_modules("package p\n", &["Main"]);
    fs::write(
        tmp.path().join("Main.lean"),
        "import A B\nimport C\ndef marker := 0\n",
    )
    .unwrap();
    let main = Name::anon().str("Main");
    assert_eq!(
        ws.import_graph_names().unwrap()[&main],
        vec![Name::anon().str("A")]
    );
}

#[test]
fn typed_import_graph_does_not_strip_comment_markers_inside_escaped_names() {
    let (tmp, ws) = workspace_with_modules("package p\n", &["Main"]);
    fs::write(
        tmp.path().join("Main.lean"),
        "import «A--B»\nimport «C/-D»\n",
    )
    .unwrap();
    assert_eq!(
        ws.import_graph_names().unwrap()[&Name::anon().str("Main")],
        vec![Name::anon().str("A--B"), Name::anon().str("C/-D")]
    );
}

#[test]
fn typed_module_path_refuses_unrepresentable_or_invalid_identity_without_alias() {
    let tmp = TempDir::new().unwrap();
    let ws = Workspace::new(tmp.path(), "test");
    for name in [
        Name::anon(),
        Name::anon().num(7),
        Name::anon().str(""),
        Name::anon().str(".."),
        Name::anon().str("A/B"),
        Name::anon().str("A\\B"),
        Name::anon().str("A\0B"),
    ] {
        assert!(ws.olean_path_name(&name).is_err(), "{name:?}");
        assert!(ws.find_module_name(&name).is_none(), "{name:?}");
    }
    for text in ["", "7", "A..B", ".ctor", "«unfinished"] {
        assert!(ws.olean_path(text).is_err(), "{text}");
        assert!(ws.find_module(text).is_none(), "{text}");
    }
    assert_eq!(
        Workspace::module_name_to_path("«7»").unwrap(),
        PathBuf::from("7.lean")
    );
}

#[test]
fn typed_module_library_prefix_does_not_confuse_dots_inside_one_component() {
    let (_tmp, ws) = workspace_with_modules(
        "package p\nlean_lib Foo\n",
        &["Foo", "Foo.Bar", "«Foo.Bar»", "FooBar"],
    );
    let mut expected = vec![Name::anon().str("Foo"), Name::anon().str("Foo").str("Bar")];
    expected.sort();
    assert_eq!(ws.lib_module_names("Foo").unwrap(), expected);
    assert_eq!(ws.lib_modules("Foo").unwrap(), vec!["Foo", "Foo.Bar"]);
}

#[cfg(unix)]
#[test]
fn typed_module_index_retains_non_utf8_refusal_and_unspellable_typed_names() {
    use std::os::unix::ffi::OsStringExt;
    let tmp = TempDir::new().unwrap();
    fs::write(tmp.path().join("lakefile.lean"), "package p\n").unwrap();
    fs::write(tmp.path().join("Good.lean"), "").unwrap();
    let invalid = std::ffi::OsString::from_vec(b"Bad\xff.lean".to_vec());
    assert!(Workspace::path_to_module_name(Path::new(&invalid)).is_err());
    let mut ws = Workspace::load(tmp.path()).unwrap();
    let root = ws.root().to_path_buf();
    // macOS rejects the filename at write() with EILSEQ. Exercise the same
    // actual entry-processing path as index_modules, without claiming that
    // an invalid filename was created on this filesystem.
    ws.index_module_path(&root, &root.join(&invalid));
    assert_eq!(ws.all_module_names(), vec![Name::anon().str("Good")]);
    assert_eq!(ws.module_index_errors().len(), 1);
    assert!(ws.validate_module_index().is_err());
    assert!(ws.all_modules().is_err());
    assert!(ws.import_graph_names().is_err());

    let clean = TempDir::new().unwrap();
    fs::write(clean.path().join("lakefile.lean"), "package p\n").unwrap();
    fs::write(clean.path().join("«.lean"), "").unwrap();
    let ws = Workspace::load(clean.path()).unwrap();
    ws.validate_module_index().unwrap();
    assert_eq!(ws.all_module_names(), vec![Name::anon().str("«")]);
    assert!(ws.all_modules().is_err(), "no invented source spelling");
    assert_eq!(ws.import_graph_names().unwrap().len(), 1);
}

#[test]
fn test_path_to_module_name() {
    assert_eq!(
        Workspace::path_to_module_name(Path::new("MyLib/Core.lean")).unwrap(),
        SurfaceName::generated_path("MyLib.Core").into_name()
    );
    assert_eq!(
        Workspace::path_to_module_name(Path::new("Main.lean")).unwrap(),
        SurfaceName::generated_path("Main").into_name()
    );
    assert_eq!(
        Workspace::path_to_module_name(Path::new("A/B/C.lean")).unwrap(),
        SurfaceName::generated_path("A.B.C").into_name()
    );
}

#[test]
fn test_module_name_to_path() {
    assert_eq!(
        Workspace::module_name_to_path("MyLib.Core").unwrap(),
        PathBuf::from("MyLib/Core.lean")
    );
    assert_eq!(
        Workspace::module_name_to_path("Main").unwrap(),
        PathBuf::from("Main.lean")
    );
}

#[test]
fn test_workspace_new() {
    let tmp = TempDir::new().unwrap();
    let ws = Workspace::new(tmp.path(), "test");
    assert_eq!(ws.config().package.name, "test");
    assert!(ws.toolchain().is_none());
}

#[test]
fn test_workspace_load() {
    let tmp = TempDir::new().unwrap();

    // Create lakefile.lean
    let lakefile = tmp.path().join("lakefile.lean");
    fs::write(&lakefile, "package test\nlean_lib Test").unwrap();

    // Create a source file
    let src = tmp.path().join("Test.lean");
    fs::write(&src, "-- Test module").unwrap();
    fs::copy(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/lean_toolchain/repo-root/lean-toolchain"),
        tmp.path().join("lean-toolchain"),
    )
    .unwrap();

    let ws = Workspace::load(tmp.path()).unwrap();
    assert_eq!(ws.config().package.name, "test");
    assert_eq!(ws.toolchain(), Some("leanprover/lean4:v4.13.0"));
    assert_eq!(ws.toolchain_version(), Some("v4.13.0"));
    assert!(
        ws.find_module("Test").is_some(),
        "workspace should find 'Test' module"
    );
    assert!(
        !ws.all_modules()
            .unwrap()
            .iter()
            .any(|module| module == "lakefile"),
        "workspace should not index lakefile.lean as a buildable module"
    );
}

#[test]
fn test_workspace_load_toml() {
    let tmp = TempDir::new().unwrap();

    // A TOML-configured project (no lakefile.lean) must load natively.
    let lakefile = tmp.path().join("lakefile.toml");
    fs::write(
        &lakefile,
        "name = \"test\"\n\n[[lean_lib]]\nname = \"Test\"\n",
    )
    .unwrap();

    let src = tmp.path().join("Test.lean");
    fs::write(&src, "-- Test module").unwrap();

    let ws = Workspace::load(tmp.path()).unwrap();
    assert_eq!(ws.config().package.name, "test");
    assert!(
        ws.find_module("Test").is_some(),
        "TOML workspace should find 'Test' module"
    );
    assert!(
        ws.config().libs.iter().any(|lib| lib.name == "Test"),
        "TOML workspace should parse the [[lean_lib]] target"
    );
}

#[test]
fn test_workspace_load_ignores_comment_lines_in_toolchain() {
    let tmp = TempDir::new().unwrap();
    let lakefile = tmp.path().join("lakefile.lean");
    fs::write(&lakefile, "package test\nlean_lib Test").unwrap();
    fs::write(
        tmp.path().join("lean-toolchain"),
        "\n# repo note\n-- Lean version\nleanprover/lean4:v4.29.1\n",
    )
    .unwrap();

    let ws = Workspace::load(tmp.path()).unwrap();
    assert_eq!(ws.toolchain(), Some("leanprover/lean4:v4.29.1"));
    assert_eq!(ws.toolchain_version(), Some("v4.29.1"));
}

#[test]
fn test_workspace_load_rejects_multiple_toolchain_identifiers() {
    let tmp = TempDir::new().unwrap();
    let lakefile = tmp.path().join("lakefile.lean");
    fs::write(&lakefile, "package test\nlean_lib Test").unwrap();
    fs::write(
        tmp.path().join("lean-toolchain"),
        "leanprover/lean4:v4.29.1\nleanprover/lean4:v4.28.0\n",
    )
    .unwrap();

    let err = Workspace::load(tmp.path()).unwrap_err();
    assert!(err
        .to_string()
        .contains("must contain a single toolchain identifier"));
}

#[test]
fn test_workspace_olean_path() {
    let tmp = TempDir::new().unwrap();
    let ws = Workspace::new(tmp.path(), "test");

    let olean = ws.olean_path("MyLib.Core").unwrap();
    assert!(olean.to_string_lossy().contains("MyLib"));
    assert!(olean.to_string_lossy().ends_with(".olean"));
}

/// Create a `.lean` source file for `module_name` under `root`,
/// translating the dotted module name into the matching directory layout.
fn write_module(root: &Path, module_name: &str) {
    let rel = Workspace::module_name_to_path(module_name).unwrap();
    let path = root.join(rel);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(&path, format!("-- module {module_name}")).unwrap();
}

/// Build a workspace from an inline lakefile plus a set of module files.
fn workspace_with_modules(lakefile: &str, modules: &[&str]) -> (TempDir, Workspace) {
    let tmp = TempDir::new().unwrap();
    fs::write(tmp.path().join("lakefile.lean"), lakefile).unwrap();
    for module in modules {
        write_module(tmp.path(), module);
    }
    let ws = Workspace::load(tmp.path()).unwrap();
    (tmp, ws)
}

#[test]
fn test_lib_modules_submodules_glob_excludes_self_and_unrelated() {
    let lakefile = "package p\nlean_lib Foo where\n  globs := #[.submodules `Foo]\n";
    let (_tmp, ws) =
        workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Foo.Baz", "Qux", "FooBar"]);

    let mut modules = ws.lib_modules("Foo").unwrap();
    modules.sort();

    assert_eq!(
        modules,
        vec!["Foo.Bar".to_string(), "Foo.Baz".to_string()],
        ".submodules Foo should include Foo.Bar/Foo.Baz but not Foo, Qux, or FooBar"
    );
}

#[test]
fn test_lib_modules_and_submodules_glob_includes_self() {
    let lakefile = "package p\nlean_lib Foo where\n  globs := #[.andSubmodules `Foo]\n";
    let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Qux"]);

    let mut modules = ws.lib_modules("Foo").unwrap();
    modules.sort();

    assert_eq!(
        modules,
        vec!["Foo".to_string(), "Foo.Bar".to_string()],
        ".andSubmodules Foo should include Foo and Foo.Bar but not Qux"
    );
}

#[test]
fn test_lib_modules_one_glob_includes_only_named_module() {
    let lakefile = "package p\nlean_lib Foo where\n  globs := #[.one `Foo]\n";
    let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Qux"]);

    let modules = ws.lib_modules("Foo").unwrap();

    assert_eq!(
        modules,
        vec!["Foo".to_string()],
        ".one Foo should include only Foo"
    );
}

#[test]
fn test_lib_modules_empty_globs_preserves_root_prefix_behavior() {
    // Regression pin: a lib without explicit globs must behave exactly as
    // before — each root plus every module whose name has the root as a
    // prefix (legacy prefix match, no glob filtering).
    let lakefile = "package p\nlean_lib Foo\n";
    let (_tmp, ws) = workspace_with_modules(lakefile, &["Foo", "Foo.Bar", "Foo.Baz", "Qux"]);

    let mut modules = ws.lib_modules("Foo").unwrap();
    modules.sort();

    assert_eq!(
        modules,
        vec![
            "Foo".to_string(),
            "Foo.Bar".to_string(),
            "Foo.Baz".to_string()
        ],
        "empty globs should include the root and its prefixed submodules, excluding unrelated Qux"
    );
}

#[test]
fn test_lib_modules_union_of_multiple_globs() {
    let lakefile = "package p\nlean_lib Lib where\n  globs := #[.one `Foo, .submodules `Bar]\n";
    let (_tmp, ws) = workspace_with_modules(
        lakefile,
        &["Foo", "Foo.Inner", "Bar", "Bar.A", "Bar.B", "Qux"],
    );

    let mut modules = ws.lib_modules("Lib").unwrap();
    modules.sort();

    assert_eq!(
        modules,
        vec!["Bar.A".to_string(), "Bar.B".to_string(), "Foo".to_string()],
        "union of .one Foo and .submodules Bar"
    );
}
