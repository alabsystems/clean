// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{package_owns, Ownership};
use std::fs;
use std::path::Path;
use tempfile::TempDir;

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().expect("parent")).expect("dirs");
    fs::write(path, text).expect("write");
}

fn package(lakefile: &str, text: &str) -> TempDir {
    let root = TempDir::new().expect("tempdir");
    write(&root.path().join(lakefile), text);
    root
}

#[test]
fn test_package_owns_a_toml_librarys_modules_and_no_other_file() {
    let root = package(
        "lakefile.toml",
        "name = \"ws\"\n\n[[lean_lib]]\nname = \"Inner\"\n\n[[require]]\nname = \"x\"\n",
    );
    let at = |rel: &str| package_owns(root.path(), &root.path().join(rel));
    assert_eq!(at("Inner.lean"), Ownership::Owned);
    assert_eq!(at("Inner/Lib.lean"), Ownership::Owned);
    assert_eq!(at("Main.lean"), Ownership::NotOwned);
    assert_eq!(at("proj/Probe.lean"), Ownership::NotOwned);
    assert_eq!(at("InnerX/Lib.lean"), Ownership::NotOwned);
}

#[test]
fn test_package_owns_toml_roots_src_dirs_and_executable_roots() {
    let root = package(
        "lakefile.toml",
        "name = \"p\"\nsrcDir = \"src\"\n\n[[lean_lib]]\nname = \"Lib\"\nroots = [\"B\", \"Std.Data.HashMap\"]\n\n\
         [[lean_lib]]\nname = \"Sub\"\nsrcDir = \"sub\"\n\n[[lean_exe]]\nname = \"tool\"\nroot = \"Tool.Main\"\n",
    );
    let at = |rel: &str| package_owns(root.path(), &root.path().join(rel));
    assert_eq!(at("src/B.lean"), Ownership::Owned);
    assert_eq!(at("src/Std/Data/HashMap.lean"), Ownership::Owned);
    assert_eq!(at("src/Std/Data/HashSet.lean"), Ownership::NotOwned);
    assert_eq!(at("src/sub/Sub/X.lean"), Ownership::Owned);
    assert_eq!(at("src/Tool/Main.lean"), Ownership::Owned);
    assert_eq!(at("src/Tool/Other.lean"), Ownership::NotOwned);
    // Outside the package's srcDir nothing is built.
    assert_eq!(at("B.lean"), Ownership::NotOwned);
}

#[test]
fn test_package_owns_lean_dsl_libraries_like_the_checkouts() {
    let root = package(
        "lakefile.lean",
        "import Lake\nopen Lake DSL\n\npackage «mathbot» where\n  leanOptions := #[\n    ⟨`autoImplicit, false⟩\n  ]\n\n\
         require mathlib from git \"https://example.invalid/mathlib4.git\"\n\n@[default_target]\n\
         lean_lib Mathbot where\n  roots := #[`Mathbot, `Mathbot.Manifest]\n\n\
         lean_lib «Mathbot.FalseControls» where\n  srcDir := \"Mathbot\" -- a comment\n  roots := #[`FalseControls]\n\n\
         lean_exe trustir_eval where\n  root := `TrustIrEval.Main\n",
    );
    let at = |rel: &str| package_owns(root.path(), &root.path().join(rel));
    assert_eq!(at("Mathbot.lean"), Ownership::Owned);
    assert_eq!(at("Mathbot/Manifest.lean"), Ownership::Owned);
    assert_eq!(at("Mathbot/FalseControls.lean"), Ownership::Owned);
    assert_eq!(at("TrustIrEval/Main.lean"), Ownership::Owned);
    assert_eq!(
        at("data/graduation/novel-2026-06/proof/Balancing.lean"),
        Ownership::NotOwned
    );
}

#[test]
fn test_package_owns_is_unknown_where_the_reading_cannot_settle() {
    for (lakefile, text) in [
        (
            "lakefile.toml",
            "name = \"p\"\n\n[[lean_lib]]\nname = \"P\"\nglobs = [\"P.+\"]\n",
        ),
        (
            "lakefile.lean",
            "package p\n\nlean_lib P where\n  globs := #[.submodules `P]\n",
        ),
        (
            "lakefile.lean",
            "package p\n\nlean_lib P where\n  roots := #[`P,\n    `Q]\n",
        ),
        (
            "lakefile.lean",
            "package p\n\ntarget ffi pkg : Unit := pure ()\n",
        ),
    ] {
        let root = package(lakefile, text);
        assert_eq!(
            package_owns(root.path(), &root.path().join("P/X.lean")),
            Ownership::Unknown,
            "{text}"
        );
    }
    // A lakefile that is a directory, which Lake refuses to read.
    let root = TempDir::new().expect("tempdir");
    fs::create_dir_all(root.path().join("lakefile.lean")).expect("dir");
    assert_eq!(
        package_owns(root.path(), &root.path().join("P/X.lean")),
        Ownership::Unknown
    );
}
