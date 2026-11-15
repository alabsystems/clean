// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`Workspace::module_lean_args`]: Lake 4.8.0's per-module `lean` arguments.

use crate::config::LakeConfig;
use crate::workspace::Workspace;
use std::path::Path;

fn workspace(lakefile: &str) -> Workspace {
    let config = LakeConfig::parse(lakefile).expect("fixture lakefile parses");
    Workspace::from_config(Path::new("/nonexistent-module-options-root"), config)
}

const LAKEFILE: &str = "package p where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n  \
     moreLeanArgs := #[\"-DmaxRecDepth=1000\"]\n\n\
     lean_lib A where\n  leanOptions := #[⟨`autoImplicit, true⟩]\n  \
     moreLeanArgs := #[\"--tstack=100\"]\n\n\
     lean_lib B where\n  globs := #[.submodules `Extra]\n\n\
     lean_exe tool where\n  root := `Tool.Main\n  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]\n";

#[test]
fn test_module_lean_args_follow_lake_order() {
    let ws = workspace(LAKEFILE);
    assert_eq!(
        ws.module_lean_args("A.Sub").expect("A owns A.Sub"),
        vec![
            "-DautoImplicit=false",
            "-DmaxRecDepth=1000",
            "-DautoImplicit=true",
            "--tstack=100",
        ],
        "package leanOptions, package moreLeanArgs, lib leanOptions, lib moreLeanArgs"
    );
}

#[test]
fn test_module_lean_args_glob_owner_and_unowned_module() {
    let ws = workspace(LAKEFILE);
    let package_only = vec!["-DautoImplicit=false", "-DmaxRecDepth=1000"];
    // `B` owns `Extra.X` by its glob, and has no options of its own.
    assert_eq!(
        ws.module_lean_args("Extra.X").expect("B owns it"),
        package_only
    );
    // `.submodules` excludes the base; nothing owns `Elsewhere`.
    assert_eq!(ws.module_lean_args("Extra").expect("unowned"), package_only);
    assert_eq!(
        ws.module_lean_args("Elsewhere").expect("unowned"),
        package_only
    );
    // A prefix is a component prefix: `AB` is not under `A`.
    assert_eq!(ws.module_lean_args("AB").expect("unowned"), package_only);
}

#[test]
fn test_module_lean_args_exe_root_gets_exe_options() {
    let ws = workspace(LAKEFILE);
    let mut expected = vec!["-DautoImplicit=false", "-DmaxRecDepth=1000"];
    expected.push("-DrelaxedAutoImplicit=false");
    assert_eq!(
        ws.module_lean_args("Tool.Main").expect("exe root"),
        expected
    );
}

#[test]
fn test_module_lean_args_refuse_unreadable_options() {
    let ws = workspace("package p\n\nlean_lib A where\n  leanOptions := opts\n");
    let err = ws
        .module_lean_args("A")
        .expect_err("unreadable lib options refuse A");
    assert!(err.to_string().contains("leanOptions := opts"), "{err}");
    // A module the unreadable target does not own is unaffected.
    assert!(ws.module_lean_args("B").expect("unowned").is_empty());
}

/// Lake 4.8.0's `Package.findModule?` is `findSomeRev?`: of two libraries
/// that can build an imported module, the LAST declared one compiles it.
#[test]
fn test_module_lean_args_import_owner_is_last_buildable_library() {
    let ws = workspace(
        "package p\n\nlean_lib X where\n  globs := #[.andSubmodules `M]\n  \
         leanOptions := #[⟨`autoImplicit, true⟩]\n\n\
         lean_lib Y where\n  globs := #[.andSubmodules `M]\n  \
         leanOptions := #[⟨`autoImplicit, false⟩]\n",
    );
    assert_eq!(
        ws.module_lean_args("M.A").expect("Y owns it"),
        vec!["-DautoImplicit=false"]
    );
}

/// Two libraries that both root a module give it different options
/// depending on the target built (Lake: `lake build` of the
/// `@[default_target]` Strict refuses `Opts` under `-DautoImplicit=false`).
/// Clean refuses the module rather than pick the first.
#[test]
fn test_module_lean_args_overlapping_roots_with_different_options_refuse() {
    let ws = workspace(
        "package p\n\nlean_lib Loose where\n  roots := #[`Opts]\n\n\
         @[default_target] lean_lib Strict where\n  roots := #[`Opts]\n  \
         leanOptions := #[⟨`autoImplicit, false⟩]\n",
    );
    let err = ws
        .module_lean_args("Opts")
        .expect_err("the two routes disagree");
    assert!(err.to_string().contains("different arguments"), "{err}");
}

/// The review's `own` package: lib B (declared first) roots `Top.Sub` with
/// autoImplicit on; lib A roots `Top`, so `findModule?` resolves an import
/// of `Top.Sub` to A, under the package's autoImplicit off. Pinned
/// `lake build` compiles it with `-DautoImplicit=false` and refuses it.
#[test]
fn test_module_lean_args_first_library_does_not_win_over_import_owner() {
    let ws = workspace(
        "package p where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n\
         lean_lib B where\n  roots := #[`Top.Sub]\n  leanOptions := #[⟨`autoImplicit, true⟩]\n\n\
         @[default_target]\nlean_lib A where\n  roots := #[`Top]\n",
    );
    ws.module_lean_args("Top.Sub")
        .expect_err("B's options are not the only ones Lake may use");
    assert_eq!(
        ws.module_lean_args("Top").expect("A roots Top"),
        vec!["-DautoImplicit=false"]
    );
}

/// An executable's root is compiled through `LeanExe.toLeanLib`: the
/// executable's options apply even when a library also covers the module,
/// and when the two differ Clean refuses (pinned `lake build e` refuses the
/// review's `exe` package).
#[test]
fn test_module_lean_args_exe_root_under_a_library_uses_exe_options() {
    let ws = workspace(
        "package p\n\nlean_lib L where\n  roots := #[`L]\n\n\
         lean_exe e where\n  root := `L.Main\n  leanOptions := #[⟨`autoImplicit, false⟩]\n",
    );
    let err = ws
        .module_lean_args("L.Main")
        .expect_err("lib L and exe e disagree");
    assert!(err.to_string().contains("lean_exe `e`"), "{err}");
    // The trust_ir-semantics shape: the library and the executable both add
    // nothing to the package's options, so the routes agree.
    let ws = workspace(
        "package p where\n  leanOptions := #[⟨`autoImplicit, false⟩]\n\n\
         lean_lib TrustIrEval where\n  srcDir := \".\"\n\n\
         lean_exe trustir_eval where\n  root := `TrustIrEval.Main\n",
    );
    assert_eq!(
        ws.module_lean_args("TrustIrEval.Main")
            .expect("routes agree"),
        vec!["-DautoImplicit=false"]
    );
}

/// `weakLeanArgs` come first (`mod.weakLeanArgs ++ mod.leanArgs`), package
/// before library, so a `leanOptions` entry of the same name wins.
#[test]
fn test_module_lean_args_weak_args_precede_lean_args() {
    let ws = workspace(
        "package p where\n  weakLeanArgs := #[\"-DautoImplicit=false\"]\n  \
         leanOptions := #[⟨`relaxedAutoImplicit, false⟩]\n\n\
         lean_lib A where\n  weakLeanArgs := #[\"-DmaxRecDepth=9\"]\n",
    );
    assert_eq!(
        ws.module_lean_args("A").expect("A"),
        vec![
            "-DautoImplicit=false",
            "-DmaxRecDepth=9",
            "-DrelaxedAutoImplicit=false"
        ]
    );
}

/// A dependency's modules are compiled with the DEPENDENCY's lakefile, not
/// the root's (pinned `lake build` compiles the review's `dep/D.lean` with
/// `-DautoImplicit=false` from `d`'s own lakefile).
#[test]
fn test_module_lean_args_dependency_module_uses_its_own_package() {
    let tmp = tempfile::TempDir::new().expect("tempdir");
    let root = tmp.path().join("root");
    let dep = tmp.path().join("d");
    std::fs::create_dir_all(&root).expect("root dir");
    std::fs::create_dir_all(&dep).expect("dep dir");
    std::fs::write(
        root.join("lakefile.lean"),
        "package r\n\nrequire d from \"../d\"\n\nlean_lib Rt\n",
    )
    .expect("root lakefile");
    std::fs::write(
        root.join("lake-manifest.json"),
        r#"{"version": 7, "packagesDir": ".lake/packages", "packages": [{"type": "path",
           "name": "d", "manifestFile": "lake-manifest.json", "inherited": false,
           "dir": "../d", "configFile": "lakefile.lean"}], "name": "r", "lakeDir": ".lake"}"#,
    )
    .expect("manifest");
    std::fs::write(root.join("Rt.lean"), "import D\n").expect("root module");
    std::fs::write(
        dep.join("lakefile.lean"),
        "package d where leanOptions := #[⟨`autoImplicit, false⟩]\n\nlean_lib D\n",
    )
    .expect("dep lakefile");
    std::fs::write(dep.join("D.lean"), "theorem t (x : Foo) : x = x := rfl\n").expect("dep");
    let ws = Workspace::load(&root).expect("workspace loads");
    assert_eq!(
        ws.module_lean_args("D").expect("d's own options"),
        vec!["-DautoImplicit=false"]
    );
    assert!(ws.module_lean_args("Rt").expect("root").is_empty());
    // A dependency lakefile Clean cannot read refuses its modules.
    std::fs::write(dep.join("lakefile.lean"), "-- no package declaration\n").expect("rewrite");
    ws.module_lean_args("D")
        .expect_err("an unreadable dependency lakefile refuses D");
}
