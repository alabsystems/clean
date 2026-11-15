// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean run` over a `.olean` that Lean 4.8.0 compiled (the v1 layout)
//! honours the module's `@[implemented_by]` and `@[extern]` bindings
//! (`docs/DECISIONS.md` R149). The fixture is
//! `crates/clean-olean/tests/fixtures/lean/v4.8.0/implemented_by_import/`,
//! and every expected output is what Lean 4.8.0's `lean --run` printed for the
//! same `main` (its README).
//!
//! Measured 2026-10-20 on the base binary (ccb6c1ab0), the source moved away
//! so that only the `.olean` can serve `import ImplByLib`: `implSlow 1`
//! printed `3` at exit 0, because every v1 extension row was `Unmeasured` and
//! no binding registered. Lean 4.8.0 prints `2`.
//!
//! Needs the `leanprover/lean4:v4.8.0` toolchain under elan, and FAILS
//! without it: a skip would leave the v1 route unmeasured while every runner
//! printed `ok` (`scripts/check_self_skipping_tests.py`). Every assertion is
//! on the exact bytes and the status of the real `clean` binary.

#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TOOLCHAIN: &str = "leanprover/lean4:v4.8.0";

/// Lean 4.8.0's `lib/lean` and `bin/lean`; a failure naming the toolchain
/// when it is not installed (module docs).
fn lean_v4_8_0() -> (PathBuf, PathBuf) {
    clean_olean::installed_lean_lib_path(TOOLCHAIN)
        .and_then(|lib| {
            let bin = lib.parent()?.parent()?.join("bin").join("lean");
            bin.is_file().then_some((lib, bin))
        })
        .unwrap_or_else(|| {
            panic!(
                "{TOOLCHAIN} is not installed under elan (`elan toolchain install \
                 {TOOLCHAIN}`): these tests measure the v1 route and never skip"
            )
        })
}

fn require_cc() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let has_cc = Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    assert!(
        has_cc,
        "a C compiler (`{cc}`) is required: these tests assert the bytes a compiled program prints"
    );
}

fn describe(output: &Output) -> String {
    format!(
        "status={:?}\nstdout={}\nstderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// A project whose build directory holds only `ImplByLib.olean`, compiled by
/// Lean 4.8.0 elsewhere; the source never enters it.
fn project(lean: &Path) -> tempfile::TempDir {
    project_of(lean, "implemented_by_import", "ImplByLib")
}

/// [`project`] for module `module` of the Lean 4.8.0 fixture family `family`.
fn project_of(lean: &Path, family: &str, module: &str) -> tempfile::TempDir {
    let source_file = format!("{module}.lean");
    let olean_file = format!("{module}.olean");
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-olean/tests/fixtures/lean/v4.8.0")
        .join(family)
        .join(&source_file);
    let build = tempfile::tempdir().expect("compile dir");
    std::fs::copy(&source, build.path().join(&source_file))
        .unwrap_or_else(|e| panic!("copy {}: {e}", source.display()));
    let compiled = Command::new(lean)
        .current_dir(build.path())
        .env("LEAN_PATH", build.path())
        .args([
            "--root",
            ".",
            "-o",
            olean_file.as_str(),
            source_file.as_str(),
        ])
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.display()));
    assert!(
        compiled.status.success(),
        "Lean 4.8.0: {}",
        describe(&compiled)
    );

    let dir = tempfile::tempdir().expect("project dir");
    std::fs::write(dir.path().join("lakefile.toml"), "").expect("write lakefile.toml");
    let lib = dir.path().join(".lake/build/lib/lean");
    std::fs::create_dir_all(&lib).expect("create build dir");
    std::fs::copy(build.path().join(&olean_file), lib.join(&olean_file))
        .unwrap_or_else(|e| panic!("copy {olean_file}: {e}"));
    dir
}

/// `clean run` a `main` printing `toString (<expr>)` over `import ImplByLib`,
/// with Lean 4.8.0's `Init` on `LEAN_PATH`.
fn run_main(dir: &Path, init: &Path, file: &str, expr: &str) -> Output {
    run_main_of(dir, init, "ImplByLib", file, expr)
}

/// [`run_main`] over `import <module>`.
fn run_main_of(dir: &Path, init: &Path, module: &str, file: &str, expr: &str) -> Output {
    std::fs::write(
        dir.join(file),
        format!("import {module}\n\ndef main : IO Unit := IO.println (toString ({expr}))\n"),
    )
    .expect("write main file");
    let lean_path = std::env::join_paths([dir.join(".lake/build/lib/lean"), init.to_path_buf()])
        .expect("LEAN_PATH");
    Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(["run", "--decl", "main", file])
        .current_dir(dir)
        .env("LEAN_PATH", lean_path)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean run: {err}"))
}

#[test]
fn test_lean_v4_8_0_implemented_by_runs_the_implementation() {
    let (init, lean) = lean_v4_8_0();
    require_cc();
    let project = project(&lean);
    for (file, expr, lean_prints) in [
        ("MainSlow.lean", "implSlow 1", "2\n"),
        ("MainCaller.lean", "implCaller 1", "20\n"),
        ("MainChain.lean", "chainHead 1", "8\n"),
        ("MainPlain.lean", "plainLib 1", "6\n"),
    ] {
        let output = run_main(project.path(), &init, file, expr);
        assert_eq!(
            (
                output.status.code(),
                String::from_utf8_lossy(&output.stdout).as_ref()
            ),
            (Some(0), lean_prints),
            "`{expr}`: Lean 4.8.0 prints {lean_prints:?}: {}",
            describe(&output)
        );
    }
}

#[test]
fn test_lean_v4_8_0_unsafe_implementation_and_extern_body_are_refused() {
    let (init, lean) = lean_v4_8_0();
    require_cc();
    let project = project(&lean);
    for (file, expr, names, tag) in [
        (
            "MainUnsafe.lean",
            "unsafeSlow 1",
            ["unsafeSlow", "unsafeFast"],
            "(implemented-by)",
        ),
        (
            "MainExtern.lean",
            "externBody 1",
            ["externBody", "clean_implby_fixture_no_such_symbol"],
            "(native-extern-body)",
        ),
    ] {
        let output = run_main(project.path(), &init, file, expr);
        assert_eq!(
            output.status.code(),
            Some(1),
            "`{expr}`: {}",
            describe(&output)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "",
            "`{expr}`: {}",
            describe(&output)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            names.iter().all(|name| stderr.contains(name)) && stderr.contains(tag),
            "`{expr}`: {}",
            describe(&output)
        );
    }
}

/// A late `attribute [implemented_by]` in a module Lean 4.8.0 compiled
/// (`implemented_by_late`): Lean 4.8.0 prints `30` for `lateCaller 1` and
/// `20` for `lateAfter 1`; every root is refused by name
/// (`native-implemented-by-order`), where the binding applied everywhere
/// prints `20` for both.
#[test]
fn test_lean_v4_8_0_late_binding_refuses_every_root() {
    let (init, lean) = lean_v4_8_0();
    require_cc();
    let project = project_of(&lean, "implemented_by_late", "LateLib");
    for (file, expr) in [
        ("MainLate.lean", "lateCaller 1"),
        ("MainAfter.lean", "lateAfter 1"),
    ] {
        let output = run_main_of(project.path(), &init, "LateLib", file, expr);
        assert_eq!(
            (
                output.status.code(),
                String::from_utf8_lossy(&output.stdout).as_ref()
            ),
            (Some(1), ""),
            "`{expr}`: {}",
            describe(&output)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("(native-implemented-by-order)")
                && stderr.contains("`lateCaller` names `lateSlow`")
                && stderr.contains("`lateSlow` itself was compiled before the binding"),
            "`{expr}`: {}",
            describe(&output)
        );
    }
}
