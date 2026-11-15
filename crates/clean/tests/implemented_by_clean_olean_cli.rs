// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `.olean` that `clean lake build` wrote carries its module's
//! `@[implemented_by]` and `@[extern]` bindings, and `clean run` honours them
//! in a program that imports it (`docs/DECISIONS.md` R149, Clean payload
//! version 5).
//!
//! Measured 2026-10-19 on the base binary (ccb6c1ab0): with `ImplLib`'s
//! source moved away, so that `import ImplLib` can only load the artifact
//! Clean built, `implSlow 1` printed `3` at exit 0. The payload carried no
//! binding, so the logical body compiled. Pinned Lean v4.30.0-rc2 (`lake
//! build` of the same project, then the executable) prints `2`; its
//! `externBody` executable fails to link (`undefined symbol:
//! clean_implby_clean_olean_no_such_symbol`) and `lean --run` stops with
//! "Could not find native implementation of external declaration
//! 'externBody'"; `plainLib 1` prints `6`.
//!
//! The module's ORDER rows travel too: a late `attribute [implemented_by]`
//! in `LateLib`, after `lateCaller` was added, makes every program importing
//! the artifact refuse (`native-implemented-by-order`), as the same command
//! in the file being run does. Measured 2026-10-20 on the lane binary before
//! that fix (behaviourally 507b056c7): `lateCaller 1` printed `20` at exit 0,
//! where pinned Lean prints `30`.
//!
//! Every assertion is on the exact bytes `clean run` printed and its status.
//! The driver is the real `clean` binary.

#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const LAKEFILE: &str =
    "import Lake\nopen Lake DSL\n\npackage implby\n\n@[default_target]\nlean_lib ImplLib\n";

const IMPL_LIB: &str = "def implFast (n : Nat) : Nat := n + 1

@[implemented_by implFast]
def implSlow (n : Nat) : Nat := n + 2

@[extern \"clean_implby_clean_olean_no_such_symbol\"]
def externBody (n : Nat) : Nat := n + 3

def plainLib (n : Nat) : Nat := n + 5
";

const LATE_LAKEFILE: &str =
    "import Lake\nopen Lake DSL\n\npackage late\n\n@[default_target]\nlean_lib LateLib\n";

const LATE_LIB: &str = "def lateFast (n : Nat) : Nat := Nat.add n 1

def lateSlow (n : Nat) : Nat := Nat.add n 2

def lateCaller (n : Nat) : Nat := Nat.mul (lateSlow n) 10

attribute [implemented_by lateFast] lateSlow

def lateAfter (n : Nat) : Nat := Nat.mul (lateSlow n) 10
";

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

fn cc_available() -> bool {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    Command::new(cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// No C compiler, no verdict: fail closed, never skip.
fn require_cc() {
    assert!(
        cc_available(),
        "a C compiler is required: these tests assert the bytes a compiled program prints"
    );
}

fn run_clean(args: &[&str], dir: &Path) -> Output {
    Command::new(clean_path())
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
}

fn describe(output: &Output) -> String {
    format!(
        "status={:?}\nstdout={}\nstderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// A Lake project whose `ImplLib` Clean built, with the source moved away so
/// an importer can only load the artifact.
fn built_project() -> tempfile::TempDir {
    built_project_of(LAKEFILE, "ImplLib", IMPL_LIB)
}

/// A Lake project of the one library `module` (source `source`), built by
/// `clean lake build`, with the source moved away.
fn built_project_of(lakefile: &str, module: &str, source: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("lakefile.lean"), lakefile).expect("write lakefile.lean");
    let file = format!("{module}.lean");
    std::fs::write(dir.path().join(&file), source).expect("write the library source");
    let build = run_clean(&["lake", "build"], dir.path());
    assert_eq!(
        build.status.code(),
        Some(0),
        "clean lake build: {}",
        describe(&build)
    );
    let artifact = dir.path().join(format!(".lake/build/lib/{module}.olean"));
    assert!(
        artifact.is_file(),
        "clean lake build wrote no {}",
        artifact.display()
    );
    std::fs::rename(
        dir.path().join(&file),
        dir.path().join(format!("{file}.moved")),
    )
    .expect("move the library source away");
    dir
}

/// `clean run` a `main` that prints `toString (<expr>)` over `import ImplLib`.
fn run_main(dir: &Path, file: &str, expr: &str) -> Output {
    run_main_of(dir, "ImplLib", file, expr)
}

/// [`run_main`] over `import <module>`.
fn run_main_of(dir: &Path, module: &str, file: &str, expr: &str) -> Output {
    std::fs::write(
        dir.join(file),
        format!("import {module}\n\ndef main : IO Unit := IO.println (toString ({expr}))\n"),
    )
    .expect("write main file");
    run_clean(&["run", "--decl", "main", file], dir)
}

#[test]
fn test_clean_olean_implemented_by_runs_the_implementation() {
    require_cc();
    let project = built_project();
    let output = run_main(project.path(), "MainImpl.lean", "implSlow 1");
    assert_eq!(output.status.code(), Some(0), "{}", describe(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "2\n",
        "pinned Lean runs implFast: {}",
        describe(&output)
    );
}

#[test]
fn test_clean_olean_extern_with_body_is_refused_by_name() {
    require_cc();
    let project = built_project();
    let output = run_main(project.path(), "MainExtern.lean", "externBody 1");
    assert_eq!(output.status.code(), Some(1), "{}", describe(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "",
        "{}",
        describe(&output)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("externBody")
            && stderr.contains("clean_implby_clean_olean_no_such_symbol")
            && stderr.contains("(native-extern-body)"),
        "{}",
        describe(&output)
    );
}

#[test]
fn test_clean_olean_plain_declaration_compiles_its_body() {
    require_cc();
    let project = built_project();
    let output = run_main(project.path(), "MainPlain.lean", "plainLib 1");
    assert_eq!(output.status.code(), Some(0), "{}", describe(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "6\n",
        "{}",
        describe(&output)
    );
}

#[test]
fn test_clean_olean_keeps_custom_and_anonymous_hadd_bodies() {
    require_cc();
    let source = "instance customNatHAdd : HAdd Nat Nat Nat where
  hAdd a b := Nat.add (Nat.add a b) 40

def namedBody (n : Nat) : Nat := n + 2

instance : HAdd Nat Nat Nat where
  hAdd a b := Nat.add (Nat.add a b) 70

def anonymousBody (n : Nat) : Nat := n + 2
";
    let project = built_project_of(LAKEFILE, "ImplLib", source);
    for (file, expr, expected) in [
        ("MainNamed.lean", "namedBody 1", "43\n"),
        ("MainAnonymous.lean", "anonymousBody 1", "73\n"),
    ] {
        let output = run_main(project.path(), file, expr);
        assert_eq!(output.status.code(), Some(0), "{}", describe(&output));
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            expected,
            "{}",
            describe(&output)
        );
    }
}

#[test]
fn test_clean_olean_source_import_requires_its_own_artifact_import() {
    require_cc();
    let project = built_project();
    let dir = project.path();
    std::fs::write(
        dir.join("Root.lean"),
        "import ImplLib\ndef rootValue : Nat := plainLib 1\n",
    )
    .expect("source root imports the hidden-source artifact");
    std::fs::write(
        dir.join("Child.lean"),
        "import ImplLib\ndef childValue : Nat := plainLib 2\n",
    )
    .expect("positive child imports its actual dependency");
    std::fs::write(
        dir.join("Main.lean"),
        "import Root\nimport Child\ndef main : IO Unit := IO.println (toString childValue)\n",
    )
    .expect("program importing both source modules");
    let positive = run_clean(&["run", "--decl", "main", "Main.lean"], dir);
    assert_eq!(positive.status.code(), Some(0), "{}", describe(&positive));
    assert_eq!(positive.stdout, b"7\n", "{}", describe(&positive));

    // Root's artifact declarations are already in the shared working env.
    // Removing ONLY Child's import must still refuse its unchanged body.
    std::fs::write(
        dir.join("Child.lean"),
        "def childValue : Nat := plainLib 2\n",
    )
    .expect("negative child has no artifact import");
    let negative = run_clean(&["run", "--decl", "main", "Main.lean"], dir);
    assert_eq!(negative.status.code(), Some(1), "{}", describe(&negative));
    assert!(negative.stdout.is_empty(), "{}", describe(&negative));
    let message = String::from_utf8_lossy(&negative.stderr);
    assert!(
        message.contains("Child")
            && message.contains("could not elaborate in its own import closure")
            && message.contains("Unknown identifier: plainLib"),
        "{}",
        describe(&negative)
    );
}

/// The late binding travels as ORDER rows: every root of a program importing
/// the Clean-built `LateLib` is refused by name, `lateAfter` (whose code
/// pinned Lean compiled after the command, `20`) as well as `lateCaller`
/// (`30` in Lean, `20` here before the rows travelled).
#[test]
fn test_clean_olean_late_binding_refuses_every_root() {
    require_cc();
    let project = built_project_of(LATE_LAKEFILE, "LateLib", LATE_LIB);
    for (file, expr) in [
        ("MainLate.lean", "lateCaller 1"),
        ("MainAfter.lean", "lateAfter 1"),
    ] {
        let output = run_main_of(project.path(), "LateLib", file, expr);
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
            stderr.contains("(native-implemented-by-order)")
                && stderr.contains("`lateCaller` names `lateSlow`")
                && stderr.contains("`lateSlow` itself was compiled before the binding"),
            "`{expr}`: {}",
            describe(&output)
        );
    }
}
