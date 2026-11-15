// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Prelude dependencies must be faithful to their own module environments.
use std::path::Path;
use std::process::{Command, Output};

fn library() -> std::path::PathBuf {
    clean_olean::pinned_lean_lib_path().expect("pinned Lean library")
}
fn lean(root: &Path, args: &[&str]) -> Output {
    let lib = library();
    let bin = lib
        .parent()
        .expect("lib")
        .parent()
        .expect("toolchain")
        .join("bin/lean");
    Command::new(bin)
        .current_dir(root)
        .env(
            "LEAN_PATH",
            std::env::join_paths([root, lib.as_path()]).expect("search path"),
        )
        .args(args)
        .output()
        .expect("pinned Lean")
}
fn clean(root: &Path, verb: &str) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
    command
        .current_dir(root)
        .env("LEAN_PATH", library())
        .args([verb, "Main.lean"]);
    if verb == "run" {
        command.args(["--decl", "answer"]);
    }
    command.output().expect("production Clean")
}
fn passed(result: &Output) {
    assert!(
        result.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn refused_artifact_world_preserves_source_only_isolation_and_never_falls_back() {
    let dir = project();
    std::fs::write(
        dir.path().join("lean-toolchain"),
        "leanprover/lean4:v4.99.0\n",
    )
    .expect("refused project world");
    std::fs::write(
        dir.path().join("Base.lean"),
        "prelude\ndef identityProof (P : Prop) (h : P) : P := h\n",
    )
    .expect("source-only prelude");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Base\ndef answer : Nat := 7\n",
    )
    .expect("source-only parent");
    passed(&lean(dir.path(), &["-o", "Base.olean", "Base.lean"]));
    passed(&lean(dir.path(), &["Main.lean"]));
    std::fs::remove_file(dir.path().join("Base.olean")).expect("source-only Clean input");
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");

    std::fs::write(
        dir.path().join("Base.lean"),
        "prelude\ndef borrowedInit : Nat := 7\n",
    )
    .expect("Init leakage control");
    assert!(!lean(dir.path(), &["Base.lean"]).status.success());
    for verb in ["check", "run"] {
        assert!(
            !clean(dir.path(), verb).status.success(),
            "{verb} lent bootstrap Init to a prelude in a refused world"
        );
    }

    std::fs::write(
        dir.path().join("Main.lean"),
        "import Init.Data.Nat.Basic\ndef answer : Nat := 7\n",
    )
    .expect("refused artifact import");
    for verb in ["check", "run"] {
        let output = clean(dir.path(), verb);
        assert!(
            !output.status.success(),
            "{verb} loaded another world's artifact"
        );
        let message = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(message.contains("v4.99.0"), "{message}");
        assert!(message.contains("Init.Data.Nat.Basic"), "{message}");
    }
}
fn project() -> tempfile::TempDir {
    let dir = tempfile::Builder::new()
        .prefix("x2-isolated-modules-")
        .tempdir()
        .expect("project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"isolated_modules\"\n",
    )
    .expect("package");
    dir
}
fn accepted(root: &Path) {
    passed(&clean(root, "check"));
    let output = clean(root, "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");
}
fn refused(root: &Path, file: &str) {
    assert!(
        !lean(root, &[file]).status.success(),
        "Lean accepted negative control"
    );
    for verb in ["check", "run"] {
        assert!(
            !clean(root, verb).status.success(),
            "{verb} accepted refused dependency"
        );
    }
}

#[test]
fn ordinary_entry_can_import_a_prelude_dependency() {
    let dir = project();
    std::fs::write(
        dir.path().join("Base.lean"),
        "prelude\nimport Init.Data.Nat.Basic\ndef importedAnswer : Nat := 7\n",
    )
    .expect("dependency");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Base\ndef answer : Nat := importedAnswer\n",
    )
    .expect("entry");
    passed(&lean(dir.path(), &["-o", "Base.olean", "Base.lean"]));
    passed(&lean(dir.path(), &["Main.lean"]));
    std::fs::remove_file(dir.path().join("Base.olean")).expect("source-only dependency");
    accepted(dir.path());
}

#[test]
fn sibling_preludes_are_compared_with_their_own_closures() {
    let dir = project();
    std::fs::write(
        dir.path().join("First.lean"),
        "prelude\nimport Init.Data.Nat.Basic\ndef siblingAnswer : Nat := 7\n",
    )
    .expect("first");
    std::fs::write(
        dir.path().join("Second.lean"),
        "prelude\ndef identityProp (p : Prop) : Prop := p\n",
    )
    .expect("second");
    std::fs::write(
        dir.path().join("Main.lean"),
        "prelude\nimport First\nimport Second\ndef answer : Nat := siblingAnswer\n",
    )
    .expect("entry");
    passed(&lean(dir.path(), &["-o", "First.olean", "First.lean"]));
    passed(&lean(dir.path(), &["-o", "Second.olean", "Second.lean"]));
    passed(&lean(dir.path(), &["Main.lean"]));
    for name in ["First.olean", "Second.olean"] {
        std::fs::remove_file(dir.path().join(name)).expect("remove oracle artifact");
    }
    accepted(dir.path());

    std::fs::write(
        dir.path().join("Second.lean"),
        "prelude\ndef bad : Nat := siblingAnswer\n",
    )
    .expect("unimported sibling twin");
    refused(dir.path(), "Second.lean");
}

#[test]
fn first_prelude_dependency_cannot_borrow_its_parents_implicit_init() {
    let dir = project();
    std::fs::write(
        dir.path().join("Base.lean"),
        "prelude\ndef bad : Nat := 7\n",
    )
    .expect("missing Init");
    std::fs::write(
        dir.path().join("Main.lean"),
        "import Base\ndef answer : Nat := 7\n",
    )
    .expect("ordinary parent");
    refused(dir.path(), "Base.lean");
}
