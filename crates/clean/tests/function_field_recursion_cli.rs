// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Function-valued structural children through production check and run.

use std::path::Path;
use std::process::{Command, Output};

fn lean(root: &Path) -> Output {
    let lib = clean_olean::pinned_lean_lib_path().expect("pinned Lean library");
    let bin = lib
        .parent()
        .expect("lib")
        .parent()
        .expect("toolchain")
        .join("bin/lean");
    Command::new(bin)
        .current_dir(root)
        .arg("Main.lean")
        .output()
        .expect("pinned Lean")
}

fn clean(root: &Path, verb: &str) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
    command
        .current_dir(root)
        .env(
            "LEAN_PATH",
            clean_olean::pinned_lean_lib_path().expect("pinned library"),
        )
        .args([verb, "Main.lean"]);
    if verb == "run" {
        command.args(["--decl", "answer"]);
    }
    command.output().expect("production Clean")
}

fn passed(output: &Output) {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn indexed_structural_children_preserve_recursive_computation() {
    let dir = tempfile::tempdir().expect("isolated project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"function_fields\"\n",
    )
    .expect("package");
    let source = "prelude\nimport Init.Data.Nat.Basic\ninductive Tree where\n  | leaf\n  | node (children : Bool → Tree)\ndef height : Tree → Nat\n  | .leaf => 0\n  | .node children => height (children true) + 1\ndef sample : Tree := .node (fun b => match b with | false => .leaf | true => .node (fun _ => .leaf))\ntheorem height_sample : height sample = 2 := rfl\ndef answer : Nat := 7\n";
    std::fs::write(dir.path().join("Main.lean"), source).expect("source");
    passed(&lean(dir.path()));
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");
    // Same type, wrong recursive computation. This catches erasing an index
    // or replacing the recursive call by the un-applied IH.
    let false_source = source.replace("height sample = 2", "height sample = 1");
    std::fs::write(dir.path().join("Main.lean"), false_source).expect("false twin");
    assert!(!lean(dir.path()).status.success());
    for verb in ["check", "run"] {
        assert!(
            !clean(dir.path(), verb).status.success(),
            "{verb} accepted false value"
        );
    }

    let invalid = source.replace("height (children true)", "height (Tree.node children)");
    std::fs::write(dir.path().join("Main.lean"), invalid).expect("nondecreasing twin");
    assert!(!lean(dir.path()).status.success());
    for verb in ["check", "run"] {
        assert!(
            !clean(dir.path(), verb).status.success(),
            "{verb} accepted nondecreasing recursion"
        );
    }
}

#[test]
fn related_recurses_on_small_indexed_families() {
    let dir = tempfile::tempdir().expect("isolated project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"indexed_families\"\n",
    )
    .expect("package");
    let original = include_str!("../../../theories/cic_l_model/CICLModel/RawSets.lean");
    let prefix = original
        .split("\ntheorem related_refl")
        .next()
        .expect("Related prefix");
    let source = format!("{prefix}\nend RawSet\nend CICL.Model\ndef answer : Nat := 7\n");
    std::fs::write(dir.path().join("Main.lean"), &source).expect("unchanged Related definition");
    passed(&lean(dir.path()));
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");

    let invalid = source
        .replace(".node _ left,", ".node index left,")
        .replace("Related (left i)", "Related (.node index left)");
    std::fs::write(dir.path().join("Main.lean"), invalid).expect("nondecreasing Related");
    assert!(!lean(dir.path()).status.success());
    for verb in ["check", "run"] {
        assert!(
            !clean(dir.path(), verb).status.success(),
            "{verb} accepted nondecreasing Related"
        );
    }
}

#[test]
fn indexed_children_keep_a_varying_parameter_before_the_major() {
    let dir = tempfile::tempdir().expect("isolated project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"indexed_prefix\"\n",
    )
    .expect("package");
    // Both the child index and the changing prefix have type Nat. Swapping
    // their positions can remain well typed, so assert the actual values.
    let source = "prelude\nimport Init.Data.Nat.Basic\ninductive NTree where\n  | leaf\n  | node (children : Nat → NTree)\ndef accumulate (n : Nat) : NTree → Nat\n  | .leaf => n\n  | .node children => accumulate (n + 1) (children n)\ndef sample : NTree := .node (fun i => match i with | 0 => .leaf | _ + 1 => .node (fun _ => .leaf))\ntheorem zero_sample : accumulate 0 sample = 1 := rfl\ntheorem one_sample : accumulate 1 sample = 3 := rfl\ndef answer : Nat := 7\n";
    std::fs::write(dir.path().join("Main.lean"), source).expect("indexed prefix source");
    passed(&lean(dir.path()));
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");
    std::fs::write(
        dir.path().join("Main.lean"),
        source.replace("accumulate 1 sample = 3", "accumulate 1 sample = 2"),
    )
    .expect("false value");
    assert!(!lean(dir.path()).status.success());
    for verb in ["check", "run"] {
        assert!(
            !clean(dir.path(), verb).status.success(),
            "{verb} accepted wrong indexed-prefix value"
        );
    }
}
