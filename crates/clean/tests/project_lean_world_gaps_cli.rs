// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KNOWN GAPS next to decision R111 (G72): `clean check` accepts what pinned
//! Lean refuses, in the world R111 selects as in every other. Each test pins
//! today's false acceptance so it fails loudly the day the gap closes; the
//! fix then flips the assertion to the refusal Lean gives and closes the
//! ledger entry the test names. Lean's verdicts were measured 2026-10-22
//! with the pinned toolchains (`lean` of each, no `LEAN_PATH`). A closed pin
//! stays here, flipped to Lean's refusal, so the gap cannot reopen silently.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// `clean check <file>` from `dir`, with every search-path variable removed.
fn check_in(dir: &Path, file: &str) -> (Output, String) {
    let output = Command::new(PathBuf::from(env!("CARGO_BIN_EXE_clean")))
        .args(["check", file])
        .current_dir(dir)
        .env_remove("LEAN_PATH")
        .env_remove("MATHLIB_PATH")
        .env_remove("LEAN_PACKAGES_PATH")
        .output()
        .expect("run clean check");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (output, text)
}

/// Write `files` (relative path, contents) under a fresh directory.
fn tree(files: &[(&str, &str)]) -> tempfile::TempDir {
    let root = tempfile::tempdir().expect("tempdir");
    for (rel, contents) in files {
        let path = root.path().join(rel);
        fs::create_dir_all(path.parent().expect("parent")).expect("dirs");
        fs::write(path, contents).expect("file");
    }
    root
}

/// Assert the KNOWN GAP still holds: Clean accepts `what`, which pinned Lean
/// refuses with `lean_says`.
fn assert_known_false_acceptance(
    what: &str,
    lean_says: &str,
    entry: &str,
    checked: &(Output, String),
) {
    assert!(
        checked.0.status.success(),
        "KNOWN GAP ({entry}) CLOSED? Clean no longer accepts {what}, which pinned Lean refuses \
         ({lean_says}). Flip this pin to that refusal and close {entry}:\n{}",
        checked.1
    );
}

/// CLOSED (R111 "Not covered", ledger (155), closed by 6e12a7791): Clean's
/// builtin prelude used to sit under every file, so `Array.data`, Lean
/// 4.8.0's name for an array's list, which Clean's prelude declares, resolved
/// over `import Init.Prelude` in the checkout's v4.30.0-rc2 world. A source
/// graph that reaches an artifact import now starts from the selected world's
/// genuine Init instead, so Clean refuses it as pinned v4.30.0-rc2 does
/// ("Unknown constant `Array.data`", re-measured 2026-11-14 with no
/// `LEAN_PATH`; pinned v4.8.0 accepts the same file).
#[test]
fn test_import_init_prelude_does_not_serve_clean_prelude_declarations() {
    let source = "import Init.Prelude\n\ndef usesArrayData := @Array.data\n";
    let project = tree(&[("proj/Probe.lean", source)]);
    let (output, text) = check_in(&project.path().join("proj"), "Probe.lean");
    assert!(
        !output.status.success(),
        "REGRESSION (R111, ledger (155)): Clean's builtin prelude reached a file importing \
         Init.Prelude again: it accepts Array.data, which pinned v4.30.0-rc2 refuses \
         (Unknown constant `Array.data`):\n{text}"
    );
    assert!(
        text.contains("Unknown identifier: Array.data"),
        "the refusal must be the unknown name pinned Lean reports, not another error:\n{text}"
    );
}

/// The residue of the item above (R111 "Not covered", ledger (155)): a file
/// with no imports is still checked against Clean's builtin prelude, so
/// `@Array.data` is accepted where pinned v4.30.0-rc2, which imports Init
/// implicitly, refuses it ("Unknown constant `Array.data`", measured
/// 2026-11-14 with no `LEAN_PATH`).
#[test]
fn test_known_gap_clean_prelude_declarations_reach_import_free_files() {
    let source = "def usesArrayData := @Array.data\n";
    let project = tree(&[("proj/NoImport.lean", source)]);
    assert_known_false_acceptance(
        "Array.data in an import-free file of the checkout's world",
        "Unknown constant `Array.data`",
        "R111 Not covered, ledger (155)",
        &check_in(&project.path().join("proj"), "NoImport.lean"),
    );
}

/// What `clean check` elaborates as "the project's own source"
/// (`resolve_intra_project_import`: the nearest Lake root, its
/// `.lake/packages`, then every ancestor directory of the importing file) is
/// wider than what Lean resolves an `import` to (ledger (176)).
#[test]
fn test_known_gap_project_source_is_wider_than_leans() {
    // A project file named like a Lean module shadows it: Lean imports its
    // own `Init.Prelude` ("unknown identifier 'ShadowLocal.x'").
    let project = tree(&[
        ("proj/Init/Prelude.lean", "def ShadowLocal.x : Nat := 1\n"),
        (
            "proj/Main.lean",
            "import Init.Prelude\n\ndef Main.m : Nat := ShadowLocal.x\n",
        ),
    ]);
    assert_known_false_acceptance(
        "a project file shadowing Init.Prelude",
        "unknown identifier 'ShadowLocal.x'",
        "ledger (176)",
        &check_in(&project.path().join("proj"), "Main.lean"),
    );
    // A source file in a directory above the project is not the project's:
    // Lean 4.8.0 says "unknown package 'Mathbot'". The walk climbs the path
    // it is given, so the entry is named by its absolute path here.
    let layout = tree(&[
        ("outer/Mathbot/X.lean", "def Mathbot.X.v : Nat := 2\n"),
        (
            "outer/proj/lakefile.toml",
            "name = \"foo\"\n\n[[lean_lib]]\nname = \"Foo\"\n",
        ),
        (
            "outer/proj/Foo.lean",
            "import Mathbot.X\n\ntheorem Foo.t : Mathbot.X.v = 2 := rfl\n",
        ),
    ]);
    assert_known_false_acceptance(
        "an import resolved to a file above the project",
        "unknown package 'Mathbot'",
        "ledger (176)",
        &check_in(
            &layout.path().join("outer/proj"),
            &layout
                .path()
                .join("outer/proj/Foo.lean")
                .display()
                .to_string(),
        ),
    );
}
