// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Prelude headers are processed before the imports they explicitly request.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn library() -> PathBuf {
    clean_olean::pinned_lean_lib_path().expect("pinned Lean library is required")
}

fn project() -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("isolated prelude project");
    std::fs::write(
        dir.path().join("lakefile.toml"),
        "name = \"prelude_source\"\n",
    )
    .expect("package boundary");
    dir
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
    command.output().expect("production Clean CLI")
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
            std::env::join_paths([root, lib.as_path()]).expect("Lean search path"),
        )
        .args(args)
        .output()
        .expect("pinned Lean CLI")
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
fn prelude_entry_runs_with_its_explicit_init_import() {
    let dir = project();
    std::fs::write(
        dir.path().join("Main.lean"),
        "prelude\nimport Init.Prelude\ndef answer : Nat := 7\n",
    )
    .expect("prelude entry");
    passed(&lean(dir.path(), &["Main.lean"]));
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");
}

#[test]
fn prelude_header_is_not_rechecked_after_a_source_import() {
    let dir = project();
    std::fs::write(
        dir.path().join("Base.lean"),
        "prelude\nimport Init.Prelude\ndef importedAnswer : Nat := 7\n",
    )
    .expect("source dependency");
    std::fs::write(
        dir.path().join("Main.lean"),
        "prelude\nimport Base\ndef answer : Nat := importedAnswer\n",
    )
    .expect("prelude importer");
    passed(&lean(dir.path(), &["-o", "Base.olean", "Base.lean"]));
    passed(&lean(dir.path(), &["Main.lean"]));
    // Clean must exercise source composition, including the imported header.
    std::fs::remove_file(dir.path().join("Base.olean")).expect("remove oracle artifact");
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");
}

#[test]
fn prelude_does_not_gain_nat_or_numerals_from_an_implicit_init() {
    for source in [
        "prelude\ndef answer : Nat := 7\n",
        "prelude\naxiom Nat : Sort 1\ndef answer : Nat := 7\n",
    ] {
        let dir = project();
        std::fs::write(dir.path().join("Main.lean"), source).expect("refused twin");
        let oracle = lean(dir.path(), &["Main.lean"]);
        assert!(!oracle.status.success(), "pinned Lean accepted {source}");
        let oracle_message = String::from_utf8_lossy(&oracle.stdout).to_ascii_lowercase();
        // Pinned Lean reports the unavailable numeral class before the type
        // error, including for the source with no declaration of Nat.
        assert!(oracle_message.contains("ofnat"), "{oracle_message}");
        for verb in ["check", "run"] {
            let output = clean(dir.path(), verb);
            assert!(!output.status.success(), "{verb} accepted {source}");
            let message = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                message.contains("Nat")
                    || message.contains("OfNat")
                    || message.contains("unsolved metavariables"),
                "{message}"
            );
        }
    }
}

const MAX_CASES: &str = r#"prelude
import Init.Data.Nat.MinMax

def diagonal (n : Nat) : Nat := match n with
  | 0 => 0
  | n + 1 => Nat.max (n + 1) (n + 1)
theorem diagonal_self (n : Nat) : diagonal n = n := by
  cases n with
  | zero => rfl
  | succ n => exact Nat.max_eq_left (Nat.le_refl _)
def answer : Nat := 7
"#;

#[test]
fn cases_then_exact_uses_the_genuine_imported_max_in_both_verbs() {
    let dir = project();
    std::fs::write(dir.path().join("Main.lean"), MAX_CASES).expect("max/cases regression");
    passed(&lean(dir.path(), &["Main.lean"]));
    passed(&clean(dir.path(), "check"));
    let output = clean(dir.path(), "run");
    passed(&output);
    assert_eq!(output.stdout, b"7\n");

    let wrong = MAX_CASES.replace("diagonal n = n :=", "diagonal n = n + 1 :=");
    assert_ne!(
        wrong, MAX_CASES,
        "negative control must change the statement"
    );
    std::fs::write(dir.path().join("Main.lean"), wrong).expect("false successor twin");
    let oracle = lean(dir.path(), &["Main.lean"]);
    assert!(
        !oracle.status.success(),
        "pinned Lean accepted the false successor twin"
    );
    for verb in ["check", "run"] {
        let output = clean(dir.path(), verb);
        assert!(
            !output.status.success(),
            "{verb} accepted the false successor twin"
        );
    }
}

#[test]
fn ordinary_source_cannot_shadow_implicit_init_inside_a_prelude_importer() {
    let dir = project();
    std::fs::write(dir.path().join("Base.lean"), "axiom Nat : Sort 1\n")
        .expect("ordinary module that Lean refuses");
    std::fs::write(
        dir.path().join("Main.lean"),
        "prelude\nimport Base\ndef answer : Sort 1 := Nat\n",
    )
    .expect("prelude importer");
    let oracle = lean(dir.path(), &["Base.lean"]);
    assert!(
        !oracle.status.success(),
        "pinned Lean accepted duplicate Nat"
    );
    let message = String::from_utf8_lossy(&oracle.stdout);
    assert!(
        message.contains("Nat") && message.contains("already"),
        "{message}"
    );
    for verb in ["check", "run"] {
        let output = clean(dir.path(), verb);
        assert!(
            !output.status.success(),
            "{verb} accepted the malformed dependency"
        );
        let message = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let lower = message.to_ascii_lowercase();
        assert!(
            lower.contains("nat") && (lower.contains("duplicate") || lower.contains("already")),
            "{message}"
        );
    }
}

#[test]
fn actual_level_source_elaborates_in_both_verbs_and_refuses_false_imax() {
    const LEVEL: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../theories/cic_l/CICL/Level.lean"
    ));
    // Cover the committed prelude and the original ordinary-module reproduction.
    // Only the temporary fixture loses its header; all theorem bodies are identical.
    let ordinary = LEVEL.replacen("\nprelude\n", "\n", 1);
    assert_ne!(
        ordinary, LEVEL,
        "the ordinary fixture must remove the header"
    );
    for level in [LEVEL, ordinary.as_str()] {
        let dir = project();
        let source = format!("{level}\ndef answer : Nat := 7\n");
        std::fs::write(dir.path().join("Main.lean"), &source)
            .expect("Level fixture followed by a runtime sentinel");
        passed(&lean(dir.path(), &["Main.lean"]));
        passed(&clean(dir.path(), "check"));
        let output = clean(dir.path(), "run");
        passed(&output);
        assert_eq!(output.stdout, b"7\n");

        let wrong = source.replace(
            "theorem imax_self (u : Level) : SemEq (.imax u u) u := by",
            "theorem imax_self (u : Level) : SemEq (.imax u u) (.succ u) := by",
        );
        assert_ne!(wrong, source, "the negative control must change imax_self");
        std::fs::write(dir.path().join("Main.lean"), wrong).expect("false imax fixture");
        assert!(!lean(dir.path(), &["Main.lean"]).status.success());
        for verb in ["check", "run"] {
            let output = clean(dir.path(), verb);
            assert!(!output.status.success(), "{verb} accepted false imax_self");
        }
    }
}

#[test]
fn simp_iota_reduces_a_definitionally_constructor_major() {
    // Imported casesOn is a definition; the builtin helper is a recursor.
    // Both must inspect the WHNF major, also under simp's lambda context.
    for header in ["prelude\nimport Init.Data.Nat.MinMax\n", ""] {
        let dir = project();
        let source = format!("{header}def choose (a b : Nat) : Nat := match b with | 0 => 0 | n + 1 => Nat.max a (n + 1)\ntheorem choose_succ (a b n : Nat) (positive : b = n + 1) : choose a b = Nat.max a b := by\n  simp only [choose, positive]\ntheorem choose_lambda (a b n : Nat) (positive : b = n + 1) : (fun z : Nat => choose (a + z) b) = (fun z : Nat => Nat.max (a + z) b) := by\n  simp only [choose, positive]\ndef answer : Nat := 7\n");
        std::fs::write(dir.path().join("Main.lean"), &source).expect("defined major");
        passed(&lean(dir.path(), &["Main.lean"]));
        passed(&clean(dir.path(), "check"));
        let output = clean(dir.path(), "run");
        passed(&output);
        assert_eq!(output.stdout, b"7\n");

        let false_source = source.replace("= Nat.max a b := by", "= 0 := by");
        std::fs::write(dir.path().join("Main.lean"), false_source).expect("false twin");
        assert!(!lean(dir.path(), &["Main.lean"]).status.success());
        for verb in ["check", "run"] {
            assert!(
                !clean(dir.path(), verb).status.success(),
                "{verb} accepted false twin"
            );
        }
    }
}
