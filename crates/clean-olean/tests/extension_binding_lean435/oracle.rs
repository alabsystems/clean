// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_olean::{ClosedRecheckOptions, ImportedConeGate};
use std::collections::BTreeSet;
use std::process::Command;

const SOURCE: &str = include_str!("../fixtures/lean/v4.35.0/extension_bindings/Bindings435.lean");
const THEOREMS: [&str; 10] = [
    "divZero",
    "modZero",
    "divLarge",
    "modLarge",
    "divMax",
    "modMax",
    "charSurrogate",
    "charUpper",
    "charBeyond",
    "stringOrder",
];

fn binary() -> std::path::PathBuf {
    clean_olean::installed_lean_lib_path("leanprover/lean4:v4.35.0")
        .expect("the exact official 4.35 SDK is required")
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("bin/lean")
}

pub(super) fn fixture() -> (tempfile::TempDir, Environment) {
    let dir = tempfile::tempdir().unwrap();
    std::fs::write(dir.path().join("Bindings435.lean"), SOURCE).unwrap();
    let output = Command::new(binary())
        .current_dir(dir.path())
        .env_remove("LEAN_SRC_PATH")
        .env("LEAN_PATH", dir.path())
        .args(["--root", ".", "-o", "Bindings435.olean", "Bindings435.lean"])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    eprintln!(
        "LEAN435_ORACLE positive {}\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success());
    for theorem in THEOREMS {
        assert!(
            stdout.lines().any(
                |line| line == format!("'Bindings435.{theorem}' does not depend on any axioms")
            ),
            "missing actual empty axiom disclosure for {theorem}: {stdout}"
        );
    }
    let mut env = load();
    clean_olean::load_module_with_deps(
        &mut env,
        "Bindings435",
        &[
            dir.path().to_path_buf(),
            clean_olean::installed_lean_lib_path("leanprover/lean4:v4.35.0").unwrap(),
        ],
    )
    .unwrap();
    (dir, env)
}

#[test]
fn genuine_435_official_rfl_fixture_passes_closed_import_replay() {
    let (_dir, env) = fixture();
    let roots = THEOREMS
        .iter()
        .map(|key| n(&format!("Bindings435.{key}")))
        .chain([
            n("Bindings435.divAlias"),
            n("Bindings435.modAlias"),
            n("Bindings435.charAlias"),
        ])
        .collect::<BTreeSet<_>>();
    let run = clean_olean::recheck_closed(&env, &roots, &ClosedRecheckOptions::default());
    eprintln!("LEAN435_SOURCE_CLOSED {:?}", run.report);
    assert!(run.report.passed(), "{}", run.report.verdict_sentence());
    assert!(run.report.axioms_admitted.is_empty());
    let mut base = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut base, LeanWorld::Lean435.tag()).unwrap();
    let verdict = ImportedConeGate::new(&base).check(&env, &roots);
    assert!(verdict.passed(false), "{}", verdict.refusal_summary(false));
}

#[test]
fn genuine_435_official_kernel_rejects_wrong_closed_answers() {
    let dir = tempfile::tempdir().unwrap();
    for (key, proposition) in [
        ("div", "Nat.div 1267650600228229401496703205395 3 = 422550200076076467165567735132"),
        ("mod", "Nat.mod 1267650600228229401496703205395 3 = 1"),
        ("divZero", "Nat.div 37 0 = 37"),
        ("modZero", "Nat.mod 37 0 = 0"),
        ("charSurrogate", "Char.toNat (Char.ofNat 0xd800) = 0xd800"),
        ("charBeyond", "Char.toNat (Char.ofNat 0x110000) = 0x110000"),
        ("stringOrder", "String.ofList (List.cons (Char.ofNat 98) (List.cons (Char.ofNat 97) List.nil)) = \"ab\""),
    ] {
        let source = format!("prelude\nimport Init.Data.UInt.Basic\nexample : {proposition} := rfl\n");
        let file = format!("Wrong{key}.lean");
        std::fs::write(dir.path().join(&file), source).unwrap();
        let output = Command::new(binary()).current_dir(dir.path())
            .env_remove("LEAN_SRC_PATH").env("LEAN_PATH", dir.path()).arg(&file).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        eprintln!("LEAN435_ORACLE negative {key} {}\n{stdout}\n{}", output.status, String::from_utf8_lossy(&output.stderr));
        assert!(!output.status.success(), "wrong official answer accepted: {key}");
        assert!(stdout.contains("type mismatch") || stdout.contains("Type mismatch"),
            "the negative must reach a kernel type mismatch: {key}: {stdout}");
    }
}
