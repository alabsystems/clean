// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::process::Command;

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_compiler_checks_the_global_main_and_preserves_its_logical_value() {
    let dir = tempfile::tempdir().unwrap();
    let check = |source: &str, args: &[&str]| {
        std::fs::write(dir.path().join("Main.lean"), source).unwrap();
        Command::new(env!("CARGO_BIN_EXE_clean"))
            .env("CLEAN_LEAN_VERSION", "v4.36.0")
            .current_dir(dir.path())
            .args(["lean"])
            .args(args)
            .arg("Main.lean")
            .output()
            .unwrap()
    };
    let result = check(
        "def main : Nat := 7\nexample : main = 7 := rfl\n#check main\n",
        &[],
    );
    assert_eq!(result.status.code(), Some(1));
    let out = String::from_utf8(result.stdout).unwrap();
    assert!(out.contains("Main.lean:1:4: error: `main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`"), "{out}");
    assert_eq!(out.matches("error:").count(), 1, "{out}");
    assert!(out.contains("main : Nat"), "{out}");

    let result = check("noncomputable def main : Nat := 7\n", &["--run"]);
    assert_eq!(result.status.code(), Some(1));
    assert_eq!(result.stderr, b"(interpreter) unknown declaration 'main'\n");
    let result = check(
        "namespace Other\ndef main : Nat := 7\nend Other\ndef main : IO PUnit := pure PUnit.unit\n",
        &[],
    );
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stdout)
    );
}
