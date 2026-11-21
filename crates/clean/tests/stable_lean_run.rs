// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The installed Lean 4.36.0 artifact-only runtime and stdin controls.

#![cfg(unix)]

use std::io::Write;
use std::path::Path;
use std::process::{Command, Output, Stdio};

fn stable_lean(root: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean"));
    command
        .arg("lean")
        .env("CLEAN_LEAN_VERSION", "v4.36.0")
        .env("LEAN_PATH", root)
        .current_dir(root);
    command
}

fn assert_output(output: &Output, code: i32, stdout: &[u8]) {
    assert_eq!(
        output.status.code(),
        Some(code),
        "stdout={:?}, stderr={:?}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, stdout);
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_olean_output_is_importable_by_lean() {
    let dir = tempfile::tempdir().expect("temporary project");
    let root = dir.path();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.36.0/proof-export");
    for file in ["Seal.lean", "Consumer.lean", "Hidden.lean", "Private.lean"] {
        std::fs::copy(fixture.join(file), root.join(file)).expect("copy oracle source");
    }
    let clean_output = || {
        stable_lean(root)
            .args(["-o", "Seal.olean", "Seal.lean"])
            .output()
            .expect("emit native module")
    };
    assert_output(&clean_output(), 0, b"");

    let path_names = [
        "Seal.olean",
        "Seal.olean.server",
        "Seal.olean.private",
        "Seal.ir.sig",
        "Seal.ir",
    ];
    let read_parts = || path_names.map(|name| std::fs::read(root.join(name)).expect(name));
    let parts = read_parts();
    let official = std::env::var_os("CLEAN_LEAN436_BIN").expect("path to official Lean 4.36.0");
    let import = |file| {
        Command::new(&official)
            .arg(file)
            .env("LEAN_PATH", root)
            .current_dir(root)
            .output()
            .expect("import Clean's module in Lean")
    };
    assert_output(
        &import("Consumer.lean"),
        0,
        b"'Seal.exportedProof' does not depend on any axioms\n'Seal.usesGap' depends on axioms: [gap]\n",
    );
    assert_output(&import("Private.lean"), 0, b"Seal.hidden : True\n");
    let hidden = import("Hidden.lean");
    assert_eq!(hidden.status.code(), Some(1));
    let message = String::from_utf8_lossy(&hidden.stdout);
    assert!(
        message.contains("Unknown identifier `Seal.hidden`"),
        "{message}"
    );

    std::fs::write(
        root.join("CleanConsumer.lean"),
        "module\nimport Seal\ntheorem consumes : True := Seal.exportedProof\n",
    )
    .expect("write Clean import control");
    let clean_import = stable_lean(root)
        .arg("CleanConsumer.lean")
        .output()
        .expect("read the generated module through Clean's artifact importer");
    assert_output(&clean_import, 0, b"");

    std::fs::write(
        root.join("Seal.lean"),
        "module\npublic theorem bad : False := True.intro\n",
    )
    .expect("write failing source");
    assert_eq!(clean_output().status.code(), Some(1));
    assert_eq!(
        read_parts(),
        parts,
        "failed elaboration replaced existing artifacts"
    );
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_olean_exports_proofs_over_imported_axioms() {
    check_axiom_consumer("");
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_prelude_olean_exports_proofs_after_its_imports() {
    check_axiom_consumer("prelude\n");
}

fn check_axiom_consumer(prelude: &str) {
    let dir = tempfile::tempdir().expect("temporary project");
    let root = dir.path();
    let sdk = std::env::var_os("CLEAN_LEAN436_BIN").expect("official Lean 4.36.0");
    let official = |args: &[&str]| {
        Command::new(&sdk)
            .args(args)
            .env("LEAN_PATH", root)
            .current_dir(root)
            .output()
            .expect("run official Lean")
    };
    std::fs::write(
        root.join("Foundation.lean"),
        "module\nprelude\npublic axiom Assumption.P : Prop\npublic axiom Assumption.w : Assumption.P\npublic theorem Assumption.t : Assumption.P := Assumption.w\n",
    )
    .unwrap();
    std::fs::write(
        root.join("UsesFoundation.lean"),
        format!("module\n{prelude}public import Foundation\npublic theorem direct : Assumption.P := Assumption.w\npublic theorem indirect : Assumption.P := Assumption.t\n"),
    )
    .unwrap();
    std::fs::write(
        root.join("InspectFoundation.lean"),
        "import UsesFoundation\n#print axioms direct\n#print axioms indirect\n",
    )
    .unwrap();
    assert_output(
        &official(&["-o", "Foundation.olean", "Foundation.lean"]),
        0,
        b"",
    );
    assert_output(
        &official(&["-o", "UsesFoundation.olean", "UsesFoundation.lean"]),
        0,
        b"",
    );
    std::fs::write(
        root.join("InspectHeader.lean"),
        r#"import Lean
open Lean
#eval do
  let parts ← readModuleDataParts #["UsesFoundation.olean"]
  for (m, _) in parts do
    for i in m.imports do
      IO.println s!"{i.module} {i.importAll} {i.isExported} {i.isMeta}"
"#,
    )
    .unwrap();
    let expected_imports: &[u8] = if prelude.is_empty() {
        b"Init false true false\nInit false true true\nFoundation false true false\n"
    } else {
        b"Foundation false true false\n"
    };
    let expected = b"'direct' depends on axioms: [Assumption.P, Assumption.w]\n'indirect' depends on axioms: [Assumption.P, Assumption.w]\n";
    let check_readers = || {
        assert_output(&official(&["InspectFoundation.lean"]), 0, expected);
        assert_output(&official(&["InspectHeader.lean"]), 0, expected_imports);
    };
    check_readers();
    for extension in ["olean", "olean.server", "olean.private", "ir", "ir.sig"] {
        std::fs::remove_file(root.join(format!("UsesFoundation.{extension}"))).unwrap();
    }
    assert_output(
        &stable_lean(root)
            .args(["-o", "UsesFoundation.olean", "UsesFoundation.lean"])
            .output()
            .expect("emit Clean module using official imports"),
        0,
        b"",
    );
    check_readers();
}

fn artifact_fixture(include_ir: bool) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("temporary project");
    let root = dir.path();
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.36.0/module-ir");
    for file in ["App.lean", "MetaUse.lean"] {
        std::fs::copy(fixture.join(file), root.join(file)).expect("consumer source");
    }
    std::fs::create_dir(root.join("StableFixture")).expect("artifact root");
    for part in ["olean", "olean.server", "olean.private", "ir.sig", "ir"] {
        if !include_ir && part.starts_with("ir") {
            continue;
        }
        let relative = format!("StableFixture/Defs.{part}");
        std::fs::copy(fixture.join(&relative), root.join(&relative)).expect("official Lean part");
    }
    dir
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and a host C compiler"]
fn stable_run_replays_artifacts_and_stdin() {
    let dir = artifact_fixture(true);
    let root = dir.path();

    for form in ["--run", "-r"] {
        let output = stable_lean(root)
            .args([form, "App.lean", "--application-argument"])
            .output()
            .expect("run artifact-only consumer");
        assert_output(&output, 17, b"41\n");
    }

    for args in [
        &["--stdin", "--run", "App.lean"][..],
        &["--stdin", "-r"][..],
    ] {
        let mut child = stable_lean(root)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run stable stdin consumer");
        child
            .stdin
            .take()
            .expect("stdin pipe")
            .write_all(b"def main : IO UInt32 := do\n  IO.println 23\n  pure 29\n")
            .expect("send stdin source");
        let output = child.wait_with_output().expect("read the stable run");
        assert_output(&output, 29, b"23\n");
    }
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and a host C compiler"]
fn stable_stdin_runs_with_implicit_init_and_preserves_flag_arguments() {
    let dir = tempfile::tempdir().expect("temporary stdin project");
    let root = dir.path();
    std::fs::write(root.join("App.lean"), "def main : IO UInt32 := pure 73\n")
        .expect("write conflicting source file");

    let mut unnamed = stable_lean(root)
        .args(["--stdin", "--run"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run stable stdin with implicit Init");
    unnamed
        .stdin
        .take()
        .expect("stdin pipe")
        .write_all(b"def main : IO Unit := IO.println \"stable-stdin-marker\"\n")
        .expect("send stdin source");
    let output = unnamed.wait_with_output().expect("read the stable run");
    assert_output(&output, 0, b"stable-stdin-marker\n");

    let mut child = stable_lean(root)
        .args(["--stdin", "--run", "App.lean", "--json", "-q"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run stable stdin with program arguments");
    child
        .stdin
        .take()
        .expect("stdin pipe")
        .write_all(b"def main (args : List String) : IO UInt32 := pure args.length.toUInt32\n")
        .expect("send stdin source");
    let output = child.wait_with_output().expect("read the stable run");
    assert_output(&output, 2, b"");
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_eval_uses_captured_ir_for_imported_nat_calls() {
    let dir = artifact_fixture(true);
    let root = dir.path();
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.36.0/compiled-nat");
    std::fs::copy(
        fixture.join("CapturedNat.lean"),
        root.join("CapturedNat.lean"),
    )
    .expect("oracle theorem and evaluation");
    let run = || {
        stable_lean(root)
            .arg("CapturedNat.lean")
            .output()
            .expect("check theorem and evaluate imported Nat calls")
    };
    assert_output(&run(), 0, b"41\n");
    let large =
        "module\nimport all StableFixture.Defs\n#eval StableFixture.twice 18446744073709551615\n";
    std::fs::write(root.join("Large.lean"), large).expect("heap Nat control");
    let output = stable_lean(root)
        .arg("Large.lean")
        .output()
        .expect("evaluate imported Nat call over a heap result");
    assert_output(&output, 0, b"36893488147419103230\n");
    for file in ["StableFixture/Defs.ir.sig", "StableFixture/Defs.ir"] {
        std::fs::copy(fixture.join("replacement").join(file), root.join(file))
            .expect("replace only interpreter IR");
    }
    assert_output(&run(), 0, b"42\n");

    std::fs::remove_file(root.join("StableFixture/Defs.ir")).expect("remove captured body");
    let output = run();
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8_lossy(&output.stdout);
    assert!(message.contains("missing captured .ir"), "{message}");
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_eval_respects_imported_nat_phases() {
    let dir = tempfile::tempdir().expect("temporary project");
    let root = dir.path();
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.36.0/meta-nat");
    for file in [
        "MetaMark.olean",
        "MetaMark.olean.server",
        "MetaMark.olean.private",
    ] {
        std::fs::copy(fixture.join(file), root.join(file)).expect("official declaration part");
    }
    let run = |name| {
        std::fs::write(
            root.join("Main.lean"),
            format!("module\nimport MetaMark\n#eval {name} 7\n"),
        )
        .expect("write phase control");
        stable_lean(root)
            .arg("Main.lean")
            .output()
            .expect("evaluate without IR companions")
    };
    assert_output(&run("markedNat"), 0, b"20\n");
    let output = run("ordinaryNat");
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8_lossy(&output.stdout);
    assert!(
        message.contains("`ordinaryNat` is not accessible here")
            && message.contains("`public meta import MetaMark`"),
        "{message}"
    );
}

fn default_artifact_project(official: &Path) -> tempfile::TempDir {
    let fixture =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/olean/v4.36.0/module-ir");
    let producer = tempfile::tempdir().expect("temporary Lake producer");
    let source = "StableFixture/Defs.lean";
    std::fs::create_dir(producer.path().join("StableFixture")).unwrap();
    std::fs::copy(fixture.join(source), producer.path().join(source)).unwrap();
    std::fs::copy(
        fixture.join("lean-toolchain"),
        producer.path().join("lean-toolchain"),
    )
    .unwrap();
    std::fs::write(
        producer.path().join("lakefile.toml"),
        "name = \"stable_fixture\"\n\n[leanOptions]\nexperimental.module = true\n\n[[lean_lib]]\nname = \"StableFixture\"\n",
    )
    .unwrap();
    let built = Command::new(official.with_file_name("lake"))
        .args([
            "build",
            "+StableFixture.Defs:olean",
            "+StableFixture.Defs:ir",
        ])
        .env_remove("LEAN_PATH")
        .current_dir(producer.path())
        .output()
        .expect("build the producer with stable Lake and its default compiler settings");
    assert!(built.status.success(), "Lake failed: {built:?}");

    let consumer = tempfile::tempdir().expect("temporary artifact-only consumer");
    let root = consumer.path();
    std::fs::create_dir(root.join("StableFixture")).unwrap();
    let built_parts = producer.path().join(".lake/build/lib/lean");
    for extension in ["olean", "olean.server", "olean.private", "ir", "ir.sig"] {
        let name = format!("StableFixture/Defs.{extension}");
        std::fs::copy(built_parts.join(&name), root.join(&name)).expect("official producer part");
    }
    for name in ["lean-toolchain", "Integrated.lean"] {
        std::fs::copy(fixture.join(name), root.join(name)).expect("project source and toolchain");
    }
    consumer
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_checks_the_integrated_source_without_producer_source() {
    let official = std::env::var_os("CLEAN_LEAN436_BIN").expect("official Lean executable");
    let consumer = default_artifact_project(Path::new(&official));
    let root = consumer.path();
    let reference = Command::new(&official)
        .arg("Integrated.lean")
        .env("LEAN_PATH", root)
        .current_dir(root)
        .output()
        .expect("check the artifact-only source with Lean");
    assert_output(&reference, 0, b"");
    let checked = stable_lean(root)
        .env_remove("CLEAN_LEAN_VERSION")
        .arg("Integrated.lean")
        .output()
        .expect("check the same source with the project-selected Clean frontend");
    assert_output(&checked, 0, &reference.stdout);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_exported_term_elaborator_replays_without_private_ir() {
    let dir = artifact_fixture(false);
    let root = dir.path();
    let output = stable_lean(root)
        .arg("MetaUse.lean")
        .output()
        .expect("check theorem and evaluate imported syntax");
    assert_output(&output, 0, b"74\n");

    let wrong = "module\nimport StableFixture.Defs\ntheorem wrong : (stable_witness% 17 : Nat) = 74 := rfl\n";
    std::fs::write(root.join("Wrong.lean"), wrong).expect("negative proof control");
    let output = stable_lean(root)
        .arg("Wrong.lean")
        .output()
        .expect("check the wrong theorem");
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8_lossy(&output.stdout);
    assert!(
        message.contains("Wrong.lean:3:51: error: Type mismatch\n  rfl\nhas type\n")
            && message.contains("but is expected to have type\n  73 = 74"),
        "{message}"
    );
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_imported_syntax_follows_module_visibility() {
    let dir = artifact_fixture(true);
    let root = dir.path();
    let sdk = std::env::var_os("CLEAN_LEAN436_BIN").expect("official Lean 4.36.0");
    let official = |args: &[&str]| {
        Command::new(&sdk)
            .args(args)
            .env("LEAN_PATH", root)
            .current_dir(root)
            .output()
            .expect("run official Lean")
    };

    for (name, imports) in [
        ("Public", "public import StableFixture.Defs"),
        ("Private", "import StableFixture.Defs"),
        ("Outer", "public import StableFixture.Private"),
    ] {
        let source = format!("StableFixture/{name}.lean");
        let object = format!("StableFixture/{name}.olean");
        std::fs::write(root.join(&source), format!("module\n{imports}\n")).unwrap();
        assert_output(&official(&["-o", &object, &source]), 0, b"");
        std::fs::remove_file(root.join(source)).expect("consume only the compiled re-export");
    }

    // Without the exported prefix, Lean parses the same spelling as the local
    // identifier followed by ordinary remainder. Both paths must elaborate.
    for (imports, witness, value) in [
        ("import StableFixture.Public", 73, &b"74\n"[..]),
        ("import StableFixture.Private", 2, &b"1\n"[..]),
        ("import all StableFixture.Private", 73, &b"74\n"[..]),
        ("import all StableFixture.Outer", 2, &b"1\n"[..]),
    ] {
        std::fs::write(
            root.join("Use.lean"),
            format!("module\n{imports}\ndef stable_witness : Nat := 19\ntheorem checked : (stable_witness% 17 : Nat) = {witness} := rfl\n#eval (stable_witness% 18 : Nat)\n"),
        )
        .unwrap();
        assert_output(&official(&["Use.lean"]), 0, value);
        let actual = stable_lean(root).arg("Use.lean").output().unwrap();
        assert_output(&actual, 0, value);
    }
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and a host C compiler"]
fn stable_native_run_uses_captured_ir_for_imported_nat_calls() {
    let dir = artifact_fixture(true);
    let root = dir.path();
    std::fs::write(
        root.join("Args.lean"),
        r#"module
import all StableFixture.Defs
theorem logical : StableFixture.addOffset (StableFixture.twice 20) = 41 := rfl
public def main (args : List String) : IO UInt32 := do
  IO.println (StableFixture.addOffset (StableFixture.twice args.length))
  pure 17
"#,
    )
    .expect("argument-dependent executable fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.36.0/compiled-nat/replacement");
    let run = |input| {
        stable_lean(root)
            .args(["--run", input, "alpha", "beta", "gamma"])
            .output()
            .expect("execute imported IR")
    };
    assert_output(&run("App.lean"), 17, b"41\n");
    assert_output(&run("Args.lean"), 17, b"7\n");
    for file in ["StableFixture/Defs.ir.sig", "StableFixture/Defs.ir"] {
        std::fs::copy(fixture.join(file), root.join(file)).expect("replace only interpreter IR");
    }
    assert_output(&run("App.lean"), 17, b"42\n");
    assert_output(&run("Args.lean"), 17, b"8\n");

    std::fs::remove_file(root.join("StableFixture/Defs.ir")).expect("remove captured body");
    let output = run("App.lean");
    assert_eq!(output.status.code(), Some(1));
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(message.contains("missing captured .ir"), "{message}");
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and a host C compiler"]
fn stable_imported_theorem_elaborator_and_compiled_function_run_together() {
    let lean = std::env::var_os("CLEAN_LEAN436_BIN").expect("path to official Lean 4.36.0");
    let consumer = default_artifact_project(Path::new(&lean));
    let root = consumer.path();
    let expected = Command::new(lean)
        .args(["--run", "Integrated.lean"])
        .env("LEAN_PATH", root)
        .current_dir(root)
        .output()
        .expect("execute the artifact-only consumer with Lean");
    assert_output(&expected, 17, b"147\n");
    for _ in 0..2 {
        let actual = stable_lean(root)
            .env_remove("CLEAN_LEAN_VERSION")
            .args(["--run", "Integrated.lean"])
            .output()
            .expect("execute the same consumer with Clean");
        assert_output(&actual, 17, &expected.stdout);
    }
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK, CLEAN_LEAN436_BIN and a host C compiler"]
fn stable_project_uses_the_local_nat_display_instance() {
    let official = std::env::var_os("CLEAN_LEAN436_BIN").expect("official Lean executable");
    let consumer = default_artifact_project(Path::new(&official));
    let root = consumer.path();
    let path = root.join("Integrated.lean");
    let original = std::fs::read_to_string(&path).unwrap();
    let (theorems, main) = original.split_once("public def main").unwrap();
    let instance = r#"local instance (priority := high) : ToString Nat where
  toString _ := "custom instance""#;
    std::fs::write(
        path,
        format!("{theorems}{instance}\n\npublic def main{main}"),
    )
    .unwrap();
    let expected = Command::new(&official)
        .args(["--run", "Integrated.lean"])
        .env("LEAN_PATH", root)
        .current_dir(root)
        .output()
        .expect("run Lean with the local instance");
    assert_output(&expected, 17, b"custom instance\n");
    let actual = stable_lean(root)
        .env_remove("CLEAN_LEAN_VERSION")
        .args(["--run", "Integrated.lean"])
        .output()
        .expect("run Clean with the same local instance");
    assert_output(&actual, 17, &expected.stdout);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_stateful_io_main_matches_the_official_runner() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let official = std::env::var_os("CLEAN_LEAN436_BIN").unwrap();
    std::fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n").unwrap();
    let cases: &[(&str, &[&str], i32, &[u8])] = &[
        ("def main : IO UInt32 := fun w => EST.Out.ok 23 w", &[], 23, b""),
        ("def main (xs : List String) : IO UInt32 := fun w => EST.Out.ok (UInt32.ofNat xs.length) w", &["a","b","c"], 3, b""),
        ("def main : IO Unit := fun w => EST.Out.ok () w", &[], 0, b""),
        ("def main : IO UInt32 := fun w => EST.Out.error (IO.userError \"world error\") w", &[], 1, b"uncaught exception: world error\n"),
        (r#"def main : IO Unit := fun w => EST.Out.error (IO.userError "ü\x00tail") w"#, &[], 1, "uncaught exception: ü\n".as_bytes()),
        (r#"@[noinline] def raiseOther (n : UInt32) : IO Unit :=
  fun w => EST.Out.error (IO.Error.otherError n "Structured") w
def main (xs : List String) : IO Unit := raiseOther (UInt32.ofNat xs.length)"#, &["a", "b", "c"], 1, b"uncaught exception: structured (error code: 3)\n"),
        (r#"@[noinline] def denied (n : UInt32) : IO Unit :=
  fun w => EST.Out.error (IO.Error.permissionDenied (.some "Remote") n "Denied") w
def main : IO Unit := denied (UInt32.ofNat 13)"#, &[], 1, b"uncaught exception: denied (error code: 13)\n  file: Remote\n"),
        (r#"@[noinline] def denied (n : UInt32) : IO Unit :=
  fun w => EST.Out.error (IO.Error.permissionDenied none n "Ünicode") w
def main : IO Unit := denied (UInt32.ofNat 4294967295)"#, &[], 1, "uncaught exception: Ünicode (error code: 4294967295)\n".as_bytes()),
        (r#"@[noinline] def raiseOther (n : UInt32) : IO Unit :=
  fun w => EST.Out.error (IO.Error.otherError n "Odd\x00tail") w
def main : IO Unit := raiseOther (UInt32.ofNat 5)"#, &[], 1, b"uncaught exception: odd\n"),
        ("@[noinline] def token (s : String) : Void String := Void.mk s\n@[noinline] def action : EST String String UInt32 := fun w => .ok 17 w\ndef main : IO UInt32 := do\n  match action (token \"owned\") with\n  | .ok n _ => pure n\n  | .error _ _ => pure 2", &[], 17, b""),
    ];
    for (source, args, code, stderr) in cases {
        std::fs::write(
            root.join("Main.lean"),
            format!("prelude\nimport Init.System.IO\n{source}\n"),
        )
        .unwrap();
        let mut lean = Command::new(&official);
        lean.current_dir(root);
        for mut command in [lean, stable_lean(root)] {
            let result = command
                .args(["--run", "Main.lean"])
                .args(*args)
                .output()
                .unwrap();
            assert_eq!(
                result.status.code(),
                Some(*code),
                "{source}: {:?}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert!(result.stdout.is_empty(), "{source}: {:?}", result.stdout);
            assert_eq!(result.stderr, *stderr, "{source}");
        }
    }
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_throw_uses_its_checked_exception_dictionary() {
    check_stable_io_cases(&[
        (
            r#"def main : IO Unit := throw (IO.userError "ordinary exception")"#,
            &[],
            1,
            b"uncaught exception: ordinary exception\n",
        ),
        (
            r#"def main : IO UInt32 := throwThe IO.Error (IO.userError "explicit exception")"#,
            &[],
            1,
            b"uncaught exception: explicit exception\n",
        ),
        (
            r#"def replacedThrow {α : Type} (_ : IO.Error) : IO α :=
  fun w => EST.Out.error (IO.userError "selected field") w

@[reducible] def selected : MonadExcept IO.Error IO :=
  @MonadExcept.mk IO.Error IO (@replacedThrow) (@MonadExceptOf.tryCatch IO.Error IO instMonadExceptOfEIO)

def main : IO Unit :=
  @MonadExcept.throw IO.Error IO selected Unit (IO.userError "discarded")"#,
            &[],
            1,
            b"uncaught exception: selected field\n",
        ),
    ]);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_lift_runs_the_method_selected_by_its_dictionary() {
    check_stable_io_cases(&[
        (
            "def main : IO UInt32 := liftM (pure 37 : BaseIO UInt32)",
            &[],
            37,
            b"",
        ),
        (
            r#"@[reducible] def chosen : MonadLiftT BaseIO IO where
  monadLift := fun _ => throw (IO.userError "selected lift")
def main : IO UInt32 := @liftM BaseIO IO chosen UInt32 (pure 37)"#,
            &[],
            1,
            b"uncaught exception: selected lift\n",
        ),
    ]);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_bind_runs_the_source_continuation_only_after_success() {
    check_stable_io_cases(&[
        ("def main : IO UInt32 := (pure 37 : IO UInt32) >>= fun n => pure n", &[], 37, b""),
        (r#"def main : IO UInt32 := (throw (IO.userError "before") : IO UInt32) >>= fun _ => throw (IO.userError "after")"#, &[], 1, b"uncaught exception: before\n"),
        (r#"def main : IO UInt32 := (pure 37 : IO UInt32) >>= fun _ => throw (IO.userError "after")"#, &[], 1, b"uncaught exception: after\n"),
        ("def acceptAction (x : IO UInt32) (f : UInt32 → IO UInt32) : IO UInt32 := x >>= f\ndef main : IO UInt32 := acceptAction (pure 37) pure", &[], 37, b""),
        (r#"def accept (x : IO UInt32) (f : UInt32 → IO UInt32) : IO UInt32 := x >>= f
def main : IO UInt32 := accept (throw (IO.userError "before")) (fun _ => throw (IO.userError "after"))"#, &[], 1, b"uncaught exception: before\n"),
        (r#"def accept (f : UInt32 → IO UInt32) (x : IO UInt32) : IO UInt32 := x >>= f
def main : IO UInt32 := accept (fun _ => throw (IO.userError "chosen")) (pure 37)"#, &[], 1, b"uncaught exception: chosen\n"),
    ]);
}

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn stable_bind_preserves_a_local_wrappers_implementation_override() {
    let program = r#"prelude
import Init.System.IO

def replacement (_ : IO UInt32) (_ : UInt32 → IO UInt32) : IO UInt32 := throw (IO.userError "actual wrapper")
@[implemented_by replacement] def accept (x : IO UInt32) (f : UInt32 → IO UInt32) : IO UInt32 := x >>= f
def main : IO UInt32 := accept (pure 37) pure"#;
    check_stable_state_override(program, b"uncaught exception: actual wrapper\n");
}

fn check_stable_state_override(program: &str, expected: &[u8]) {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    std::fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n").unwrap();
    std::fs::write(root.join("Main.lean"), program).unwrap();
    let lean = Command::new(std::env::var_os("CLEAN_LEAN436_BIN").unwrap())
        .current_dir(root)
        .args(["--run", "Main.lean"])
        .output()
        .unwrap();
    assert_eq!(lean.status.code(), Some(1));
    assert!(lean.stdout.is_empty());
    assert_eq!(lean.stderr, expected);
    let clean = stable_lean(root)
        .args(["--run", "Main.lean"])
        .output()
        .unwrap();
    assert_eq!(clean.status.code(), Some(1));
    assert!(clean.stdout.is_empty());
    if clean.stderr != lean.stderr {
        let diagnostic = String::from_utf8_lossy(&clean.stderr);
        assert!(diagnostic.contains("native-eager-io"), "{diagnostic}");
    }
}

fn check_stable_io_cases(cases: &[(&str, &[&str], i32, &[u8])]) {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let official = std::env::var_os("CLEAN_LEAN436_BIN").unwrap();
    std::fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n").unwrap();
    for (source, args, code, stderr) in cases {
        std::fs::write(
            root.join("Main.lean"),
            format!("prelude\nimport Init.System.IO\n{source}\n"),
        )
        .unwrap();
        let mut lean = Command::new(&official);
        lean.current_dir(root);
        for mut command in [lean, stable_lean(root)] {
            let result = command
                .args(["--run", "Main.lean"])
                .args(*args)
                .output()
                .unwrap();
            assert_eq!(
                result.status.code(),
                Some(*code),
                "{source}: {:?}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert!(result.stdout.is_empty(), "{source}: {:?}", result.stdout);
            assert_eq!(result.stderr, *stderr, "{source}");
        }
    }
}
