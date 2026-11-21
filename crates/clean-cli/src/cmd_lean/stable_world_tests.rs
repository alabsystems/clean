// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::process::Command;

#[test]
fn stable_source_uses_the_dialect_world_through_elaboration() {
    const CHILD: &str = "CLEAN_LEAN_STABLE_SOURCE_CHILD";
    if std::env::var_os(CHILD).is_some() {
        assert_eq!(run_inner(&["src/Probe.lean".into()]), 0);
        assert_eq!(run_inner(&["src/RequiresInit.lean".into()]), 1);
        assert_eq!(run_inner(&["src/RequiresFoundation.lean".into()]), 1);
        assert_stable_artifact_paths();
        return;
    }

    let dir = tempfile::tempdir().expect("temporary working directory");
    let root = dir.path();
    let source = root.join("src");
    std::fs::create_dir(&source).expect("source directory");
    std::fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n")
        .expect("working directory selects the stable dialect");
    std::fs::write(
        source.join("lean-toolchain"),
        "leanprover/lean4:v4.30.0-rc2\n",
    )
    .expect("the file directory names an older world");
    // Official Lean 4.36.0 accepts this bare-prelude source on stdin.
    std::fs::write(
        source.join("Probe.lean"),
        "prelude\nprivate variable (α : Type)\n",
    )
    .expect("bare source");
    std::fs::write(
        source.join("RequiresInit.lean"),
        "private variable (α : Type)\n",
    )
    .expect("ordinary source");
    std::fs::write(
        source.join("RequiresFoundation.lean"),
        "prelude\nimport SomeModule\n",
    )
    .expect("source with explicit prelude import");

    // The artifact supplies the exact release header the selector reads.
    // A bare prelude needs no Init, while the ordinary source must refuse it.
    let lib = stable_lib(root);
    std::fs::create_dir_all(lib.join("Init")).expect("toolchain identity directory");
    std::fs::write(
        lib.join("Init/Prelude.olean"),
        include_bytes!("../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean"),
    )
    .expect("tracked stable header identity");

    // A different release on a project-only search root would turn the
    // genuine missing-Init error into a mixed-world refusal if consulted.
    let ignored = root.join("ignored-artifact-root");
    std::fs::create_dir_all(ignored.join("Init")).expect("ambient artifact directory");
    let other_release =
        include_bytes!("../../../../tests/fixtures/olean/v4.30.0/closure_cache/Init.olean");
    for module in ["Init.olean", "Init/Core.olean"] {
        std::fs::write(ignored.join(module), other_release).expect("ambient fixture");
    }
    let absent = root.join("absent-search-root");
    let lean_path = std::env::join_paths([absent.as_path(), Path::new(""), &absent, &lib])
        .expect("raw LEAN_PATH");

    let output = Command::new(std::env::current_exe().expect("test executable"))
        .args([
            "--exact",
            "cmd_lean::stable_world_tests::stable_source_uses_the_dialect_world_through_elaboration",
            "--nocapture",
        ])
        .env_clear()
        .env(CHILD, "1")
        .env("ELAN_HOME", root)
        .env("LEAN_PATH", lean_path)
        .env("MATHLIB_PATH", ignored)
        .current_dir(root)
        .output()
        .expect("run isolated stable CLI regression");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");
    assert!(stderr.contains("module Init not found"), "{stderr}");
    assert!(stderr.contains("module Init.Core not found"), "{stderr}");
    assert!(!stderr.contains("ignored-artifact-root"), "{stderr}");
}

fn stable_lib(root: &Path) -> PathBuf {
    root.join("toolchains/leanprover--lean4---v4.36.0/lib/lean")
}

fn assert_stable_artifact_paths() {
    let root = PathBuf::from(std::env::var_os("ELAN_HOME").expect("test toolchain root"));
    let absent = root.join("absent-search-root");
    let lib = stable_lib(&root);
    let expected = vec![absent.clone(), PathBuf::new(), absent, lib.clone(), lib];
    let decision = clean_olean::source_world_for_file(
        Path::new("src/Probe.lean"),
        Some(clean_kernel::LeanWorld::Lean436),
    )
    .expect("exact stable world");
    let paths = deps::search_path(LeanDialect::V4_36_0, Some(&decision));
    assert_eq!(paths, expected);
    let header = clean_parser::Parser::parse_header("prelude\n").expect("bare header");
    let (_, context) = clean_elab::module_driver::module_environment_and_context_with_import_paths(
        clean_elab::module_driver::EnvironmentSetup::default(),
        &decision,
        &header,
        paths,
    )
    .expect("prelude environment");
    assert_eq!(context.effective_import_search_paths().unwrap(), expected);
}
