// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake exe` / `clean lake run` under the lakefile's `leanOptions`
//! (gap G50). The review's `exepkg`: pinned `lake exe hello` refuses
//! `Main.lean` (`unknown identifier 'Foo'`) under `autoImplicit false`; Clean
//! used to fall back to its native pipeline, which ignores the options, and
//! printed `hi`.

use super::*;

fn project(package_fields: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join("lakefile.lean"),
        format!(
            "import Lake\nopen Lake DSL\n\npackage exepkg{package_fields}\n\n\
             @[default_target]\nlean_exe hello where\n  root := `Main\n"
        ),
    )
    .expect("write lakefile");
    std::fs::write(
        dir.path().join("Main.lean"),
        "def idFoo (x : Foo) : Foo := x\n\ndef main : IO Unit := IO.println \"hi\"\n",
    )
    .expect("write Main.lean");
    dir
}

const AUTO_IMPLICIT_OFF: &str = " where\n  leanOptions := #[⟨`autoImplicit, false⟩]";

#[test]
fn test_lake_exe_under_lean_options_refuses_native_fallback() {
    let dir = project(AUTO_IMPLICIT_OFF);
    let err = lake_exe("hello", &[], false, Some(dir.path().to_path_buf()))
        .expect_err("Lake refuses Main under autoImplicit false; Clean must not run it");
    let text = format!("{err:#}");
    assert!(text.contains("leanOptions"), "{text}");
    assert!(
        !native_executable_build_path(&clean_lake::Workspace::new(dir.path(), "exepkg"), "hello")
            .exists(),
        "nothing was linked"
    );
}

#[test]
fn test_lake_run_under_lean_options_refuses_native_fallback() {
    let dir = project(AUTO_IMPLICIT_OFF);
    let err = lake_run(None, &[], false, 1, Some(dir.path().to_path_buf()))
        .expect_err("same refusal through `lake run`");
    assert!(format!("{err:#}").contains("leanOptions"), "{err:#}");
}

#[test]
fn test_refuse_native_fallback_only_when_options_govern_the_failure() {
    let dir = project("");
    let ws = clean_lake::Workspace::load(dir.path()).expect("loads");
    let failed = vec![("Main".to_string(), "some failure".to_string())];
    refuse_native_fallback_under_lean_options(&ws, &failed, "exe")
        .expect("no options: the legacy fallback is not this refusal's business");
    let dir = project(AUTO_IMPLICIT_OFF);
    let ws = clean_lake::Workspace::load(dir.path()).expect("loads");
    refuse_native_fallback_under_lean_options(&ws, &failed, "exe")
        .expect_err("options govern Main");
}
