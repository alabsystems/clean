// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end Lake replacement smokes for #3707.
//!
//! The smoke runs the public `clean lake new/build/run` workflow with failing
//! `lean`, `lake`, and `elan` shims at the front of PATH. A regression that
//! delegates project semantics to a Lean4 process will either fail the command
//! or leave a marker file behind.

#![cfg(unix)]

use std::ffi::{OsStr, OsString};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn host_c_compiler() -> Option<PathBuf> {
    for var in ["CLEAN_CC", "CC"] {
        let Ok(value) = std::env::var(var) else {
            continue;
        };
        let path = PathBuf::from(value);
        if path.is_absolute() && compiler_responds(&path) {
            return Some(path);
        }
    }

    let path = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path) {
        for name in ["cc", "gcc", "clang"] {
            let candidate = dir.join(name);
            if candidate.is_file() && compiler_responds(&candidate) {
                return Some(candidate);
            }
        }
    }

    None
}

fn compiler_responds(path: &Path) -> bool {
    Command::new(path)
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

fn write_failing_tool(fake_bin: &Path, name: &str, marker: &Path) {
    let path = fake_bin.join(name);
    fs::write(
        &path,
        format!(
            "#!/bin/sh\nprintf '%s\\n' \"{name} $*\" >> '{}'\nexit 87\n",
            marker.display()
        ),
    )
    .unwrap_or_else(|err| panic!("failed to write fake {name}: {err}"));
    let mut perms = fs::metadata(&path)
        .unwrap_or_else(|err| panic!("failed to stat fake {name}: {err}"))
        .permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&path, perms)
        .unwrap_or_else(|err| panic!("failed to chmod fake {name}: {err}"));
}

fn stripped_system_path(fake_bin: &Path) -> OsString {
    std::env::join_paths([
        fake_bin,
        Path::new("/usr/bin"),
        Path::new("/bin"),
        Path::new("/usr/sbin"),
        Path::new("/sbin"),
    ])
    .expect("join stripped PATH")
}

fn run_clean(cwd: &Path, stripped_path: &OsStr, cc: &Path, args: &[&str]) -> Output {
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(args)
        .current_dir(cwd)
        .env("PATH", stripped_path)
        .env("CLEAN_CC", cc)
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"));

    assert!(
        output.status.success(),
        "clean {args:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

#[test]
fn lake_new_build_run_with_lean4_tools_stripped_from_path() {
    let Some(cc) = host_c_compiler() else {
        eprintln!("skipping #3707 Lake PATH-stripped smoke: no host C compiler found");
        return;
    };

    let dir = tempfile::tempdir().expect("tempdir");
    let fake_bin = dir.path().join("fake-bin");
    fs::create_dir(&fake_bin).expect("create fake bin");
    let marker = dir.path().join("lean4-delegation-marker.txt");
    for tool in ["lean", "lake", "elan"] {
        write_failing_tool(&fake_bin, tool, &marker);
    }

    let stripped_path = stripped_system_path(&fake_bin);

    let project_name = "path_stripped_smoke";
    let project_dir = dir.path().join(project_name);

    run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "new", project_name, "--exe"],
    );
    assert!(project_dir.join("lakefile.lean").exists());
    assert!(project_dir.join("Main.lean").exists());

    run_clean(
        &project_dir,
        &stripped_path,
        &cc,
        &["lake", "build", project_name, "-j", "1"],
    );
    let run = run_clean(
        &project_dir,
        &stripped_path,
        &cc,
        &["lake", "run", project_name, "-j", "1"],
    );

    assert_eq!(String::from_utf8_lossy(&run.stdout), "Hello, world!\n");
    assert!(
        !marker.exists(),
        "Lean4 delegation shim was invoked:\n{}",
        fs::read_to_string(&marker).unwrap_or_default()
    );
}

#[test]
fn lake_path_dependency_build_test_run_with_external_tools_stripped_from_path() {
    let Some(cc) = host_c_compiler() else {
        eprintln!("skipping #3707 Lake dependency workflow smoke: no host C compiler found");
        return;
    };

    let dir = tempfile::tempdir().expect("tempdir");
    let fake_bin = dir.path().join("fake-bin");
    fs::create_dir(&fake_bin).expect("create fake bin");
    let marker = dir.path().join("external-delegation-marker.txt");
    for tool in ["lean", "lake", "elan", "git"] {
        write_failing_tool(&fake_bin, tool, &marker);
    }
    let stripped_path = stripped_system_path(&fake_bin);

    let dep_dir = dir.path().join("dep_pkg");
    fs::create_dir(&dep_dir).expect("create dep package");
    fs::write(
        dep_dir.join("lakefile.lean"),
        r#"import Lake
open Lake DSL

package dep_pkg where
  version := "0.1.0"

@[default_target]
lean_lib DepPkg where
  roots := #[`DepPkg]
"#,
    )
    .expect("write dep lakefile");
    fs::write(
        dep_dir.join("DepPkg.lean"),
        "def depMessage := \"dep ok\"\n",
    )
    .expect("write dep root");

    let app_dir = dir.path().join("app_pkg");
    fs::create_dir(&app_dir).expect("create app package");
    fs::write(
        app_dir.join("lakefile.lean"),
        r#"import Lake
open Lake DSL

package app_pkg where
  version := "0.1.0"

require dep_pkg from path "../dep_pkg"

@[default_target]
lean_lib AppPkg where
  roots := #[`AppPkg]

lean_exe app_run where
  root := `Main

lean_test app_tests where
  root := `Tests
"#,
    )
    .expect("write app lakefile");
    fs::write(
        app_dir.join("AppPkg.lean"),
        "import DepPkg\n\ndef appMessage := \"app ok\"\n",
    )
    .expect("write app root");
    fs::write(
        app_dir.join("Main.lean"),
        "import AppPkg\n\ndef main : IO Unit := IO.println \"run ok\"\n",
    )
    .expect("write app main");
    fs::write(
        app_dir.join("Tests.lean"),
        "import AppPkg\n\ndef main : IO Unit := IO.println \"test ok\"\n",
    )
    .expect("write app tests");

    let app_dir_arg = app_dir.to_str().expect("temp path should be valid UTF-8");
    let resolve = run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "resolve"],
    );
    assert!(
        String::from_utf8_lossy(&resolve.stdout).contains("Resolved 1 dependencies"),
        "resolve should write the path dependency manifest:\n{}",
        String::from_utf8_lossy(&resolve.stdout)
    );

    let fetch = run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "fetch"],
    );
    assert!(
        String::from_utf8_lossy(&fetch.stdout).contains("All dependencies up to date."),
        "fetch should validate the path dependency without git:\n{}",
        String::from_utf8_lossy(&fetch.stdout)
    );

    let update = run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "update", "-v"],
    );
    let update_stdout = String::from_utf8_lossy(&update.stdout);
    assert!(
        update_stdout.contains("dep_pkg skipped (path package)")
            && update_stdout.contains("All dependencies are up to date."),
        "update should skip path dependencies without invoking git:\n{update_stdout}"
    );

    run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "build", "AppPkg", "-j", "1"],
    );
    assert!(
        app_dir.join(".lake/build/lib/DepPkg.olean").exists(),
        "build should compile the path dependency through the workspace"
    );
    assert!(
        app_dir.join(".lake/build/lib/AppPkg.olean").exists(),
        "build should compile the app library"
    );

    run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "build", "app_run", "-j", "1"],
    );
    assert!(
        app_dir.join(".lake/build/bin/app_run").exists(),
        "executable build should produce a clean-owned native artifact"
    );

    let test = run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "test", "app_tests", "-j", "1"],
    );
    let test_stdout = String::from_utf8_lossy(&test.stdout);
    assert!(
        test_stdout.contains("test ok\n") && test_stdout.contains("Test results: 1 passed"),
        "test should execute the native bounded test target:\n{test_stdout}"
    );

    let run = run_clean(
        dir.path(),
        &stripped_path,
        &cc,
        &["lake", "--dir", app_dir_arg, "run", "app_run", "-j", "1"],
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout), "run ok\n");

    assert!(
        !marker.exists(),
        "external delegation shim was invoked:\n{}",
        fs::read_to_string(&marker).unwrap_or_default()
    );
}
