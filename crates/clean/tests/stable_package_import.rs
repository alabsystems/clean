// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise package-root shadowing across the actual frontend and Lean SDK.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK"]
fn stable_project_compiler_refuses_an_absent_child_in_the_first_package() {
    let official = std::env::var_os("CLEAN_LEAN436_BIN")
        .map(PathBuf::from)
        .expect("set CLEAN_LEAN436_BIN to the official Lean 4.36.0 executable");
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path().canonicalize().unwrap();
    let first = root.join("first���");
    let later = root.join("later");
    for search_root in [&first, &later] {
        fs::create_dir_all(search_root.join("Pkg")).unwrap();
    }
    fs::write(root.join("lean-toolchain"), "leanprover/lean4:v4.36.0\n").unwrap();
    fs::write(
        later.join("Pkg/OnlyLater.lean"),
        "prelude\naxiom fromLater : Prop\n",
    )
    .unwrap();
    let output = Command::new(&official)
        .current_dir(&later)
        .args(["-o", "Pkg/OnlyLater.olean", "Pkg/OnlyLater.lean"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    fs::write(
        root.join("Use.lean"),
        "prelude\nimport Pkg.OnlyLater\naxiom useLater : fromLater\n",
    )
    .unwrap();

    for reference in [true, false] {
        let run = |search: &[&PathBuf]| -> Output {
            let mut command = if reference {
                Command::new(&official)
            } else {
                let mut cmd = Command::new(env!("CARGO_BIN_EXE_clean"));
                cmd.arg("lean").env_remove("CLEAN_LEAN_VERSION");
                cmd
            };
            command
                .current_dir(&root)
                .env("LEAN_PATH", std::env::join_paths(search).unwrap())
                .arg("Use.lean")
                .output()
                .unwrap()
        };
        let pass = run(&[&later]);
        assert!(pass.status.success(), "{pass:?}");
        let check_first = |entry: &PathBuf| {
            let fail = run(&[entry, &later]);
            assert_eq!(fail.status.code(), Some(1), "{fail:?}");
            let missing = first.join("Pkg/OnlyLater.olean");
            let messages = [fail.stdout, fail.stderr].concat();
            assert!(
                String::from_utf8_lossy(&messages).contains(missing.to_str().unwrap()),
                "{messages:?}"
            );
        };
        check_first(&first);
        #[cfg(unix)]
        {
            use std::os::unix::ffi::{OsStrExt, OsStringExt};
            let mut bytes = root.join("first").as_os_str().as_bytes().to_vec();
            bytes.extend([0x80, 0x80, 0xff, 0xff]);
            check_first(&PathBuf::from(std::ffi::OsString::from_vec(bytes)));
        }
    }
}
