// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Modern Lean resolves a dependency listing by package before appending the
//! remaining module components. Source and artifact listings have separate roots.

use std::fs;
use std::process::Command;

#[test]
fn modern_dependency_queries_respect_package_roots_and_file_kinds() {
    for version in ["4.30.0-rc2", "4.36.0"] {
        check_package_roots(version);
    }
}

fn check_package_roots(version: &str) {
    let project = tempfile::tempdir().unwrap();
    let root = project.path().canonicalize().unwrap();
    let toolchain = root.join(format!("toolchains/leanprover--lean4---v{version}"));
    let lib = toolchain.join("lib/lean");
    fs::create_dir_all(lib.join("Init")).unwrap();
    fs::write(
        lib.join("Init/Prelude.olean"),
        include_bytes!("../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean"),
    )
    .unwrap();

    let source = root.join("src");
    let artifacts = root.join("artifacts");
    let fallback = root.join("fallback");
    for dir in [&source, &artifacts, &fallback] {
        fs::create_dir_all(dir.join("Pkg")).unwrap();
    }
    for ext in ["lean", "olean"] {
        fs::write(fallback.join(format!("Pkg/OnlyLater.{ext}")), "").unwrap();
    }
    fs::write(
        root.join("Dependencies.lean"),
        "prelude\nimport Pkg.OnlyLater\nimport Missing.X\n",
    )
    .unwrap();

    let run = |flag: &str| {
        Command::new(env!("CARGO_BIN_EXE_clean"))
            .current_dir(&root)
            .args(["lean", flag, "Dependencies.lean"])
            .env("CLEAN_LEAN_VERSION", version)
            .env("ELAN_HOME", &root)
            .env(
                "LEAN_PATH",
                std::env::join_paths([&artifacts, &fallback]).unwrap(),
            )
            .env(
                "LEAN_SRC_PATH",
                std::env::join_paths([&source, &fallback]).unwrap(),
            )
            .output()
            .unwrap()
    };
    let built_in_src = toolchain.join("bin/../src/lean");
    for (flag, ext, first, roots) in [
        (
            "--deps",
            "olean",
            &artifacts,
            vec![artifacts.clone(), fallback.clone(), lib],
        ),
        (
            "--src-deps",
            "lean",
            &source,
            vec![
                source.clone(),
                fallback.clone(),
                built_in_src.join("lake"),
                built_in_src,
            ],
        ),
    ] {
        let output = run(flag);
        assert_eq!(output.status.code(), Some(1));
        let expected = first.join(format!("Pkg/OnlyLater.{ext}"));
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!("{}\n", expected.display())
        );
        let entries = roots
            .iter()
            .map(|entry| entry.as_path().display().to_string())
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(String::from_utf8(output.stderr).unwrap(), format!(
            "unknown module prefix 'Missing'\n\nNo directory 'Missing' or file 'Missing.{ext}' in the search path entries:\n{entries}\n"
        ));
    }
}

#[cfg(unix)]
#[test]
fn stable_dependencies_keep_user_symlinks_and_print_the_physical_sdk_prefix() {
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    use std::os::unix::fs::symlink;

    let project = tempfile::tempdir().unwrap();
    let root = project.path().canonicalize().unwrap();
    let sdk = root.join("installed-sdk");
    let user = root.join("user-path-alias");
    for directory in [
        sdk.join("bin"),
        sdk.join("lib/lean/Init"),
        sdk.join("src/lean/Init"),
        root.join("toolchains"),
        root.join("project-modules/Pkg"),
    ] {
        fs::create_dir_all(directory).unwrap();
    }
    fs::write(
        sdk.join("lib/lean/Init/Prelude.olean"),
        include_bytes!("../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean"),
    )
    .unwrap();
    symlink(&sdk, root.join("toolchains/leanprover--lean4---v4.36.0")).unwrap();
    symlink(root.join("project-modules"), &user).unwrap();
    fs::write(
        root.join("Deps.lean"),
        "prelude\nimport Pkg.Child\nimport Init\n",
    )
    .unwrap();

    for (args, ext, sdk_dir) in [
        (&["--deps", "Deps.lean"][..], "olean", "lib/lean"),
        (&["--src-deps", "Deps.lean"][..], "lean", "bin/../src/lean"),
        (
            &["--stdin", "--deps", "--src-deps"][..],
            "olean",
            "lib/lean",
        ),
        (
            &["--stdin", "--src-deps", "--deps"][..],
            "olean",
            "lib/lean",
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .current_dir(&root)
            .arg("lean")
            .args(args)
            .stdin(fs::File::open(root.join("Deps.lean")).unwrap())
            .env("ELAN_HOME", &root)
            .env("CLEAN_LEAN_VERSION", "4.36.0")
            .env("LEAN_PATH", &user)
            .env("LEAN_SRC_PATH", &user)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!(
                "{}\n{}\n",
                user.join(format!("Pkg/Child.{ext}")).display(),
                sdk.join(sdk_dir).join(format!("Init.{ext}")).display(),
            )
        );
    }

    // Official Lean decodes invalid Unix environment bytes before looking up a
    // package. Skipping this directory would silently select the later package.
    let decoded = root.join("candidate���");
    fs::create_dir_all(decoded.join("Pkg")).unwrap();
    let mut bytes = root.join("candidate").as_os_str().as_bytes().to_vec();
    bytes.extend([0x80, 0x80, 0xff, 0xff]);
    let raw = std::path::PathBuf::from(std::ffi::OsString::from_vec(bytes));
    let search = std::env::join_paths([&raw, &user]).unwrap();
    for (flag, ext) in [("--deps", "olean"), ("--src-deps", "lean")] {
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .current_dir(&root)
            .args(["lean", flag, "Deps.lean"])
            .env("ELAN_HOME", &root)
            .env("CLEAN_LEAN_VERSION", "4.36.0")
            .env("LEAN_PATH", &search)
            .env("LEAN_SRC_PATH", &search)
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let child = decoded.join(format!("Pkg/Child.{ext}"));
        assert_eq!(
            String::from_utf8(output.stdout).unwrap().lines().next(),
            child.to_str()
        );
    }
}
