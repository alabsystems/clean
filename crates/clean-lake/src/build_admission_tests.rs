// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake build` and `clean lake check-build` admit every module they
//! load that the workspace does not build, through the authority `clean
//! check` uses (module-trust round 31).
//!
//! Measured by the verification of `a7c69cb8c` on that tree and on
//! `f4af8f11a`, `6d4100991`, `e3f696689` and `3f45fb7c6`: a Clean-built
//! library `Mathlib.Evil` (the same with `Std.` or `Init.`) whose artifact
//! was rewritten from `v := 0` to `v := 1`, its source left beside it,
//! reached by a consumer workspace through `LEAN_PATH`. `clean check`
//! refused the import ("not the build of its source"); `clean lake build`
//! printed `Build OK (2 modules: 2 built)` with a dependent, and `clean lake
//! check-build` `Build check passed`, disclosing nothing. A toolchain-named
//! import the workspace does not provide was loaded from the search paths
//! with no binding at all (`is_stdlib_import`).
//!
//! These tests set `LEAN_PATH` through the crate's serialized environment
//! guard, so the consumer's toolchain-named imports resolve to the library.

use super::{BuildContext, BuildOptions, BuildResult};
use crate::test_env::with_serialized_env_vars;
use crate::workspace::Workspace;
use clean_kernel::Name;
use clean_olean::payload::{decode_clean_payload, encode_clean_payload, CleanPayload};
use std::fs;
use std::path::{Path, PathBuf};

/// A library workspace declaring the modules `files` (name, source) under
/// the library `lib`, built in place.
fn built_library(dir: &Path, lib: &str, files: &[(&str, &str)]) {
    let roots = files
        .iter()
        .map(|(m, _)| format!("\"{m}\""))
        .collect::<Vec<_>>()
        .join(", ");
    fs::create_dir_all(dir).expect("library dir");
    fs::write(
        dir.join("lakefile.toml"),
        format!(
            "name = \"lib\"\ndefaultTargets = [\"{lib}\"]\n\n[[lean_lib]]\nname = \"{lib}\"\nroots = [{roots}]\n"
        ),
    )
    .expect("library lakefile");
    for (module, source) in files {
        let path = dir.join(format!("{}.lean", module.replace('.', "/")));
        fs::create_dir_all(path.parent().expect("parent")).expect("source dir");
        fs::write(path, source).expect("library source");
    }
    let result = BuildContext::new(Workspace::load(dir).expect("library workspace"))
        .build_all()
        .expect("library build runs");
    assert!(result.failed.is_empty(), "the library builds: {result:?}");
}

fn olean(lib_dir: &Path, module: &str) -> PathBuf {
    lib_dir.join(format!("{}.olean", module.replace('.', "/")))
}

fn payload(path: &Path) -> (Vec<u8>, CleanPayload) {
    let bytes = fs::read(path).expect("artifact");
    let payload = decode_clean_payload(&bytes)
        .expect("decode")
        .expect("a Clean-built artifact carries a payload");
    (bytes, payload)
}

/// Rewrite the payload of `path` in place (the companions go: their regions
/// were laid out after the original length).
fn rewrite(path: &Path, edit: impl FnOnce(&mut CleanPayload)) {
    let (bytes, mut p) = payload(path);
    edit(&mut p);
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(encode_clean_payload(&p).expect("encode"));
    fs::write(path, out).expect("write");
    let _ = fs::remove_file(path.with_extension("olean.server"));
    let _ = fs::remove_file(path.with_extension("olean.private"));
}

/// The value `1 : Nat` as `clean lake build` writes it, from a donor build.
fn value_one(root: &Path, module: &str) -> clean_kernel::Expr {
    let donor = root.join("donor");
    built_library(
        &donor,
        "Donor",
        &[(module, &format!("def {module}.v : Nat := 1\n"))],
    );
    let n = Name::from_string(&format!("{module}.v"));
    payload(&olean(&donor.join(".lake/build/lib"), module))
        .1
        .constants
        .into_iter()
        .find(|c| c.name == n)
        .and_then(|c| c.value)
        .expect("donor value")
}

fn set_v(path: &Path, module: &str, value: clean_kernel::Expr) {
    let n = Name::from_string(&format!("{module}.v"));
    rewrite(path, |p| {
        p.constants
            .iter_mut()
            .find(|c| c.name == n)
            .expect("the payload declares v")
            .value = Some(value);
    });
}

/// A consumer workspace whose module `U` imports `import` and claims `claim`.
fn consumer(dir: &Path, import: &str, claim: &str) {
    fs::create_dir_all(dir).expect("consumer dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"usr\"\ndefaultTargets = [\"U\"]\n\n[[lean_lib]]\nname = \"U\"\nroots = [\"U\"]\n",
    )
    .expect("consumer lakefile");
    fs::write(
        dir.join("U.lean"),
        format!("import {import}\n\ntheorem U.c : {claim} := rfl\n"),
    )
    .expect("consumer source");
}

/// `clean lake build` (or `check-build`) of `dir` with `LEAN_PATH=lib_path`.
fn build_with(dir: &Path, lib_path: &Path, check_only: bool) -> BuildResult {
    with_serialized_env_vars(&[("LEAN_PATH", lib_path.to_str().expect("utf-8"))], || {
        BuildContext::new(Workspace::load(dir).expect("consumer workspace"))
            .with_options(BuildOptions::new().with_check_only(check_only))
            .build_all()
            .expect("the build runs")
    })
}

fn refused(result: &BuildResult) -> bool {
    result
        .failed
        .iter()
        .any(|(_, why)| why.contains("is not the build of its source"))
}

#[test]
fn a_toolchain_named_artifact_rewritten_beside_its_source_builds_nothing_against_it() {
    let tmp = tempfile::tempdir().expect("tmp");
    for prefix in ["Mathlib", "Std", "Init"] {
        let module = format!("{prefix}.Evil");
        let root = tmp.path().join(prefix);
        let lib = root.join("lib");
        built_library(
            &lib,
            prefix,
            &[(&module, &format!("def {module}.v : Nat := 0\n"))],
        );
        let lib_path = lib.join(".lake/build/lib");

        // Control: the honest artifact is bound to its source, and a true
        // claim builds with nothing disclosed.
        let honest = root.join("honest");
        consumer(&honest, &module, &format!("{module}.v = 0"));
        for check_only in [false, true] {
            let result = build_with(&honest, &lib_path, check_only);
            assert!(result.failed.is_empty(), "{prefix} honest: {result:?}");
            assert!(result.disclosures.is_empty(), "{prefix}: {result:?}");
        }

        // The artifact now says `v := 1`; its source still says `0`.
        set_v(
            &olean(&lib_path, &module),
            &module,
            value_one(&root, &module),
        );
        for (claim, tag) in [("1", "false in the source"), ("0", "true in the source")] {
            let dir = root.join(format!("u{claim}"));
            consumer(&dir, &module, &format!("{module}.v = {claim}"));
            for check_only in [false, true] {
                let result = build_with(&dir, &lib_path, check_only);
                assert!(
                    refused(&result),
                    "{prefix}, claim {tag}, check_only {check_only}: {result:?}"
                );
            }
        }
    }
}

#[test]
fn a_bare_toolchain_named_artifact_is_disclosed_by_the_build() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = tmp.path().join("lib");
    built_library(
        &lib,
        "Mathlib",
        &[("Mathlib.Evil", "def Mathlib.Evil.v : Nat := 0\n")],
    );
    // The artifacts alone, with no workspace or source anywhere near them.
    let bare = tmp.path().join("bare");
    fs::create_dir_all(bare.join("Mathlib")).expect("bare dir");
    for part in ["olean", "olean.server", "olean.private"] {
        fs::copy(
            lib.join(format!(".lake/build/lib/Mathlib/Evil.{part}")),
            bare.join(format!("Mathlib/Evil.{part}")),
        )
        .expect("copy part");
    }
    let dir = tmp.path().join("u");
    consumer(&dir, "Mathlib.Evil", "Mathlib.Evil.v = 0");
    for check_only in [false, true] {
        let result = build_with(&dir, &bare, check_only);
        assert!(result.failed.is_empty(), "{result:?}");
        assert!(
            result
                .disclosures
                .iter()
                .any(|row| row.starts_with("Mathlib.Evil: ")),
            "check_only {check_only}: {result:?}"
        );
    }
}

/// The whole closure a build loads is admitted, not the named import's
/// root: here the root stays the build of its source (its trace pins the
/// module behind it by that module's ARTIFACT, which is unchanged), and only
/// the module behind it is no longer the build of its own source.
#[test]
fn a_module_behind_the_named_import_is_admitted_too() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = tmp.path().join("lib");
    built_library(
        &lib,
        "Mathlib",
        &[
            ("Mathlib.Base", "def Mathlib.Base.v : Nat := 0\n"),
            (
                "Mathlib.Top",
                "import Mathlib.Base\n\ndef Mathlib.Top.w : Nat := Mathlib.Base.v\n",
            ),
        ],
    );
    let lib_path = lib.join(".lake/build/lib");
    let dir = tmp.path().join("u");
    consumer(&dir, "Mathlib.Top", "Mathlib.Top.w = 0");
    let result = build_with(&dir, &lib_path, false);
    assert!(result.failed.is_empty(), "honest: {result:?}");
    fs::write(
        lib.join("Mathlib/Base.lean"),
        "def Mathlib.Base.v : Nat := 2\n",
    )
    .expect("edit the source behind the import");
    let dir = tmp.path().join("u2");
    consumer(&dir, "Mathlib.Top", "Mathlib.Top.w = 0");
    let result = build_with(&dir, &lib_path, false);
    assert!(refused(&result), "{result:?}");
    assert!(
        result
            .failed
            .iter()
            .any(|(_, why)| why.contains("import `Mathlib.Base`")),
        "the module behind the import is the one refused: {result:?}"
    );
}

#[test]
fn a_reused_module_is_admitted_again() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = tmp.path().join("lib");
    built_library(
        &lib,
        "Mathlib",
        &[("Mathlib.Evil", "def Mathlib.Evil.v : Nat := 0\n")],
    );
    let lib_path = lib.join(".lake/build/lib");
    let dir = tmp.path().join("u");
    consumer(&dir, "Mathlib.Evil", "Mathlib.Evil.v = 0");
    let first = build_with(&dir, &lib_path, false);
    assert!(
        first.failed.is_empty() && first.built == vec!["U".to_string()],
        "{first:?}"
    );
    let again = build_with(&dir, &lib_path, false);
    assert!(again.skipped == vec!["U".to_string()], "reused: {again:?}");
    // The library's source now says something else; its artifact is
    // unchanged, so U's trace still matches — but the artifact U rests on is
    // no longer the build of its source.
    fs::write(
        lib.join("Mathlib/Evil.lean"),
        "def Mathlib.Evil.v : Nat := 2\n",
    )
    .expect("edit");
    let result = build_with(&dir, &lib_path, false);
    assert!(refused(&result), "{result:?}");
}
