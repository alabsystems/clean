// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake build` under the lakefile's `leanOptions` (gap G50).
//!
//! `trust_ir-semantics` declares `leanOptions := #[⟨`autoImplicit, false⟩]`.
//! Measured on pinned Lean 4.8.0: `theorem t (x : Foo) : x = x := rfl` with
//! `Foo` undefined is ACCEPTED by `lean f.lean` (Foo auto-binds) and REFUSED
//! by `lean -DautoImplicit=false f.lean` (`unknown identifier 'Foo'`), which
//! is how Lake compiles every module of that package. Before this, Clean's
//! build skipped `leanOptions` with a warning and built the module.

use super::*;
use tempfile::TempDir;

/// The G50 repro: only auto-binding accepts `Foo`.
const UNDEFINED_TYPE: &str = "theorem t (x : Foo) : x = x := rfl\n";

/// A one-module package whose lakefile `package` block carries `package_body`
/// (a `where` block's fields, or empty) and whose module is `source`.
fn project(package_body: &str, lib_body: &str, source: &str) -> TempDir {
    let tmp = TempDir::new().expect("tempdir");
    let package = if package_body.is_empty() {
        "package opts\n".to_string()
    } else {
        format!("package opts where\n{package_body}\n")
    };
    std::fs::write(
        tmp.path().join("lakefile.lean"),
        format!("{package}\nlean_lib Opts where\n  roots := #[`Opts]\n{lib_body}\n"),
    )
    .expect("write lakefile");
    std::fs::write(tmp.path().join("Opts.lean"), source).expect("write module");
    tmp
}

fn build(tmp: &TempDir) -> BuildResult {
    let ws = Workspace::load(tmp.path()).expect("workspace loads");
    BuildContext::new(ws)
        .with_options(BuildOptions {
            check_only: true,
            ..Default::default()
        })
        .build_all()
        .expect("build runs")
}

fn refused(result: &BuildResult) -> Option<&str> {
    result
        .failed
        .iter()
        .find(|(m, _)| m == "Opts")
        .map(|(_, reason)| reason.as_str())
}

/// The trust_ir-semantics lakefile shape, multi-line array and all.
const TRUST_IR_PACKAGE: &str = "  leanOptions := #[\n    ⟨`autoImplicit, false⟩\n  ]";

#[test]
fn test_build_lean_options_auto_implicit_false_refuses_undefined_type() {
    let result = build(&project(TRUST_IR_PACKAGE, "", UNDEFINED_TYPE));
    let reason = refused(&result).unwrap_or_else(|| panic!("Opts must be refused: {result:?}"));
    assert!(reason.contains("Foo"), "the refusal names `Foo`: {reason}");
}

#[test]
fn test_build_without_lean_options_accepts_undefined_type_by_auto_bind() {
    // Lean's default (autoImplicit true): the control that makes the
    // refusal above the option's doing.
    let result = build(&project("", "", UNDEFINED_TYPE));
    assert!(result.failed.is_empty(), "control must build: {result:?}");
    assert_eq!(result.built, vec!["Opts".to_string()]);
}

#[test]
fn test_build_lib_lean_options_apply_and_override_package() {
    // Library-level options apply to its modules...
    let lib_off = "  leanOptions := #[⟨`autoImplicit, false⟩]";
    let result = build(&project("", lib_off, UNDEFINED_TYPE));
    assert!(
        refused(&result).is_some(),
        "lib leanOptions apply: {result:?}"
    );

    // ...and come after the package's, so the library's value wins.
    let lib_on = "  leanOptions := #[⟨`autoImplicit, true⟩]";
    let result = build(&project(TRUST_IR_PACKAGE, lib_on, UNDEFINED_TYPE));
    assert!(result.failed.is_empty(), "lib value wins: {result:?}");
}

#[test]
fn test_build_more_lean_args_define_applies() {
    let args = "  moreLeanArgs := #[\"-DautoImplicit=false\"]";
    let result = build(&project(args, "", UNDEFINED_TYPE));
    assert!(
        refused(&result).is_some(),
        "moreLeanArgs -D applies: {result:?}"
    );
}

#[test]
fn test_build_unknown_lean_option_fails_like_lean() {
    // `lean -Dbogus=true` refuses before elaborating anything.
    let bogus = "  leanOptions := #[⟨`bogus, true⟩]";
    let result = build(&project(bogus, "", "theorem u : 1 = 1 := rfl\n"));
    let reason = refused(&result).unwrap_or_else(|| panic!("must be refused: {result:?}"));
    assert!(
        reason.contains("unknown configuration option 'bogus'"),
        "Lean's message: {reason}"
    );
}

#[test]
fn test_build_unreadable_lean_options_refuses_instead_of_ignoring() {
    // An identifier Clean cannot evaluate: the options Lake would use are
    // unknown, so the module is not built under different ones.
    let opaque = "  leanOptions := myOptions";
    let result = build(&project(opaque, "", "theorem u : 1 = 1 := rfl\n"));
    let reason = refused(&result).unwrap_or_else(|| panic!("must be refused: {result:?}"));
    assert!(reason.contains("leanOptions := myOptions"), "{reason}");
}
