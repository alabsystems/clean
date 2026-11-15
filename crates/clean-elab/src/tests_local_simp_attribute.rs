// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `attribute [local simp] foo`: the lemma is a simp lemma until the
//! enclosing section or namespace ends, and `… in <command>` scopes it to the
//! one command.
//!
//! Lean's `attrInstance := attrKind attr` with `attrKind := optional
//! («scoped» <|> «local»)`; `cmd₁ in cmd₂` is `section cmd₁ cmd₂ end`
//! (`Lean/Elab/BuiltinCommand.lean:516-519`). Measured 2026-09-20 on main at
//! `5e2e6dc0e`, before this: the attribute parser read `local` as the
//! attribute NAME and skipped `simp` as its argument, so `attribute [local
//! simp] foo_eq` registered nothing and the `simp` it was written for failed
//! "simp: no progress" — in the explicit `section … end` form too. That is the
//! wall behind Mathlib `Logic/Unique.lean:240` (`attribute [local simp]
//! eq_iff_true_of_subsingleton in theorem Unique.bijective …`).
//!
//! Ground truth, pinned v4.30.0-rc2 `lean` binary (2026-09-20): every fixture
//! `accepts` takes elaborates there (exit 0), and every `after_*` theorem is
//! refused there with "`simp` made no progress".
//!
//! The fixtures run with a `FileContext`, as `clean check` runs a file: the
//! scoping lives in it.

use crate::{elaborate_decl_and_register_with_context, ElabResult, FileContext};
use clean_kernel::Environment;
use clean_parser::parse_file;

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Every declaration that failed, top-level or inside a section/namespace.
fn failures(src: &str) -> Vec<String> {
    let mut env = Environment::with_prelude();
    let mut fc = FileContext::new();
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut out = Vec::new();
    for d in &decls {
        match elaborate_decl_and_register_with_context(&mut env, d, &mut fc) {
            Ok(result) => collect_failures(&result, &mut out),
            Err(e) => out.push(format!("{e}")),
        }
    }
    out
}

fn accepts(src: &str, what: &str) {
    let failed = failures(src);
    assert!(failed.is_empty(), "{what}: {failed:?}");
}

/// Exactly the declaration `name` fails, and it fails in `simp`.
fn refuses_only(src: &str, name: &str) {
    let failed = failures(src);
    assert_eq!(failed.len(), 1, "only `{name}` may fail, got {failed:?}");
    assert!(
        failed[0].contains("simp"),
        "`{name}` must fail in `simp`, which no longer knows the lemma, got {failed:?}"
    );
}

const FOO: &str = "def foo (n : Nat) : Nat := n\n\
                   theorem foo_eq (n : Nat) : foo n = n := rfl\n";

#[test]
fn test_local_simp_attribute_is_in_force_inside_its_scope() {
    let src = format!(
        "{FOO}attribute [local simp] foo_eq in\n\
         theorem bar_in (n : Nat) : foo n = n := by simp\n\
         section\n\
         attribute [local simp] foo_eq\n\
         theorem bar_sec (n : Nat) : foo n = n := by simp\n\
         end\n\
         namespace N\n\
         attribute [local simp] foo_eq\n\
         theorem bar_ns (n : Nat) : foo n = n := by simp\n\
         end N\n"
    );
    accepts(&src, "`local simp` must register the lemma for its scope");
}

#[test]
fn test_local_simp_attribute_in_command_ends_with_the_command() {
    let src = format!(
        "{FOO}attribute [local simp] foo_eq in\n\
         theorem bar_in (n : Nat) : foo n = n := by simp\n\
         theorem after_in (n : Nat) : foo n = n := by simp\n"
    );
    refuses_only(&src, "after_in");
}

#[test]
fn test_local_simp_attribute_ends_with_its_section() {
    let src = format!(
        "{FOO}section\n\
         attribute [local simp] foo_eq\n\
         end\n\
         theorem after_sec (n : Nat) : foo n = n := by simp\n"
    );
    refuses_only(&src, "after_sec");
}

#[test]
fn test_local_simp_attribute_ends_with_its_namespace() {
    let src = format!(
        "{FOO}namespace N\n\
         attribute [local simp] foo_eq\n\
         end N\n\
         theorem after_ns (n : Nat) : foo n = n := by simp\n"
    );
    refuses_only(&src, "after_ns");
}

/// A lemma that was a simp lemma BEFORE the local attribute still is one after
/// the scope ends: retiring the local attribute must not take the global one.
#[test]
fn test_local_simp_attribute_does_not_retire_a_global_simp_lemma() {
    accepts(
        "def goo (n : Nat) : Nat := n\n\
         @[simp] theorem goo_eq (n : Nat) : goo n = n := rfl\n\
         section\n\
         attribute [local simp] goo_eq\n\
         end\n\
         theorem goo_still (n : Nat) : goo n = n := by simp\n",
        "a global simp lemma survives a local re-attribution",
    );
}
