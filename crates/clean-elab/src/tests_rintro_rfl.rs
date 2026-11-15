// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A top-level `rfl` pattern of `rintro` substitutes the equation it
//! introduces — Lean's `rcasesCore` `.one `rfl` is `substEq`
//! (`Lean/Elab/Tactic/RCases.lean`). Clean's `rintro` handler sent it to a
//! plain `intro` of a hypothesis NAMED `rfl` and substituted nothing, so even
//! `a = b → b = a := by rintro rfl; rfl` failed (measured 2026-09-12; the
//! first wall of `Mathlib/Logic/Basic.lean`'s `heq_of_eq_cast`).
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): each accepted declaration elaborates there as written, and
//! `n1` fails there with "Tactic `subst` failed".

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_rintro_rfl_substitutes_the_introduced_equation() {
    let mut env = Environment::with_prelude();
    let src = "theorem t1 {α : Sort u} (a b : α) : a = b → b = a := by\n\
               \x20 rintro rfl; rfl\n\
               theorem t2 {α β : Sort u} (e : β = α) (a : α) (b : β) : a = cast e b → a = cast e b := by\n\
               \x20 rintro rfl; rfl\n\
               theorem t3 {α : Sort u} (f : α → α) (a b : α) : a = f b → a = f b := by\n\
               \x20 rintro rfl; rfl\n\
               theorem t3b {α : Sort u} (f : α → α) (a b : α) : a = f b → f b = a := by\n\
               \x20 rintro rfl; rfl\n\
               theorem t4 {α : Sort u} (f : α → α) (a b : α) : f b = a → f b = a := by\n\
               \x20 rintro rfl; rfl\n\
               theorem t6 {α : Sort u} (f : α → α) (b : α) : ∀ a, a = f b → f b = a := by\n\
               \x20 rintro a rfl; rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`rintro rfl` must substitute the equation it introduces, as Lean's does: {e}");
    }
}

/// `rfl` on a hypothesis that is not an equation is refused, as Lean's
/// `subst` refuses it — never introduced under the name `rfl`.
#[test]
fn test_rintro_rfl_on_a_non_equation_is_refused() {
    let mut env = Environment::with_prelude();
    let err = elab(
        &mut env,
        "theorem n1 (p : Prop) : p → p := by\n\x20 rintro rfl\n",
    )
    .expect("Lean refuses `rintro rfl` on `p → p` (`subst` failed); so must Clean");
    assert!(
        err.contains("subst") || err.contains("Subst") || err.contains("equality"),
        "the refusal must come from `subst`: {err}"
    );
}
