// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A leading-dot identifier in an argument slot whose type is still open is
//! elaborated after the remaining arguments have pinned it (Lean postpones
//! `elabDotIdent` on a metavariable), and a FUNCTION-typed expected type
//! names the constructor through its result (`withForallBody`):
//! `h.elim (.intro _) (.intro _) : ∃ h, p h` — `Prop.exists_iff` in
//! `Mathlib/Logic/Basic.lean`, measured 2026-09-11 ("Unknown identifier:
//! .intro").

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

const MY_OR_ELIM: &str =
    "theorem myOrElim {a b c : Prop} (h : a ∨ b) (l : a → c) (r : b → c) : c :=\n\
     \x20 @Or.rec a b (fun _ => c) (fun x => l x) (fun y => r y) h\n";

#[test]
fn test_leading_dot_argument_waits_for_its_slot_and_resolves_through_the_arrow() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{MY_OR_ELIM}theorem viaDot {{p : Prop → Prop}} (h : p False ∨ p True) : ∃ h, p h :=\n\
         \x20 myOrElim h (.intro _) (.intro _)\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`.intro _` must resolve to `Exists.intro` through the slot's arrow type: {e}");
    }
}

#[test]
fn test_leading_dot_in_a_pinned_slot_is_unchanged() {
    let mut env = Environment::with_prelude();
    let src = "def someNat : Option Nat := .some 3\n\
               theorem viaApp (n : Nat) : ∃ k, k = n := .intro n rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("leading-dot identifiers with a known expected type are unchanged: {e}");
    }
}
