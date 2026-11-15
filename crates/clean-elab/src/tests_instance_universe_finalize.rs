// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An `instance` of a class whose second universe only the VALUE fixes
//! (`HasEquiv.{u, v}`, `Equiv : α → α → Sort v`) reaches the kernel with ONE
//! universe for that slot in both its type and its value, not the header's
//! `?v` and the value's `?v'` (`Mathlib/Data/Subtype.lean`'s `instance
//! [HasEquiv α] (p) : HasEquiv (Subtype p)`, measured 2026-09-11).

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
fn test_instance_with_a_value_fixed_class_universe_kernel_checks() {
    let mut env = Environment::with_prelude();
    let src = "class HasEq2 (α : Sort u) where\n  eqv : α → α → Sort v\n\
               instance instHasEq2Sub {α : Sort u} [HasEq2 α] (p : α → Prop) : HasEq2 (Subtype p) :=\n  ⟨fun s t => HasEq2.eqv s.val t.val⟩\n\
               theorem eqvIff {α : Sort u} [HasEq2 α] {p : α → Prop} {s t : Subtype p} :\n    HasEq2.eqv s t = HasEq2.eqv s.val t.val := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the instance's value-fixed universe must reach the kernel resolved: {e}");
    }
}

#[test]
fn test_instance_short_form_and_where_form_agree_on_universes() {
    let mut env = Environment::with_prelude();
    let src = "class HasEq2 (α : Sort u) where\n  eqv : α → α → Sort v\n\
               instance instA : HasEq2 Nat := ⟨fun a b => a = b⟩\n\
               instance instB : HasEq2 Bool where\n  eqv a b := a = b\n\
               theorem useA : HasEq2.eqv (1 : Nat) 1 = (1 = 1) := rfl\n\
               theorem useB : HasEq2.eqv true true = (true = true) := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("both instance spellings must register with resolved universes: {e}");
    }
}

/// A postponed `?x =?= max ?x ?y` (the `Compl (α → Prop)` instance search
/// through a `Pi` instance, with `α : Type*` a universe metavariable) is
/// closed Lean's way — `?x := max ?x' ?y` — in both an `example` and an
/// `instance`, instead of reaching the kernel as `Sort (?x+1)` against
/// `Sort (max ?x ?y + 1)`.
#[test]
fn test_self_max_level_equation_is_solved_for_examples_and_instances() {
    let mut env = Environment::with_prelude();
    let src = "class Compl' (α : Type u) where\n  compl : α → α\n\
               instance Prop.instCompl' : Compl' Prop := ⟨Not⟩\n\
               instance Pi.instCompl' {ι : Type u} {π : ι → Type v} [∀ i, Compl' (π i)] : Compl' (∀ i, π i) :=\n  ⟨fun x i => Compl'.compl (x i)⟩\n\
               example {α : Type*} : Compl' (α → Prop) := inferInstance\n\
               example {α : Type*} : Compl' (α → α → Prop) := inferInstance\n\
               instance instRelCompl {α : Type*} : Compl' (α → α → Prop) := inferInstance\n\
               def relCompl {α : Type*} (r : α → α → Prop) : α → α → Prop := Compl'.compl r\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("self-max level equations must be closed before the kernel: {e}");
    }
}
