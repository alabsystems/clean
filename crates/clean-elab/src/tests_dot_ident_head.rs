// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `.name` against an expected type headed by a DEFINITION resolves
//! `<head>.name` before any unfolding — Lean's `resolveDotName`. The head
//! used to be read off the full `whnf`, so `Function.Injective (Pi.map f)`
//! (a `∀`-bodied def) lost its head and `.piMap` was unknown
//! (`Mathlib/Logic/Function/Basic.lean`, four rows, measured 2026-09-11).

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
fn test_dot_ident_resolves_against_a_definition_headed_expected_type() {
    let mut env = Environment::with_prelude();
    let src = "def IsZeroP (n : Nat) : Prop := n = 0\n\
               theorem IsZeroP.z : IsZeroP 0 := rfl\n\
               theorem useZ : IsZeroP 0 := .z\n\
               def AllZero (f : Nat → Nat) : Prop := ∀ n, IsZeroP (f n)\n\
               theorem AllZero.const : AllZero (fun _ => 0) := fun _ => .z\n\
               theorem useConst : AllZero (fun _ => 0) := .const\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`.z` / `.const` must resolve through the definition head: {e}");
    }
}

#[test]
fn test_dot_ident_still_resolves_constructors_of_inductives() {
    let mut env = Environment::with_prelude();
    let src = "def someNat : Option Nat := .some 3\n\
               def noneNat : Option Nat := .none\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("constructor dot-idents are unchanged: {e}");
    }
}

#[test]
fn test_dot_ident_as_application_head_uses_the_applications_expected_type() {
    let mut env = Environment::with_prelude();
    let src = "def IsZeroP (n : Nat) : Prop := n = 0\n\
               theorem IsZeroP.ofEq {n : Nat} (h : n = 0) : IsZeroP n := h\n\
               theorem useOfEq : IsZeroP 0 := .ofEq rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`.ofEq rfl` must resolve `IsZeroP.ofEq` from the application's expected type: {e}");
    }
}

#[test]
fn test_receiver_dot_notation_uses_the_head_constant_before_reducing() {
    let mut env = Environment::with_prelude();
    let src = "def IsZeroP (n : Nat) : Prop := n = 0\n\
               theorem IsZeroP.toEq {n : Nat} (h : IsZeroP n) : n = 0 := h\n\
               theorem useToEq {n : Nat} (h : IsZeroP n) : n = 0 := h.toEq\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`h.toEq` with `h : IsZeroP n` must resolve `IsZeroP.toEq`: {e}");
    }
}
