// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An explicit `_` handed to an instance-implicit binder (`@f α _`) is
//! synthesized by typeclass resolution, as Lean does; it used to be a plain
//! metavariable nothing solved, so `rfl` about `@default _ _` reached the
//! kernel with the instance unassigned (`Pi.default_def` in
//! `Mathlib/Logic/Unique.lean`, measured 2026-09-11).

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
fn test_explicit_hole_at_instance_binder_is_synthesized() {
    let mut env = Environment::with_prelude();
    let src = "class HasD (α : Type) where\n  d : α\n\
               instance instHasDNat : HasD Nat := ⟨7⟩\n\
               theorem dNat : @HasD.d Nat _ = 7 := rfl\n\
               def dOf (α : Type) [HasD α] : α := @HasD.d α _\n\
               theorem dOfNat : dOf Nat = 7 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`_` at an instance-implicit binder must be synthesized: {e}");
    }
}
