// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The TERM `⟨⟨a⟩, h⟩ : S` for `S extends P`: Lean's as-written reading.
//!
//! Lean's `elabAnonymousCtor` has no subobject flattening: when the argument
//! count equals the constructor's explicit field count it emits `ctor args`
//! (`Lean/Elab/BuiltinNotation.lean:43-100`), so the parent is written as its
//! own `⟨…⟩`. Clean's subobject regrouping fired on the same count whenever
//! every parent contributes one leaf and wrapped the nested `⟨a⟩` again —
//! measured 2026-09-20 on main at `5e2e6dc0e`: `⟨⟨a⟩, h⟩ : Unique' α` died
//! "Anonymous constructor ⟨⟩ expected inductive type, got fvar#0" (the next
//! wall of Mathlib's `unique_iff_existsUnique` and
//! `unique_subtype_iff_existsUnique`), and `⟨⟨1⟩, 2⟩ : B` "requires
//! single-constructor type, but Nat has 2 constructors".
//!
//! Every accepted fixture below elaborates as written on the pinned
//! v4.30.0-rc2 `lean` binary (2026-09-20, exit 0) — except the flat control,
//! which Lean REJECTS and Clean has always accepted; it is pinned here only so
//! that this change is seen to add a reading and remove none.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(src: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

fn accepts(src: &str, what: &str) {
    if let Some(e) = elab(src) {
        panic!("{what}: {e}");
    }
}

const UNIQUE: &str = "universe u\n\
     structure Unique' (α : Sort u) extends Inhabited α where\n\
     \x20 uniq : ∀ a : α, a = default\n";

/// The shape of `unique_iff_existsUnique`'s second half.
#[test]
fn test_anon_ctor_subobject_as_written_unique_shape_is_accepted() {
    let src = format!(
        "{UNIQUE}def mkU {{α : Sort u}} (a : α) (h : ∀ b : α, b = a) : Unique' α := ⟨⟨a⟩, h⟩\n\
         theorem uq_shape (α : Sort u) (a : α) (h : ∀ b : α, b = a) : Nonempty (Unique' α) :=\n\
         \x20 ⟨⟨⟨a⟩, fun _ ↦ h _⟩⟩\n"
    );
    accepts(&src, "`⟨⟨a⟩, h⟩ : Unique' α` is `Unique'.mk ⟨a⟩ h`");
}

/// The VALUES land in the fields they were written for.
#[test]
fn test_anon_ctor_subobject_as_written_values_reach_their_fields() {
    accepts(
        "structure A where\n\
         \x20 x : Nat\n\
         structure B extends A where\n\
         \x20 y : Nat\n\
         def b1 : B := ⟨⟨1⟩, 2⟩\n\
         theorem b1_x : b1.x = 1 := rfl\n\
         theorem b1_y : b1.y = 2 := rfl\n\
         structure A2 where\n\
         \x20 x : Nat\n\
         \x20 z : Nat\n\
         structure B2 extends A2 where\n\
         \x20 y : Nat\n\
         def b2 : B2 := ⟨⟨1, 3⟩, 2⟩\n\
         theorem b2_z : b2.z = 3 := rfl\n\
         theorem b2_y : b2.y = 2 := rfl\n",
        "a parent written as its own `⟨…⟩` fills the parent subobject",
    );
}

/// Control: the flat spelling Clean has always accepted (Lean rejects it:
/// the as-written reading fails, is rolled back, and the regrouped reading
/// runs exactly as before).
#[test]
fn test_anon_ctor_subobject_flat_spelling_is_still_accepted() {
    accepts(
        "structure A where\n\
         \x20 x : Nat\n\
         structure B extends A where\n\
         \x20 y : Nat\n\
         def bflat : B := ⟨1, 2⟩\n\
         theorem bflat_x : bflat.x = 1 := rfl\n\
         theorem bflat_y : bflat.y = 2 := rfl\n",
        "the regrouped reading still runs when the as-written one fails",
    );
}

/// A failed as-written attempt leaves nothing behind: an ill-typed literal is
/// still refused, by the regrouped reading's own error.
#[test]
fn test_anon_ctor_subobject_ill_typed_literal_is_refused() {
    let err = elab(
        "structure A where\n\
         \x20 x : Nat\n\
         structure B extends A where\n\
         \x20 y : Nat\n\
         def bbad : B := ⟨⟨true⟩, 2⟩\n",
    );
    assert!(err.is_some(), "`⟨⟨true⟩, 2⟩ : B` must be refused");
}
