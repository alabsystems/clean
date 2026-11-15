// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A NESTED constructor pattern under a DEPENDENT motive.
//!
//! When a match's expected type mentions its discriminant, the minor of
//! `ctor f₀ … fₙ` has the type `R[discriminant := ctor f₀ … fₙ]`. The
//! column-split lowering (`compile_ctor_field_column_split`) elaborated the
//! field match against the UNREFINED type, so the inner `casesOn`'s motive
//! kept naming the discriminant and the kernel refused the minor — measured
//! 2026-09-20 on main at `5e2e6dc0e` ("expected … (fun x1 : Unique' α => x1 =
//! x1 → True) (Unique'.mk α x f), got … (fun x1 : Inhabited α => fvar#4 =
//! fvar#4 → True) x"). It is the shape of Mathlib's
//! `Unique.subsingleton_unique'` (`Logic/Unique.lean`).
//!
//! Every fixture elaborates as written on the pinned v4.30.0-rc2 `lean`
//! binary (2026-09-20, exit 0).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            panic!("{what}: {e:?}");
        }
    }
}

const UNIQUE: &str = "universe u\n\
     structure Unique' (α : Sort u) extends Inhabited α where\n\
     \x20 uniq : ∀ a : α, a = default\n";

/// One discriminant, a named nested constructor, a codomain that mentions
/// the discriminant.
#[test]
fn test_nested_ctor_dependent_motive_one_discriminant_is_accepted() {
    let src = format!(
        "{UNIQUE}theorem ss_one {{α : Sort u}} : ∀ h₁ : Unique' α, h₁ = h₁ → True :=\n\
         \x20 fun d0 => match d0 with\n\
         \x20   | Unique'.mk (Inhabited.mk _) _ => fun _ => True.intro\n"
    );
    accepts(&src, "a nested constructor under a dependent motive");
}

/// Two discriminants destructured one after the other; the second match's
/// codomain mentions both.
#[test]
fn test_nested_ctor_dependent_motive_two_discriminants_is_accepted() {
    let src = format!(
        "{UNIQUE}theorem ss_named {{α : Sort u}} : ∀ h₁ h₂ : Unique' α, h₁ = h₂ → True :=\n\
         \x20 fun d0 => match d0 with\n\
         \x20   | Unique'.mk (Inhabited.mk _) _ => fun d1 => match d1 with\n\
         \x20     | Unique'.mk (Inhabited.mk _) _ => fun _ => True.intro\n\
         theorem ss_anon {{α : Sort u}} : ∀ h₁ h₂ : Unique' α, h₁ = h₂ → True :=\n\
         \x20 fun d0 => match d0 with\n\
         \x20   | ⟨Inhabited.mk _, _⟩ => fun d1 => match d1 with\n\
         \x20     | ⟨Inhabited.mk _, _⟩ => fun _ => True.intro\n"
    );
    accepts(&src, "two nested destructures under a dependent motive");
}

/// Control: the refined type is USED — the body is `rfl` at the constructor
/// value, which only type-checks when the arm's expected type was refined.
#[test]
fn test_nested_ctor_dependent_motive_body_sees_the_refined_type() {
    accepts(
        "structure In where\n\
         \x20 n : Nat\n\
         structure Out where\n\
         \x20 i : In\n\
         \x20 k : Nat\n\
         theorem out_eta : ∀ o : Out, o = Out.mk (In.mk o.i.n) o.k :=\n\
         \x20 fun o => match o with\n\
         \x20   | Out.mk (In.mk _) _ => rfl\n",
        "the arm body is checked against the refined type",
    );
}
