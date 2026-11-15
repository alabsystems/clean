// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A ONE-element anonymous-constructor pattern `⟨x⟩` destructures the
//! scrutinee's sole constructor (Lean's `elabAnonymousCtor`,
//! `Lean/Elab/BuiltinNotation.lean:43-100`); it is never a parenthesis.
//!
//! Every accepted fixture elaborates as written on the pinned v4.30.0-rc2
//! `lean` binary (2026-09-12). The two refused fixtures are refused there:
//! `bad_prod` with "Insufficient number of fields for `⟨...⟩` constructor:
//! Constructor `Prod.mk` has 2 explicit field, but only 1 was provided", and
//! `bad_elim` with "recursor `Nonempty.casesOn` can only eliminate into
//! `Prop`".

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

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, src) {
        panic!("{what}: {e}");
    }
}

const AXIOMS: &str = "axiom congr_fun2 {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} \
                      (h : f = g) (a : α) : f a = g a\n\
                      axiom sselim {α : Sort _} (a b : α) : a = b\n";

/// `Function.const_injective` (Mathlib `Logic/Function/Basic.lean`):
/// `let ⟨x⟩ := ‹Nonempty α›; congr_fun h x`.
#[test]
fn test_anon_ctor_one_field_let_destructures_nonempty() {
    let src = format!(
        "{AXIOMS}theorem d7 {{α β : Sort _}} [Nonempty α] {{y₁ y₂ : β}} \
         (h : (fun _ : α => y₁) = (fun _ : α => y₂)) : y₁ = y₂ :=\n\
         \x20 let ⟨x⟩ := ‹Nonempty α›\n\
         \x20 congr_fun2 h x\n\
         theorem d22 {{α β : Sort _}} [na : Nonempty α] (f : α → β) : ∀ b, ∃ a, f a = b :=\n\
         \x20 fun _ ↦ let ⟨a⟩ := na; ⟨a, sselim _ _⟩\n"
    );
    accepts(&src, "`let ⟨x⟩ := h` must bind the Nonempty's witness");
}

#[test]
fn test_anon_ctor_one_field_match_fun_and_have() {
    let src = format!(
        "{AXIOMS}theorem d_match {{α β : Sort _}} [na : Nonempty α] (f : α → β) : \
         ∀ b, ∃ a, f a = b :=\n\
         \x20 fun _ ↦ match na with | ⟨a⟩ => ⟨a, sselim _ _⟩\n\
         theorem d_fun {{α : Sort _}} (p : α → Prop) (hp : ∀ a, p a) : Nonempty α → ∃ a, p a :=\n\
         \x20 fun ⟨x⟩ => ⟨x, hp x⟩\n\
         theorem d_have {{α : Sort _}} (p : α → Prop) (hp : ∀ a, p a) (h : Nonempty α) : \
         ∃ a, p a :=\n\
         \x20 have ⟨x⟩ := h\n\
         \x20 ⟨x, hp x⟩\n\
         theorem d_ctrl {{α β : Sort _}} [na : Nonempty α] (f : α → β) : ∀ b, ∃ a, f a = b :=\n\
         \x20 fun _ ↦ match na with | .intro a => ⟨a, sselim _ _⟩\n"
    );
    accepts(
        &src,
        "`⟨x⟩` in a match arm, a lambda binder and `have` must destructure",
    );
}

/// A one-field `Type`-valued structure, where the value is observable.
#[test]
fn test_anon_ctor_one_field_on_a_data_structure() {
    accepts(
        "structure Box (α : Type) where\n\
         \x20 val : α\n\
         theorem d_box {α : Type} (bx : Box α) (p : α → Prop) (h : ∀ a, p a) : ∃ a, p a :=\n\
         \x20 let ⟨a⟩ := bx; ⟨a, h a⟩\n\
         def box_fun : Box Nat → Nat := fun ⟨n⟩ => n + 1\n\
         theorem box_fun_val : box_fun ⟨2⟩ = 3 := rfl\n",
        "`fun ⟨n⟩` on a one-field structure must bind the field",
    );
}

const NESTED_ARGUMENT: &str = "def firstSome (x : Option (Nat × Nat)) : Nat :=\n\
                             \x20 match x with\n\
                             \x20 | some ⟨a, b⟩ => a\n\
                             \x20 | none => 0\n";

#[test]
fn test_anon_ctor_nested_match_argument_preserves_selected_field() {
    accepts(
        &format!(
            "{NESTED_ARGUMENT}\
             theorem firstSome_value : firstSome (some (3, 7)) = 3 := rfl\n\
             theorem firstSome_none : firstSome none = 0 := rfl\n"
        ),
        "a nested anonymous pattern must select the actual first field",
    );
}

#[test]
fn test_anon_ctor_nested_match_argument_refuses_wrong_selected_field() {
    let mut env = Environment::with_prelude();
    assert!(elab(&mut env, NESTED_ARGUMENT).is_none());
    assert!(
        elab(
            &mut env,
            "theorem firstSome_wrong : firstSome (some (3, 7)) = 7 := rfl\n",
        )
        .is_some(),
        "the second field must not satisfy the theorem about the first field"
    );
}

/// `rintro ⟨x⟩`, `obtain ⟨x⟩ := h` and `rcases h with ⟨x⟩` on `Nonempty`.
#[test]
fn test_anon_ctor_one_field_tactic_patterns_destructure_nonempty() {
    accepts(
        "theorem t_rintro {α : Sort _} (p : α → Prop) (hp : ∀ a, p a) : \
         Nonempty α → ∃ a, p a := by\n\
         \x20 rintro ⟨x⟩\n\
         \x20 exact ⟨x, hp x⟩\n\
         theorem t_obtain {α : Sort _} (p : α → Prop) (hp : ∀ a, p a) (h : Nonempty α) : \
         ∃ a, p a := by\n\
         \x20 obtain ⟨x⟩ := h\n\
         \x20 exact ⟨x, hp x⟩\n\
         theorem t_rcases {α : Sort _} (p : α → Prop) (hp : ∀ a, p a) (h : Nonempty α) : \
         ∃ a, p a := by\n\
         \x20 rcases h with ⟨x⟩\n\
         \x20 exact ⟨x, hp x⟩\n",
        "a tactic `⟨x⟩` pattern must destructure `Nonempty`",
    );
}

/// A one-element `(a)` is still a parenthesis.
#[test]
fn test_anon_ctor_one_field_paren_let_stays_a_plain_let() {
    accepts(
        "def paren_let (n : Nat) : Nat := let (a) := n; a + 1\n\
         theorem paren_let_val : paren_let 2 = 3 := rfl\n",
        "`let (a) := n` binds `a := n`",
    );
}

/// Fail-closed: `⟨a⟩` supplies one field where `Prod.mk` has two.
#[test]
fn test_anon_ctor_one_field_refuses_a_two_field_constructor() {
    let mut env = Environment::with_prelude();
    assert!(
        elab(&mut env, "def bad_prod : Nat × Nat → Nat := fun ⟨a⟩ => a\n").is_some(),
        "`⟨a⟩` must not destructure a two-field `Prod`"
    );
}

/// Fail-closed: `Nonempty` eliminates only into `Prop`.
#[test]
fn test_anon_ctor_one_field_refuses_large_elimination_of_nonempty() {
    let mut env = Environment::with_prelude();
    assert!(
        elab(
            &mut env,
            "def bad_elim (h : Nonempty Nat) : Nat := let ⟨x⟩ := h; x\n"
        )
        .is_some(),
        "a `Nonempty` witness must not escape into `Nat`"
    );
}
