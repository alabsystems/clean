// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The type-less ascription `(e :)` (Lean's `typeAscription` with the type
//! omitted, `Lean/Parser/Term.lean:182-183`): `e` is elaborated with no
//! expected type and then checked against the context's type.
//!
//! Ground-truthed on the pinned v4.30.0-rc2 `lean` binary (2026-09-12): the
//! accepted fixtures elaborate there as written, and `bad` is refused there
//! ("Type mismatch … h has type a = 1 but is expected to have type a = 2").

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
fn test_ascription_without_type_checks_against_the_context() {
    let mut env = Environment::with_prelude();
    let src = "theorem t1 (a : Nat) (h : a = 1) : a = 1 := (h :)\n\
               theorem sym (a b : Nat) (h : a = b) : b = a := (h.symm :)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`(e :)` must elaborate `e` and check it against the context: {e}");
    }
}

/// `Function.Injective2.left'` (Mathlib `Logic/Function/Basic.lean:983`):
/// `hf.left b <| (congr_fun h b :)`, with the row's `Nonempty` destructure
/// replaced by an explicit `b` (that is a separate class).
#[test]
fn test_ascription_without_type_in_pipe_argument() {
    let mut env = Environment::with_prelude();
    let src = "universe u v w\n\
               variable {α : Sort u} {β : Sort v} {γ : Sort w}\n\
               def Inj (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
               def Inj2 (f : α → β → γ) : Prop := \
               ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂\n\
               theorem Inj2.left {f : α → β → γ} (hf : Inj2 f) (b : β) : \
               Inj fun a => f a b := fun _ _ h => (hf h).left\n\
               theorem left_row (f : α → β → γ) (hf : Inj2 f) (b : β) : Inj f := \
               fun _ _ h =>\n\
               \x20 hf.left b <| (congrFun h b :)\n\
               theorem ctl_hole (f : α → β → γ) (hf : Inj2 f) (b : β) : Inj f := \
               fun _ _ h =>\n\
               \x20 hf.left b <| (congrFun h b : _)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`(congrFun h b :)` must parse and elaborate as in Lean: {e}");
    }
}

/// Soundness: the context's type is still enforced after `e` is elaborated
/// on its own.
#[test]
fn test_ascription_without_type_still_rejects_a_mismatch() {
    let mut env = Environment::with_prelude();
    let src = "theorem bad (a : Nat) (h : a = 1) : a = 2 := (h :)\n";
    assert!(
        elab(&mut env, src).is_some(),
        "`(h :)` with `h : a = 1` must not prove `a = 2`"
    );
}

/// The whole row: `Function.Injective2.left'` destructures the `Nonempty`
/// instance with a one-element `⟨b⟩` and then pipes into `(… :)` — the
/// type-less ascription and the one-field anonymous-constructor pattern
/// together, as Mathlib writes it.
#[test]
fn test_ascription_without_type_row_with_nonempty_destructure() {
    let mut env = Environment::with_prelude();
    let src = "universe u v w\n\
               variable {α : Sort u} {β : Sort v} {γ : Sort w}\n\
               def Inj (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
               def Inj2 (f : α → β → γ) : Prop := \
               ∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂\n\
               theorem Inj2.left {f : α → β → γ} (hf : Inj2 f) (b : β) : \
               Inj fun a => f a b := fun _ _ h => (hf h).left\n\
               theorem Inj2.left' {f : α → β → γ} (hf : Inj2 f) [Nonempty β] : Inj f := \
               fun _ _ h =>\n\
               \x20 let ⟨b⟩ := ‹Nonempty β›\n\
               \x20 hf.left b <| (congrFun h b :)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the `Injective2.left'` shape must elaborate as in Lean: {e}");
    }
}
