// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalized field notation on a FUNCTION-typed receiver binds the receiver
//! at the first parameter whose TYPE is a function type, not at the first
//! EXPLICIT parameter.
//!
//! `Function.surjInv : {α} → {β} → {f : α → β} → Surjective f → β → α` has its
//! function parameter at the IMPLICIT `{f}`, so Lean's `addLValArg`
//! (`Lean/Elab/App.lean:1587-1626`, with `typeMatchesBaseName` for `Function`
//! spelled `(← whnf type).isForall` at :1564-1567) produces
//! `@Function.surjInv α β f hf x` — verified with `pp.explicit` on the pinned
//! v4.30.0-rc2 binary. Clean applied the receiver as the first EXPLICIT
//! argument, i.e. into the surjectivity slot, and `hf`/`x` then landed one slot
//! late: `Mathlib/Logic/Function/Basic.lean` `Function.comp_surjInv`.
//!
//! The transparency is the safety of the port: Lean runs that test under
//! `withReducibleAndInstances`, where a parameter typed `Surjective f` does
//! NOT read as a function. Clean's plain `whnf` is full-delta and unfolds it
//! to `∀ b, ∃ a, f a = b` — the fixture below would then match the PROOF
//! parameter and reproduce the same defect one step later.

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

/// `Surj` is a plain `def` (so it must stay folded at reducible-and-instances
/// transparency) and `sInv`'s function parameter is the implicit `{f}`.
const BASE: &str = "namespace Function\n\
                    def Surj {α : Type} {β : Type} (f : α → β) : Prop :=\n\
                    \x20 ∀ b : β, ∃ a : α, f a = b\n\
                    axiom sInv {α : Type} {β : Type} {f : α → β} (h : Surj f) (b : β) : α\n\
                    end Function\n";

#[test]
fn test_function_dot_notation_binds_the_receiver_at_the_implicit_function_slot() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}def viaDot {{α β : Type}} (f : α → β) (hf : Function.Surj f) (x : β) : α :=\n\
         \x20 f.sInv hf x\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`f.sInv hf x` must bind `f` to the implicit `{{f}}` slot: {e}");
    }
}

#[test]
fn test_spelled_out_control_still_elaborates() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}def spelled {{α β : Type}} (f : α → β) (hf : Function.Surj f) (x : β) : α :=\n\
         \x20 Function.sInv hf x\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the spelled-out control must stay green: {e}");
    }
}

#[test]
fn test_function_dot_notation_at_an_explicit_function_slot_still_elaborates() {
    // The shape the old rule got right — `Function.comp`-like, whose first
    // function-typed parameter IS its first explicit parameter. The new scan
    // must agree with the old rule there, not merely avoid crashing.
    let mut env = Environment::with_prelude();
    let src = "namespace Function\n\
               def cmp {α : Type} {β : Type} {γ : Type} (f : β → γ) (g : α → β) : α → γ :=\n\
               \x20 fun a => f (g a)\n\
               end Function\n\
               def viaDotComp {α β γ : Type} (f : β → γ) (g : α → β) : α → γ := f.cmp g\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`f.cmp g` must still apply `f` at its explicit slot: {e}");
    }
}
