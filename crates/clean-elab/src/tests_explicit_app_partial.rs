// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@f a …` is a genuine PARTIAL application whatever expected type it meets.
//!
//! `elab_app` sets `explicit_mode` only for the duration of `elab_app_inner`,
//! and the `@`-ness did not travel with the produced value: once `elab_app`
//! returned, `apply_implicit_to_expected_type` reconciled the value with the
//! enclosing expected type and filled every remaining LEADING implicit and
//! instance-implicit binder. So `@D.toC α` came back as `C α` where
//! `D α → C α` was written, and `Function.Injective (@PartialOrder.toPreorder
//! α)` (`Mathlib/Order/Basic.lean`) received `Preorder α` instead of
//! `PartialOrder α → Preorder α`.
//!
//! Lean carries `explicit` in the `ElabAppArgs` state and never reaches
//! `addImplicitArg`/`processImplicitArg` while it is set; `finalize` ends the
//! application with the remaining binders INTACT and `ensureHasType` then does
//! a plain `isDefEq`. Every fixture below is accepted by the pinned
//! v4.30.0-rc2 `lean` binary (the diagnosis's own replicas needed
//! `noncomputable` to reach exit 0; these are `Prop`/`Type`-valued and do not).

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

/// A class `C` with a field, a class `D` extending it, a plain structure `F`
/// extending a plain structure `E` (the non-class control, whose remaining
/// binder is EXPLICIT), and two functions with trailing implicit binders.
const BASE: &str = "class C (α : Type) where\n\
                    \x20 v : Nat\n\
                    class D (α : Type) extends C α where\n\
                    \x20 w : Nat\n\
                    structure E (α : Type) where\n\
                    \x20 e : Nat\n\
                    structure F (α : Type) extends E α where\n\
                    \x20 f : Nat\n\
                    def foo {α : Type} [C α] (n : Nat) : Nat := n\n\
                    def bar {α : Type} {β : Type} (n : Nat) : Nat := n\n";

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
fn test_explicit_app_keeps_a_trailing_instance_binder_unfilled() {
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}def ck1 (α : Type) : D α → C α := @D.toC α\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@D.toC α` must keep its `[D α]` binder unfilled: {e}");
    }
}

#[test]
fn test_explicit_app_keeps_a_trailing_instance_binder_before_an_explicit_one() {
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}def ck6 (α : Type) : C α → Nat → Nat := @foo α\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@foo α` must keep `[C α]` and `(n : Nat)` unfilled: {e}");
    }
}

#[test]
fn test_explicit_app_keeps_an_ordinary_trailing_implicit_unfilled() {
    let mut env = Environment::with_prelude();
    let src = format!("{BASE}def ckA (α : Type) : Type → Nat → Nat := @bar α\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@bar α` must keep its `{{β}}` binder unfilled: {e}");
    }
}

#[test]
fn test_explicit_app_stays_partial_in_an_argument_slot() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{BASE}def use2 (g : Type → Nat → Nat) : Nat := g Nat 0\n\
         def ckD (α : Type) : Nat := use2 (@bar α)\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`@bar α` in an argument slot must stay partial: {e}");
    }
}

#[test]
fn test_non_class_structure_parent_projection_control_still_elaborates() {
    let mut env = Environment::with_prelude();
    // The control that isolated the class: `F.toE`'s remaining binder is
    // EXPLICIT, so nothing was ever inserted for it and this always passed.
    let src = format!("{BASE}def ck4 (α : Type) : F α → E α := @F.toE α\n");
    if let Some(e) = elab(&mut env, &src) {
        panic!("the explicit-binder control must stay green: {e}");
    }
}

#[test]
fn test_fully_applied_explicit_app_still_elaborates() {
    let mut env = Environment::with_prelude();
    // `@f a b c` that fills every binder never reached the insertion path and
    // must be byte-identical.
    let src = format!(
        "{BASE}def ck10 (α : Type) (inst : C α) : Nat := @foo α inst 3\n\
         def ck11 (α : Type) (β : Type) : Nat := @bar α β 3\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("a fully applied `@f a b c` must stay green: {e}");
    }
}

#[test]
fn test_implicit_insertion_without_the_at_marker_still_runs() {
    let mut env = Environment::with_prelude();
    // The opposite direction must keep running: with no `@`, a polymorphic head
    // meeting a non-Pi expected type still has its implicits inserted. `α`
    // is named: a bare `foo 3` leaves `C ?α` with nothing to pin `?α`, which
    // both pinned Lean binaries refuse ("typeclass instance problem is
    // stuck") and Clean now refuses too instead of taking the one instance.
    let src = format!(
        "{BASE}instance instCNat : C Nat where\n\
         \x20 v := 0\n\
         def ck12 : Nat := foo (α := Nat) 3\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("implicit insertion without `@` must keep running: {e}");
    }
}

/// An `optParam` binder is left INTACT by `@` exactly as an implicit one is.
///
/// Ground truth, pinned v4.30.0-rc2: `#check @withOpt 1` prints
/// `optParam Nat 5 → Nat`, and `def t : Nat := @withOpt 1` is
/// "Type mismatch … has type optParam Nat 5 → Nat but is expected to have type
/// Nat". The `autoParam` twin behaves identically (`@withAuto 1 : autoParam
/// (1 = 1) … → Nat`). Lean never reaches the default while
/// `ElabAppArgs.explicit` is set, so the same flag that stops implicit
/// insertion must stop this one.
///
/// The fixture reaches Clean's `optParam` arm through a constant whose LAST
/// COMPONENT is `optParam` (`opt_param_default` matches on that), because
/// Clean's builtin prelude has no `optParam` and a source-level `(b : Nat := 5)`
/// does not produce one. The second declaration is the control that isolates
/// the `@` gate: without the marker the default is still supplied, which is
/// what this test holds fixed while the `@` half changes.
#[test]
fn test_explicit_app_keeps_a_trailing_opt_param_unfilled() {
    let mut env = Environment::with_prelude();
    let shim = "namespace Shim\n\
                def optParam (α : Type) (d : α) : Type := α\n\
                end Shim\n\
                axiom oc : (a : Nat) → Shim.optParam Nat 5 → Nat\n";
    let refused = elab(&mut env, &format!("{shim}def ckOptAt : Nat := @oc 1\n"));
    assert!(
        refused.is_some(),
        "`@oc 1` must keep its `optParam` binder unfilled, as Lean does"
    );

    let mut env2 = Environment::with_prelude();
    if let Some(e) = elab(&mut env2, &format!("{shim}def ckOptPlain : Nat := oc 1\n")) {
        panic!("the no-`@` control must still supply the default: {e}");
    }
}
