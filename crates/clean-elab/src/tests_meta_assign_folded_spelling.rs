// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A bare metavariable unified against a δ-reducible constant application is
//! assigned the term AS WRITTEN, not its unfolding.
//!
//! Lean's `isDefEqQuickOther` (`Lean/Meta/ExprDefEq.lean:1797`) hands the
//! opposite side to `processAssignment'` with no `whnf` on that path, so
//! `congrFun h a'` yields `Function.update f a' v a' = Function.update f a' v' a'`
//! with the constant intact and `rwa [update_self, update_self] at this`
//! rewrites it. Clean reduced first — `unify_app_args` only suppressed the
//! `whnf` for an `Irreducible` head — so the hypothesis came out as
//! `(fun x => dite …) a' = (fun x => dite …) a'` and the rewrite could not
//! find its pattern (`Function.update_injective`, Mathlib/Logic/Function/Basic:
//! "rewrite rule … did not match at hyp:this").
//!
//! Every fixture below was ground-truthed on the pinned v4.30.0-rc2 `lean`
//! binary (accepted there).

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

/// The prelude-only replica of `Function.update` / `Function.update_self`.
const UPD_PRELUDE: &str = "def upd {α : Type} {β : α → Type} [DecidableEq α]\n\
    \x20   (f : (a : α) → β a) (a' : α) (v : β a') : (a : α) → β a :=\n\
    \x20 fun a => dite (a = a') (fun h => h ▸ v) (fun _ => f a)\n\
    axiom upd_self {α : Type} {β : α → Type} [inst : DecidableEq α]\n\
    \x20   (f : (a : α) → β a) (a' : α) (v : β a') : upd f a' v a' = v\n";

/// The row itself: the `have` must keep `upd` FOLDED so the rewrite finds it.
#[test]
fn test_congr_fun_meta_assignment_keeps_the_constant_folded() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{UPD_PRELUDE}theorem updInjective {{α : Type}} {{β : α → Type}} [DecidableEq α]\n\
         \x20   (f : (a : α) → β a) (a' : α) (v v' : β a')\n\
         \x20   (h : upd f a' v = upd f a' v') : v = v' := by\n\
         \x20 have := congrFun h a'\n\
         \x20 rwa [upd_self, upd_self] at this\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`congrFun h a'` must assign `?f := upd f a' v` as written: {e}");
    }
}

/// The control that passed all along: an ASCRIBED `have` never poses the
/// bare-metavariable constraint, so it was never reduced. It must keep
/// passing — the fix may not change a path that already agreed with Lean.
#[test]
fn test_ascribed_have_keeps_the_constant_folded() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{UPD_PRELUDE}theorem updInjectiveAscribed {{α : Type}} {{β : α → Type}} [DecidableEq α]\n\
         \x20   (f : (a : α) → β a) (a' : α) (v v' : β a')\n\
         \x20   (h : upd f a' v = upd f a' v') : v = v' := by\n\
         \x20 have hh : upd f a' v a' = upd f a' v' a' := congrFun h a'\n\
         \x20 rwa [upd_self, upd_self] at hh\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the ascribed control must keep passing: {e}");
    }
}

/// The reduced comparison is still the FALLBACK: a bare metavariable facing a
/// constant application whose folded spelling does NOT unify must still
/// succeed through the δ-unfolded form. `natWrap` is a `def`, so the folded
/// `natWrap n` and the expected `Nat` shape agree only after unfolding.
///
/// `rewrite`, not `rw`: `rw`'s trailing `with_reducible rfl` closes the
/// reflexive main goal, so pinned Lean 4.8.0 refuses the `rw … at this; exact
/// this` spelling ("no goals to be solved") and accepts this one (integ/r5 fix
/// 2026-10-16, `regr/t11/RewriteAt.lean`).
#[test]
fn test_reduced_fallback_still_solves_a_folded_mismatch() {
    let mut env = Environment::with_prelude();
    let src = "def natWrap (n : Nat) : Nat := Nat.succ n\n\
               axiom natWrapEq (n : Nat) : natWrap n = Nat.succ n\n\
               theorem usesFallback (n : Nat) : Nat.succ n = Nat.succ n := by\n\
               \x20 have := natWrapEq n\n\
               \x20 rewrite [natWrap] at this\n\
               \x20 exact this\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the reduced comparison must remain reachable: {e}");
    }
}
