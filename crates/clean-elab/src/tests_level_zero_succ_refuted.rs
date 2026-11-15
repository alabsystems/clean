// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `0 =?= succ ?u` is refuted, never postponed — Lean's `solve`
//! (`Lean/Meta/LevelDefEq.lean`: `| Level.zero, Level.succ .. => return
//! LBool.false`). Every fixture was ground-truthed on the pinned v4.30.0-rc2
//! `lean` binary (2026-09-12); Lean registers `Fn2.partialInv` at
//! `{α : Type u_1} → {β : Sort u_2}`.

use crate::test_support::file_verdicts::{assert_all_accepted, run_file, verdict_of};
use crate::unify::level_solve::solve_level_eq;
use crate::unify::{MetaState, UnifyResult};
use clean_kernel::{Level, Name};

/// `Mathlib/Logic/Function/Basic.lean`'s `Function.partialInv {α β}`: the
/// Prop-only `exists_prop_decidable` (`Exists.{0}`) is tried for
/// `Decidable (∃ a, f a = b)` while `Option α` has forced `α : Sort (succ ?u)`.
/// Its level check `0 =?= succ ?u` used to be postponed (accepted), the
/// candidate was committed, and the declaration died at the boundary drain
/// with `unresolved universe level equation after postponement: Zero =?=
/// Succ(?u_4)`. `Fn3` (an explicit `Type u`) is the control that always
/// passed; `Fn4` (`Type _`) failed the same way as `Fn2`.
#[test]
fn test_level_zero_succ_prop_only_instance_is_skipped_at_type_carrier() {
    let src = "universe u v\n\
               axiom chooseX {α : Sort u} {p : α → Prop} (h : Exists p) : α\n\
               axiom propDec (p : Prop) : Decidable p\n\
               attribute [instance 10] propDec\n\
               axiom exists_prop_decidable' {p : Prop} (P : p → Prop) [Decidable p]\n\
               \x20   [∀ h, Decidable (P h)] : Decidable (∃ h, P h)\n\
               attribute [instance] exists_prop_decidable'\n\
               namespace Fn2\n\
               noncomputable def partialInv {α β} (f : α → β) (b : β) : Option α :=\n\
               \x20 if h : ∃ a, f a = b then some (chooseX h) else none\n\
               end Fn2\n\
               namespace Fn3\n\
               noncomputable def partialInv {α : Type u} {β : Sort v} (f : α → β) (b : β) :\n\
               \x20   Option α :=\n\
               \x20 if h : ∃ a, f a = b then some (chooseX h) else none\n\
               end Fn3\n\
               namespace Fn4\n\
               noncomputable def partialInv {α : Type _} {β} (f : α → β) (b : β) : Option α :=\n\
               \x20 if h : ∃ a, f a = b then some (chooseX h) else none\n\
               end Fn4\n";
    let verdicts = run_file(src);
    for name in ["Fn2.partialInv", "Fn3.partialInv", "Fn4.partialInv"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: the Prop-only candidate must fail its level check: {e}");
        }
    }
    assert_all_accepted(&verdicts, "the whole fixture elaborates in Lean");
}

/// The solver itself: `0 =?= succ ?u` and `succ ?u =?= 0` fail with the
/// metavariable unassigned and nothing postponed; `0 =?= ?u` still assigns.
#[test]
fn test_level_zero_succ_solver_refuses_both_orientations() {
    let mut metas = MetaState::new();
    let meta = Level::param(Name::from_string("?u_7"));
    let succ = Level::succ(meta.clone());
    for (l, r) in [(Level::zero(), succ.clone()), (succ.clone(), Level::zero())] {
        match solve_level_eq(&mut metas, &l, &r) {
            UnifyResult::Failure(_) => {}
            other => panic!("`{l} =?= {r}` must be refuted, got {other:?}"),
        }
    }
    assert_eq!(
        metas.instantiate_level(&meta),
        meta,
        "a refuted equation must not assign its metavariable"
    );
    assert!(
        metas.drain_postponed_levels().is_ok(),
        "a refuted equation must not be left postponed"
    );
    assert!(
        matches!(
            solve_level_eq(&mut metas, &Level::zero(), &meta),
            UnifyResult::Success
        ),
        "`0 =?= ?u` is still solvable"
    );
    assert_eq!(metas.instantiate_level(&meta), Level::zero());
}
