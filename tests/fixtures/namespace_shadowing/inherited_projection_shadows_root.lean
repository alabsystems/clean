-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- SRCELAB cluster C6 ("rigid head clash"), the dominant Pi-vs-FVar sub-cluster.
--
-- MINIMAL REPRO of the one defect that kills `Unique.eq_default`,
-- `Unique.default_eq`, `Unique.forall_iff` and `Unique.exists_iff` in
-- `Mathlib/Logic/Unique.lean` under `scripts/source_elab_gate.sh`.
--
-- `MyU extends Inhabited α` makes Clean materialize a DERIVED projection
--   `MyU.default : {α : Type u} → (self : MyU α) → α`
-- for the inherited field. Lean 4 declares no such constant: it composes
-- `Inhabited.default (MyU.toInhabited self)` on the fly at each use site
-- (`mkBaseProjections`, `src/Lean/Elab/App.lean`). Measured against the real
-- Lean 4 `Init` oleans (93,172 constants loaded), `Monad.toApplicative` EXISTS
-- while `Monad.pure` and `Applicative.pure` do NOT.
--
-- Because Clean's constant DOES exist it joins the current-namespace-outward
-- candidate set in `elab_ident`, so a bare `default` written inside
-- `namespace MyU` resolves to `MyU.default` and shadows the root/exported
-- `default` the author meant. The derived projection takes an EXPLICIT `self`
-- nobody supplied, so the term stays under-applied and carries a `Pi` type
-- where the field type belongs — a rigid head clash against whatever the
-- context expected.
--
-- Each pair below is the SAME theorem text inside and outside the namespace.
-- Before the fix the `MyU.*` half failed and the root half passed, verbatim:
--
--   MyU.inside: Type mismatch: expected Const(Name { depth: 1, suffix:
--   ["Nat"], ... }, []), got Pi(BinderData { info: Default, mult: Many },
--   App(Const(Name { depth: 1, suffix: ["MyU"], ... }, [Param(...)]),
--   FVar(FVarId(9223372036854775809))), FVar(FVarId(9223372036854775809)))
--   (cannot unify expressions of different shape: Discriminant(6) vs
--   Discriminant(3))
--
--   MyU.applied: Type mismatch: expected FVar(FVarId(0)), got cannot unify
--   expressions of different shape: Discriminant(6) vs Discriminant(1)
--
-- `MyU.applied`'s line is BYTE-IDENTICAL to the one `Unique.eq_default`,
-- `Unique.forall_iff` and `Unique.exists_iff` emit against real Mathlib.
-- `Discriminant(6)` is `ExprKind::Pi`, `Discriminant(1)` is `ExprKind::FVar`
-- and `Discriminant(3)` is `ExprKind::Const`
-- (`crates/clean-kernel/src/expr/kind.rs`); the `FVarId` with bit 63 set is a
-- metavariable (`MetaState::META_FVAR_TAG`), i.e. the projection's unsolved
-- `{α}`.
--
-- All four declarations must check.

universe u

structure MyU (α : Type u) extends Inhabited α where
  tag : Nat

theorem outside : (default : Nat) = (default : Nat) := rfl

theorem appliedRoot {β : Type u} [Inhabited β] (p : β → Prop) (h : p default) :
    p default := h

namespace MyU

theorem inside : (default : Nat) = (default : Nat) := rfl

theorem applied {β : Type u} [Inhabited β] (p : β → Prop) (h : p default) :
    p default := h

end MyU
