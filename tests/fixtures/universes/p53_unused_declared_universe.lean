-- P53 — `universe u v w` declares NAMES; a declaration's level parameters
-- are the ones that OCCUR in it (Lean's `collectLevelParams`), never the
-- whole declared list. Added 2026-09-10.
--
-- MEASURED BEFORE the change (release binary, builtin prelude): 4 passed,
-- 2 failed — `useIt` and `clsThm2` both died at the KERNEL with
--   Type mismatch: expected Cls fvar#N, got Cls fvar#N
-- ("both sides print identically; they differ in universe levels"), because
-- `Cls` had been registered as `Cls.{u, v, w}` and each `[Cls α]` binder then
-- minted two level metavariables (`?v`, `?w`) that nothing in the declaration
-- could ever constrain — the body's `Cls.le`/`Cls.x` minted two more, and the
-- kernel saw the pairs disagree. CONTROLS, measured the same day, both
-- 6 passed / 0 failed: the same file with `universe u` alone, and with every
-- `Type u` spelled `Type*`. So the ONLY variable is the unused declared names.
--
-- The shape is Mathlib's: `Mathlib/Logic/Unique.lean` opens with
-- `universe u v w` and declares `structure Unique (α : Sort u)`, so every
-- `[Unique α]` binder in that file took this defect;
-- `Mathlib/Logic/Function/Basic.lean` opens with `universe u v w x`.
--
-- `defOnly` and `thmViaDef` are the in-file controls that pass before and
-- after: a plain `def`/`theorem` carrying an unused universe parameter never
-- reached the kernel with a metavariable, because no instance binder is
-- involved — which is why this class hid behind classes only.
universe u v w

class Cls (α : Type u) where
  x : α
  le : α → α → Prop

instance natCls : Cls Nat where
  x := 0
  le a b := a = b

def useIt (α : Type u) [Cls α] (a b : α) : Prop := Cls.le a b

theorem clsThm2 (α : Type u) [Cls α] : (Cls.x : α) = Cls.x := rfl

def defOnly (α : Type u) (a : α) : α := a

theorem thmViaDef (α : Type u) (a : α) : defOnly α a = a := rfl
