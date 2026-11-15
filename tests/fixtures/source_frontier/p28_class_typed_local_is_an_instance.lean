-- p28 — CLASS I, the LOCAL side: a local is an INSTANCE because of its TYPE,
-- not because of its binder brackets.
--
-- PROVES: Lean's rule (`Lean.Meta.withNewLocalInstances`, keyed on `isClass?`
-- of the local's type) — any local whose type is a class is a local
-- instance, whatever its annotation. `{_ : Cls α}`, `{inst : Cls α}` and
-- `(h : Cls α)` all make `Cls.x` synthesizable, exactly like `[Cls α]`.
--
-- MEASURED at HEAD 88b9b8ee4 (2026-09-10, before the change): 2 passed,
-- 4 failed — every non-bracket spelling died
-- `failed to synthesize instance Cls for goal Cls fvar#0` with the instance
-- sitting in the local context, because only `BinderInfo::InstImplicit`
-- binders were ever pushed as local instances (seven push sites, one rule).
-- Ground truth, pinned `lean` v4.30.0-rc2 on this exact file: accepted, no
-- diagnostics.
--
-- IN-FILE CONTROL (`viaInst`): the bracket spelling, passing before and
-- after — so what moved is which LOCALS count, not resolution itself.
--
-- WHY IT MATTERS: Mathlib writes the implicit spelling routinely.
-- `Mathlib/Logic/Unique.lean` has `uniqueElim_default {_ : Unique ι}` and
-- `uniqueElim_const {β : Sort*} {_ : Unique ι}`, both failing in the pinned
-- slice as `failed to synthesize instance Inhabited` — the `Unique ι` local
-- that would supply it was never a local instance.
class Cls (α : Type u) where
  x : α

def viaInst {α : Type u} [Cls α] : α := Cls.x

def viaImplicit {α : Type u} {_ : Cls α} : α := Cls.x

def viaExplicit {α : Type u} (h : Cls α) : α := Cls.x

def viaNamedImplicit {α : Type u} {inst : Cls α} : α := Cls.x

theorem viaImplicitThm {α : Type u} {_ : Cls α} : (Cls.x : α) = Cls.x := rfl
