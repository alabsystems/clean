-- P33 — universe-polymorphic `class ... extends`. FIXED 2026-08-14.
--
-- `class C (α : Type u) extends P α` is THE Mathlib idiom (the whole algebraic
-- and order hierarchy; Iris's OFE -> COFE -> BI tower). It used to fail
-- outright:
--
--   KernelCheckFailed { name: C.toP._deriveAdmissionProbe,
--                       detail: "Level count mismatch for C:
--                                declared 1 level params, got 0" }
--
-- CAUSE. `elab_class` synthesises a derived parent instance `C.toP` whose type
-- and value both reference `C` — the class being elaborated — via
-- `ElabCtx::mk_const`. `mk_const` resolves through the ENVIRONMENT
-- (`infer/elab_ctx.rs:323-332`), where the declaration is not registered yet,
-- so it took the not-found branch and emitted `Const(C, [])` with ZERO level
-- arguments. The monomorphic form passed only because zero is then correct.
--
-- FIX. `elab_structure` has already run by that point and its `ElabResult`
-- carries the structure's FINAL `universe_params` (declared, filtered to those
-- actually used). The finished instance type and value are now folded through
-- `FilterStructSelfLevels { struct_name, keep_params }` — exactly the treatment
-- `ctor_ty` and `projections` already receive and the derived parent instances
-- never did — and `DerivedInstance::level_params` is set to that same list.
--
-- TWO WRONG APPROACHES, measured and reverted before the right one; kept here
-- because each fails in an instructive way:
--   1. Fixing ONE of the two self-references (there are two: the instance TYPE
--      and the abstracted child class type) leaves the other failing
--      byte-identically — the output does not move AT ALL, which reads as
--      "wrong mechanism" when it is really "incomplete patch".
--   2. Hand-building the level list from `self.universe_params` turns
--      "got 0" into "got 3": it accumulates fresh universe metas minted during
--      field elaboration. `FilterStructSelfLevels`' own doc comment predicts
--      exactly this ("a DUPLICATED level slot `Struct.{u,u}`"), which is why
--      reusing it beats reconstructing the list.
--
-- p34 is the bounding control (`structure ... extends` at the same universes).
-- p35 pins the end-to-end behaviour: the derived parent instance RESOLVES and
-- COMPUTES, not merely elaborates.
--
-- STILL OPEN, distinct bug: the `Type _` hole spelling
-- (`class D (α : Type _) extends ...`) fails differently, with "Undefined
-- universe level parameter 'u_5'" — a hole-minted param leaking into the
-- derived instance. Not covered by this fix.
class P33Sg (α : Type u) where
  op : α → α → α

class P33Mon (α : Type u) extends P33Sg α where
  unit : α
