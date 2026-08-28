-- p06 — CLASS II, Proj sub-shape (9 of the 44 corpus entries, all Order/Basic).
--
-- PROVES: the same defect through a different reduction route. `MyLE.le a b`
-- whnf's to a projection out of an OPAQUE instance variable
-- (`Proj(MyLE, 0, Proj(MyPre, 0, FVar(FVarId(1))))`), which has no nameable
-- head either — so the pre-repair message dumped the projection spine.
-- Compare the corpus entry for `Mathlib.Tactic.LE.le.lt_iff_ne`:
-- `Proj(LE, 0, Proj(Preorder, 0, FVar(FVarId(1))))`. Same shape, three
-- declarations, no Mathlib.
--
-- CONTROL: p07 rules out "a projection-typed receiver cannot resolve dot
-- notation" — the identical receiver with a RESOLVABLE target passes.
class MyLE (α : Type) where
  le : α → α → Prop

class MyPre (α : Type) where
  toMyLE : MyLE α

instance instMyLEOfPre {α : Type} [p : MyPre α] : MyLE α := p.toMyLE

theorem probe_proj {α : Type} [MyPre α] {a b : α} (h : MyLE.le a b) : True :=
  h.nosuchfield
