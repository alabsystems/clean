-- p07 — CLASS II CONTROL (PASS). p06's resolvable twin.
--
-- PROVES: the two-level class-projection receiver p06 fails on resolves its dot
-- target when that target EXISTS — both when the instance in scope is the
-- derived `[MyPre α]` (the stuck `Proj(MyLE, 0, Proj(MyPre, 0, …))` spine) and
-- when it is the direct `[MyLE α]`.
--
-- RULES OUT: "the Proj sub-shape of class II is a distinct capability gap from
-- the Pi sub-shape." Both sub-shapes are the same thing: an unresolved target.
class MyLE (α : Type) where
  le : α → α → Prop

class MyPre (α : Type) where
  toMyLE : MyLE α

instance instMyLEOfPre {α : Type} [p : MyPre α] : MyLE α := p.toMyLE

theorem MyLE.le.self {α : Type} [MyLE α] {a b : α} (h : MyLE.le a b) : MyLE.le a b := h

theorem control_named {α : Type} [MyPre α] {a b : α} (h : MyLE.le a b) : MyLE.le a b :=
  MyLE.le.self h

theorem probe_dot_existing {α : Type} [MyPre α] {a b : α} (h : MyLE.le a b) : MyLE.le a b := h.self

theorem probe_dot_direct_inst {α : Type} [MyLE α] {a b : α} (h : MyLE.le a b) : MyLE.le a b := h.self
