-- P35 — the derived parent instance of a universe-polymorphic class actually
-- RESOLVES AND COMPUTES. Elaborating is not the same as working.
--
-- p33 pins that `class C (α : Type u) extends P α` elaborates. That alone would
-- be satisfied by a declaration that registers and is then unusable, which is
-- precisely the failure mode this ladder keeps finding (a green surface over a
-- capability no user can reach). So this probe uses the parent through the
-- child: `FSg.op` is resolved from an `[FMon α]` binder via the derived
-- `FMon.toFSg`, and the result is checked by `rfl`.
--
-- Measured equal to the monomorphic spelling — same 6/6 — so universe
-- polymorphism is now at parity here rather than merely "not erroring".
--
-- NOTE the explicit `toFSg := natFSg`. Omitting it fails with
-- `MissingStructureFields { struct_name: FSg, fields: ["op"] }` — but the
-- MONOMORPHIC spelling fails identically, so that is a pre-existing,
-- universe-independent gap in structure-literal parent synthesis, deliberately
-- out of scope here and not to be confused with the universe fix.
class FSg (α : Type u) where
  op : α → α → α

class FMon (α : Type u) extends FSg α where
  unit : α

instance natFSg : FSg Nat where
  op := Nat.add

instance natFMon : FMon Nat where
  toFSg := natFSg
  unit  := Nat.zero

def useParent {α : Type u} [FMon α] (x y : α) : α := FSg.op x y

theorem parent_resolves : useParent (2 : Nat) 3 = 5 := rfl
