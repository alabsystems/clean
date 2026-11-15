prelude
import Init.Core

/-!
# `ReplayHonestDepNestedDeep` — `Lean.Json`'s nesting shape, compiled by the pinned Lean

A module SOURCE (`lean -o`; Lean's kernel checks it). `Lean.Json` nests through
`Std.TreeMap.Raw`, then `Std.DTreeMap.Raw`, then the RECURSIVE dependent container
`Std.DTreeMap.Internal.Impl` (pinned Lean: `numNested = 5`, every recursor carrying the β-redex
the const map `fun _ => Json` leaves). `RJ` has that shape in small: a structure `DR` over the
recursive dependent container `DM`, instantiated with the const map `fun _ => β`.
`ReplayHonestDepNested`'s blocks nest once, through non-recursive containers.
-/

inductive DM (α : Type) (β : α → Type) where
  | leaf
  | node (k : α) (v : β k) (l r : DM α β)

structure DR (β : Type) where
  m : DM Nat (fun _ => β)

inductive RJ where
  | leaf
  | obj (r : DR RJ)

def honest_rj_obj : RJ := RJ.obj ⟨DM.node 0 RJ.leaf DM.leaf DM.leaf⟩

theorem honest_rj_ne : RJ.obj ⟨DM.leaf⟩ ≠ RJ.leaf := fun h => RJ.noConfusion h
