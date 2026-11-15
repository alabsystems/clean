prelude
import Init.Prelude

/-! `@[implemented_by]` bindings whose target the builtin prelude of Clean types otherwise. -/

/-- Pinned Lean types `Nat.modCore` `Nat → Nat → Nat`; Clean's builtin prelude takes a fuel
argument first (`Nat → Nat → Nat → Nat`). -/
@[implemented_by Nat.modCore]
def modVia (x y : Nat) : Nat := Nat.add x y

/-- Pinned Lean types `instDecidableEqFin` `(n : Nat) → DecidableEq (Fin n)`; Clean's builtin
prelude holds it at the unfolded `(n : Nat) → (x y : Fin n) → Decidable (x = y)`. -/
@[implemented_by instDecidableEqFin]
def finEqVia (n : Nat) : DecidableEq (Fin n) := fun i j => instDecidableEqFin n i j

def finZero : Fin 1 := Fin.mk 0 Nat.le.refl

def finSelfEq (_ : Unit) : Bool := @decide (Eq finZero finZero) (finEqVia 1 finZero finZero)
