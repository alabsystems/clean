section
variable (unused : Nat) (p : Prop) [Decidable p]
def prunedOwn (x : α) (hp : p) : α := by exact x
axiom prunedAxiomOwn (x : α) (y : β) (hp : p) : Nat
end
theorem prunedNamed : prunedOwn (p := True) (x := 3) (hp := True.intro) = 3 := rfl
noncomputable def prunedAxiomNamed : Nat := prunedAxiomOwn (p := True) (x := 3) (y := true) (hp := True.intro)
