section
variable (unused : α → Prop)
def pruned (x : β) : β := by exact x
theorem prunedThm (x : β) : (by exact x = x) := by rfl
theorem prunedRec (x : β) : (by exact ∀ n : Nat, x = x)
 | 0 => rfl
 | n + 1 => by exact prunedRec x n
end
theorem usePruned : @pruned Nat 3 = 3 := rfl
theorem usePrunedThm : (3 : Nat) = 3 := @prunedThm Nat 3
theorem usePrunedRec : (3 : Nat) = 3 := @prunedRec Nat 3 2
