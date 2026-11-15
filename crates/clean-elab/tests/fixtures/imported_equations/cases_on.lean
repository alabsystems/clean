import ImportedEquations
open ImportedEquations
inductive J (p : β → Prop) (f : α → Option β) : Tree α → Prop where
  | leaf {a d} : f a = some d → p d → J p f (.leaf a)
  | fork (a b : Tree α) : J p f (.fork a b)
def Guard (p : β → Prop) (f : α → Option β) : Tree α → Prop
  | .leaf a => ∃ d, f a = some d ∧ p d
  | .fork _ _ => True
theorem checkGuard {p : β → Prop} {f : α → Option β} {e} (h : J p f e) : Guard p f e := by
  induction h <;> simp_all only [Guard]
  case leaf a d hf hp => exact ⟨d, rfl, hp⟩

theorem forkGuard (p : β → Prop) (f : α → Option β) (a b : Tree α) : Guard p f (.fork a b) := by
  simp only [Guard]
