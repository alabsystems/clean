prelude
import Init.SimpLemmas
namespace ImportedEquations
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | fork : Tree α → Tree α → Tree α
@[simp] def good : Tree α → Prop
  | .leaf _ => True
  | .fork a b => good a ∧ good b
-- Realize the same equation family Lean uses for `simp [good]` on import.
#check good.eq_1
#check good.eq_2
end ImportedEquations
