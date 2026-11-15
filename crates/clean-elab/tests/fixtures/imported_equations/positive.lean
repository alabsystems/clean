import ImportedEquations
open ImportedEquations

theorem explicit_equations {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) :
    good (.fork a b) := by
  simp only [good, ha, hb, and_self]

theorem registered_equations {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) :
    good (.fork a b) := by
  simp [ha, hb, and_self]

theorem readd_equations {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) :
    good (.fork a b) := by
  simp only [-good.eq_2, good, ha, hb, and_self]
