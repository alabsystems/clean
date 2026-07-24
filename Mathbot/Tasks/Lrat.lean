/-!
LRAT/FRAT-style unit-conflict replay toy.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Lrat

def positiveUnitSatisfied (assignment : Bool) : Prop :=
  assignment = true

def negativeUnitSatisfied (assignment : Bool) : Prop :=
  assignment = false

theorem lrat_unit_conflict_sound
    (assignment : Bool)
    (hpos : positiveUnitSatisfied assignment)
    (hneg : negativeUnitSatisfied assignment) :
    False := by
  cases assignment <;> simp [positiveUnitSatisfied, negativeUnitSatisfied] at hpos hneg

end Mathbot.Tasks.Lrat
