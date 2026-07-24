/-!
QBF strategy replay toy.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Qbf

def equalityMatrix (x y : Bool) : Prop :=
  x = y

def copycatStrategy (x : Bool) : Bool :=
  x

theorem qbf_copycat_strategy_replay :
    ∀ x, equalityMatrix x (copycatStrategy x) := by
  intro x
  cases x <;> rfl

end Mathbot.Tasks.Qbf
