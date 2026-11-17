prelude
import Init.Prelude

namespace StablePlain
def successor (n : Nat) : Nat := Nat.succ n
theorem successor_zero : Eq (successor Nat.zero) (Nat.succ Nat.zero) := Eq.refl (Nat.succ Nat.zero)
end StablePlain
