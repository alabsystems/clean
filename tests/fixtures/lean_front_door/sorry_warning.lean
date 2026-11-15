-- An explicit `sorry` is Lean's warning, not an error: exit 0.
theorem t : 1 = 1 := sorry

example : True := sorry

namespace N
def q : Nat := sorry
end N
