/- The list decreases, but the explicit Nat major is unchanged.
Both functions would be structurally admissible on the list if hints were ignored. -/
mutual
def f : Nat → List Nat → Nat
  | _, [] => 0
  | n, _ :: xs => g n xs
termination_by structural fuel _ => fuel
def g : Nat → List Nat → Nat
  | _, [] => 0
  | n, _ :: xs => f n xs
termination_by structural fuel _ => fuel
end
