def choose (first : Option Nat) (next : Nat → Option Nat) (last : Option Nat) : Nat :=
  match first with
  | none => 1
  | some x =>
    match next x with
    | none => 2
    | some _ =>
      match last with
      | none => 3
      | some _ => 4

theorem afterThreeLookups (view : Nat → Nat) (first : Option Nat)
    (next : Nat → Option Nat) (last : Option Nat) (x y : Nat)
    (hx : first = some x) (hy : next x = some y) (hz : last = none) :
    view (choose first next last) = view 3 := by
  unfold choose
  simp only [hx, hy, hz]
