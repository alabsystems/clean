def bad : Nat → Nat
  | 0 => 0
  | n + 1 => bad n
termination_by structural _ => «_»
