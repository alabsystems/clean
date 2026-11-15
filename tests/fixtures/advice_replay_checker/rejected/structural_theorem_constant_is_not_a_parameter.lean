theorem prop : Nat → True
  | 0 => True.intro
  | n + 1 => prop n
termination_by structural _ => 0
