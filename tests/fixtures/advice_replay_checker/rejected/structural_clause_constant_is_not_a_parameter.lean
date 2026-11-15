def bad : Nat → Nat → Nat
  | _, 0 => 0
  | tag, n + 1 => bad tag n
termination_by structural tag _ => 0
