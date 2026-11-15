def outer (n : Nat) : Nat := go n
where
  go : Nat → Nat
    | 0 => 0
    | k + 1 => go k
  termination_by structural _ => 0
