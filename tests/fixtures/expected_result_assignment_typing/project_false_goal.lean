theorem projectBadGoal (a : Nat × Bool) (b : Nat × Nat)
    (h : (a.1, (0 : Nat)) = b) : a.1 = Nat.succ b.1 :=
  congrArg (fun p : Nat × Nat => p.1) h
