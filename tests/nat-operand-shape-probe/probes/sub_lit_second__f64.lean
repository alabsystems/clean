set_option maxHeartbeats 400000
set_option maxRecDepth 4096
--@ probe-expect: GRIND
theorem probe (x : Nat) : @Nat.rec (fun _ => Bool) Bool.false (fun _ _ => Bool.true) (Nat.sub x 9218868437227405312) = Bool.false := rfl
