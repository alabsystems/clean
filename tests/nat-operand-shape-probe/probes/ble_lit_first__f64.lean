set_option maxHeartbeats 400000
set_option maxRecDepth 4096
--@ probe-expect: STUCK-fast
theorem probe (x : Nat) : @Nat.rec (fun _ => Bool) Bool.false (fun _ _ => Bool.true) (Nat.pred (Nat.sub (Nat.succ Nat.zero) (Nat.pred (Nat.sub 9218868437227405312 x)))) = Bool.false := rfl
