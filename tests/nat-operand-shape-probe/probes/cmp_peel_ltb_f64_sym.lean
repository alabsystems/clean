set_option maxHeartbeats 400000
set_option maxRecDepth 4096
-- The spec's comparison vocabulary (crates/clean-verify/src/spec/core_spec/eval_ir_state.rs, 2026-09-08), mirrored over Lean's Nat.
def ir_nat_pos (n : Nat) : Bool := @Nat.rec (fun _ => Bool) Bool.false (fun _ _ => Bool.true) n
def ir_nat_iszero (n : Nat) : Bool := @Nat.rec (fun _ => Bool) Bool.true (fun _ _ => Bool.false) n
def ir_nat_sub_ltb (a b : Nat) : Bool := ir_nat_pos (Nat.sub b a)
def ir_nat_sub_eqb (a b : Nat) : Bool := @Bool.rec (fun _ => Bool) Bool.false (ir_nat_iszero (Nat.sub b a)) (ir_nat_iszero (Nat.sub a b))
def ir_nat_ltb (a b : Nat) : Bool := @Nat.rec (fun _ => Nat -> Bool) (fun y => ir_nat_pos y) (fun ap _ => fun y => @Nat.rec (fun _ => Bool) Bool.false (fun yp _ => ir_nat_sub_ltb ap yp) y) a b
def ir_nat_eqb (a b : Nat) : Bool := @Nat.rec (fun _ => Nat -> Bool) (fun y => ir_nat_iszero y) (fun ap _ => fun y => @Nat.rec (fun _ => Bool) Bool.false (fun yp _ => ir_nat_sub_eqb ap yp) y) a b
-- Forcer: the comparison as the MAJOR premise of a Bool.rec, the shape every reflected predicate and every icmp puts it in.
--@ probe-expect: STUCK-fast
-- peeled ir_nat_ltb, f64 literal first, symbolic second (the ir_f64_class orientation)
theorem probe (x : Nat) : @Bool.rec (fun _ => Bool) Bool.false Bool.false (ir_nat_ltb 9218868437227405312 x) = Bool.false := rfl
