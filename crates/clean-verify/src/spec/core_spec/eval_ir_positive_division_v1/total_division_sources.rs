// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Original checked fuel-sufficiency mathematics, owned once for production
//! installation and the historical probe. No evaluator body is duplicated.

pub(super) const UNCONDITIONAL: &[(&str, &str)] = &[
    (
        "ir_nat_ltb_walk_pred_left",
        r"def ir_nat_ltb_walk_pred_left (x : Nat) (b : Nat) (h : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) b) Bool.true) : @Eq Bool (ir_nat_ltb_walk x b) Bool.true := @Nat.rec (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true -> @Eq Bool (ir_nat_ltb_walk x z) Bool.true) (fun (h0 : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) Nat.zero) Bool.true) => ir_bool_false_ne_true (@Eq Bool (ir_nat_ltb_walk x Nat.zero) Bool.true) (@Eq.trans Bool Bool.false (ir_nat_ltb_walk (Nat.succ x) Nat.zero) Bool.true (@Eq.symm Bool (ir_nat_ltb_walk (Nat.succ x) Nat.zero) Bool.false (ir_nat_ltb_walk_zero_right (Nat.succ x))) h0)) (fun (bp : Nat) (_ihb : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) bp) Bool.true -> @Eq Bool (ir_nat_ltb_walk x bp) Bool.true) => fun (h1 : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) (Nat.succ bp)) Bool.true) => ir_nat_ltb_succ_walk x bp h1) b h",
    ),
    (
        "ir_nat_ltb_walk_drop_add_left",
        r"def ir_nat_ltb_walk_drop_add_left (a : Nat) (b : Nat) (c : Nat) (h : @Eq Bool (ir_nat_ltb_walk (Nat.add a c) b) Bool.true) : @Eq Bool (ir_nat_ltb_walk a b) Bool.true := @Nat.rec (fun (k : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.add a k) b) Bool.true -> @Eq Bool (ir_nat_ltb_walk a b) Bool.true) (fun (h0 : @Eq Bool (ir_nat_ltb_walk (Nat.add a Nat.zero) b) Bool.true) => h0) (fun (cp : Nat) (ih : @Eq Bool (ir_nat_ltb_walk (Nat.add a cp) b) Bool.true -> @Eq Bool (ir_nat_ltb_walk a b) Bool.true) => fun (h1 : @Eq Bool (ir_nat_ltb_walk (Nat.add a (Nat.succ cp)) b) Bool.true) => ih (ir_nat_ltb_walk_pred_left (Nat.add a cp) b h1)) c h",
    ),
    (
        "ir_nat_shl_index_lt",
        r"def ir_nat_shl_index_lt (k : Nat) : forall (p : Nat), @Eq Bool (ir_nat_ltb_walk (Nat.add k p) (ir_nat_shl (Nat.succ p) k)) Bool.true := @Nat.rec (fun (n : Nat) => forall (p : Nat), @Eq Bool (ir_nat_ltb_walk (Nat.add n p) (ir_nat_shl (Nat.succ p) n)) Bool.true) (fun (p : Nat) => @Eq.trans Bool (ir_nat_ltb_walk (Nat.add Nat.zero p) (Nat.succ p)) (ir_nat_ltb_walk p (Nat.succ p)) Bool.true (Eq.cong Nat Bool (fun (z : Nat) => ir_nat_ltb_walk z (Nat.succ p)) (Nat.add Nat.zero p) p (nat_add_zero_left p)) (ir_nat_ltb_walk_self_lt_add_succ p Nat.zero)) (fun (kp : Nat) (ih : forall (p : Nat), @Eq Bool (ir_nat_ltb_walk (Nat.add kp p) (ir_nat_shl (Nat.succ p) kp)) Bool.true) => fun (p : Nat) => ir_nat_ltb_walk_drop_add_left (Nat.add (Nat.succ kp) p) (ir_nat_shl (Nat.succ (Nat.add p (Nat.succ p))) kp) p (@Eq.trans Bool (ir_nat_ltb_walk (Nat.add (Nat.add (Nat.succ kp) p) p) (ir_nat_shl (Nat.succ (Nat.add p (Nat.succ p))) kp)) (ir_nat_ltb_walk (Nat.add kp (Nat.add p (Nat.succ p))) (ir_nat_shl (Nat.succ (Nat.add p (Nat.succ p))) kp)) Bool.true (Eq.cong Nat Bool (fun (z : Nat) => ir_nat_ltb_walk z (ir_nat_shl (Nat.succ (Nat.add p (Nat.succ p))) kp)) (Nat.add (Nat.add (Nat.succ kp) p) p) (Nat.add kp (Nat.add p (Nat.succ p))) (@Eq.trans Nat (Nat.add (Nat.add (Nat.succ kp) p) p) (Nat.add (Nat.succ kp) (Nat.add p p)) (Nat.add kp (Nat.add p (Nat.succ p))) (nat_add_assoc_local (Nat.succ kp) p p) (nat_add_succ_left kp (Nat.add p p)))) (ih (Nat.add p (Nat.succ p))))) k",
    ),
    (
        "ir_dm_fuel_always_suffices",
        r"def ir_dm_fuel_always_suffices (m : Nat) (d : Nat) : @Eq Bool (ir_nat_ltb m (ir_nat_shl (Nat.succ d) (Nat.succ m))) Bool.true := @Eq.trans Bool (ir_nat_ltb m (ir_nat_shl (Nat.succ d) (Nat.succ m))) (ir_nat_ltb_walk m (ir_nat_shl (Nat.succ d) (Nat.succ m))) Bool.true (ir_nat_ltb_walk_eq m (ir_nat_shl (Nat.succ d) (Nat.succ m))) (ir_nat_ltb_walk_drop_add_left m (ir_nat_shl (Nat.succ d) (Nat.succ m)) (Nat.succ d) (@Eq.trans Bool (ir_nat_ltb_walk (Nat.add m (Nat.succ d)) (ir_nat_shl (Nat.succ d) (Nat.succ m))) (ir_nat_ltb_walk (Nat.add (Nat.succ m) d) (ir_nat_shl (Nat.succ d) (Nat.succ m))) Bool.true (Eq.cong Nat Bool (fun (z : Nat) => ir_nat_ltb_walk z (ir_nat_shl (Nat.succ d) (Nat.succ m))) (Nat.add m (Nat.succ d)) (Nat.add (Nat.succ m) d) (@Eq.symm Nat (Nat.add (Nat.succ m) d) (Nat.add m (Nat.succ d)) (nat_add_succ_left m d))) (ir_nat_shl_index_lt (Nat.succ m) d)))",
    ),
    (
        "ir_div_agrees_unconditional",
        r"def ir_div_agrees_unconditional (m : Nat) (d : Nat) : @Eq Nat (ir_nat_div m (Nat.succ d)) (ir_dm_quot (ir_dm_go (Nat.succ Nat.zero) m (Nat.succ m) (Nat.succ d) (IRDivMod.mk m Nat.zero))) := ir_div_agrees_at_fuel m d (Nat.succ m) (ir_dm_fuel_always_suffices m d)",
    ),
    (
        "ir_rem_agrees_unconditional",
        r"def ir_rem_agrees_unconditional (m : Nat) (d : Nat) : @Eq Nat (ir_nat_rem m (Nat.succ d)) (ir_dm_rem (ir_dm_go (Nat.succ Nat.zero) m (Nat.succ m) (Nat.succ d) (IRDivMod.mk m Nat.zero))) := ir_rem_agrees_at_fuel m d (Nat.succ m) (ir_dm_fuel_always_suffices m d)",
    ),
];

pub(super) const TOTAL: &[(&str, &str)] = &[
    (
        "ir_nat_divmod_total_v1",
        r"def ir_nat_divmod_total_v1 (dividend divisor : Nat) : IRDivMod :=
@Nat.rec (fun (_ : Nat) => IRDivMod)
  (IRDivMod.mk dividend dividend)
  (fun (previous : Nat) (_ : IRDivMod) =>
    ir_dm_go 1 dividend (Nat.succ dividend) (Nat.succ previous) (IRDivMod.mk dividend 0))
  divisor",
    ),
    (
        "ir_nat_div_total_v1",
        r"def ir_nat_div_total_v1 (dividend divisor : Nat) : Nat :=
ir_dm_quot (ir_nat_divmod_total_v1 dividend divisor)",
    ),
    (
        "ir_nat_rem_total_v1",
        r"def ir_nat_rem_total_v1 (dividend divisor : Nat) : Nat :=
ir_dm_rem (ir_nat_divmod_total_v1 dividend divisor)",
    ),
    (
        "ir_div_go_zero_divisor_v1",
        r"def ir_div_go_zero_divisor_v1 (fuel word : Nat) :
  @Eq Nat (ir_div_go fuel word 0) fuel :=
@Nat.rec
  (fun (steps : Nat) => forall (input : Nat), @Eq Nat (ir_div_go steps input 0) steps)
  (fun (input : Nat) => @Eq.refl Nat 0)
  (fun (steps : Nat)
    (ih : forall (input : Nat), @Eq Nat (ir_div_go steps input 0) steps) =>
    fun (input : Nat) =>
      @Eq.trans Nat (ir_div_go (Nat.succ steps) input 0)
        (Nat.succ (ir_div_go steps (Nat.sub input 0) 0)) (Nat.succ steps)
        (ir_eq_cong Bool Nat
          (fun (guard : Bool) => @Bool.rec (fun (_ : Bool) => Nat)
            (Nat.succ (ir_div_go steps (Nat.sub input 0) 0)) 0 guard)
          (ir_nat_ltb input 0) Bool.false
          (@Eq.trans Bool (ir_nat_ltb input 0) (ir_nat_ltb_walk input 0) Bool.false
            (ir_nat_ltb_walk_eq input 0) (ir_nat_ltb_walk_zero_right input)))
        (ir_eq_cong Nat Nat Nat.succ (ir_div_go steps (Nat.sub input 0) 0) steps
          (ih (Nat.sub input 0))))
  fuel word",
    ),
    (
        "ir_nat_div_zero_divisor_v1",
        r"def ir_nat_div_zero_divisor_v1 (word : Nat) :
  @Eq Nat (ir_nat_div word 0) word :=
ir_div_go_zero_divisor_v1 word word",
    ),
    (
        "ir_nat_rem_zero_divisor_v1",
        r"def ir_nat_rem_zero_divisor_v1 (word : Nat) :
  @Eq Nat (ir_nat_rem word 0) word :=
ir_eq_cong Nat Nat (fun (product : Nat) => Nat.sub word product)
  (ir_nat_mul 0 (ir_nat_div word 0)) 0
  (ir_nat_mul_zero_left (ir_nat_div word 0))",
    ),
    (
        "ir_nat_div_total_agrees_v1",
        r"def ir_nat_div_total_agrees_v1 (dividend divisor : Nat) :
  @Eq Nat (ir_nat_div dividend divisor) (ir_nat_div_total_v1 dividend divisor) :=
@Nat.rec
  (fun (denominator : Nat) =>
    @Eq Nat (ir_nat_div dividend denominator) (ir_nat_div_total_v1 dividend denominator))
  (ir_nat_div_zero_divisor_v1 dividend)
  (fun (previous : Nat)
    (_ : @Eq Nat (ir_nat_div dividend previous) (ir_nat_div_total_v1 dividend previous)) =>
    ir_div_agrees_unconditional dividend previous)
  divisor",
    ),
    (
        "ir_nat_rem_total_agrees_v1",
        r"def ir_nat_rem_total_agrees_v1 (dividend divisor : Nat) :
  @Eq Nat (ir_nat_rem dividend divisor) (ir_nat_rem_total_v1 dividend divisor) :=
@Nat.rec
  (fun (denominator : Nat) =>
    @Eq Nat (ir_nat_rem dividend denominator) (ir_nat_rem_total_v1 dividend denominator))
  (ir_nat_rem_zero_divisor_v1 dividend)
  (fun (previous : Nat)
    (_ : @Eq Nat (ir_nat_rem dividend previous) (ir_nat_rem_total_v1 dividend previous)) =>
    ir_rem_agrees_unconditional dividend previous)
  divisor",
    ),
    (
        "ir_nat_rem_total_positive_bound_v1",
        r"def ir_nat_rem_total_positive_bound_v1 (word predecessor : Nat) :
  @Eq Bool (ir_nat_ltb (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (Nat.succ predecessor)) Bool.true :=
@Eq.trans Bool
  (ir_nat_ltb (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (Nat.succ predecessor))
  (ir_nat_ltb_walk (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (Nat.succ predecessor)) Bool.true
  (ir_nat_ltb_walk_eq (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (Nat.succ predecessor))
  (ir_dm_go_bound word (Nat.succ word) (Nat.succ predecessor)
    (ir_dm_fuel_always_suffices word predecessor))",
    ),
    (
        "ir_nat_rem_positive_bound_v1",
        r"def ir_nat_rem_positive_bound_v1 (word predecessor : Nat) :
  @Eq Bool (ir_nat_ltb (ir_nat_rem word (Nat.succ predecessor))
    (Nat.succ predecessor)) Bool.true :=
@Eq.trans Bool
  (ir_nat_ltb (ir_nat_rem word (Nat.succ predecessor)) (Nat.succ predecessor))
  (ir_nat_ltb (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (Nat.succ predecessor)) Bool.true
  (ir_eq_cong Nat Bool
    (fun (remainder : Nat) => ir_nat_ltb remainder (Nat.succ predecessor))
    (ir_nat_rem word (Nat.succ predecessor))
    (ir_nat_rem_total_v1 word (Nat.succ predecessor))
    (ir_nat_rem_total_agrees_v1 word (Nat.succ predecessor)))
  (ir_nat_rem_total_positive_bound_v1 word predecessor)",
    ),
];
