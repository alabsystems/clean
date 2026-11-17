/-
  SemRMiniRust — SemR's scalar operator layer IS MiniRust's (Trust proven-core
  RM4: "Its scalar operators are MiniRust's generated operators … A kernel
  lemma equates SemR's operator layer with MiniRust's").

  `MiniRust.lean` is the specr translator's output (Trust
  `scripts/trust_core/specr/SpecrPrelude.lean` followed by
  `generated/MiniRustSlice.lean`, verbatim, in a `noncomputable section`), so
  the MiniRust side of every lemma below is the generated
  `MRf.Machine.eval_bin_op` / `eval_un_op` itself, run on an ARBITRARY machine
  `M` and fuel: the integer arms never read the machine. SemR keeps its own
  executable operators (on `w`-bit residues; Lean's code generator does not
  take the free monad `SOut`'s recursor, the kernel does), and this file
  proves, for EVERY integer type and every residue, that they compute what
  MiniRust computes:

  * a SemR residue `a` of type `t` is the MiniRust integer `readAt s (t.bits 64) a`
    at MiniRust's `IntType` `mrIntTy s t` (signedness `s`, `t.bytes` bytes),
    and back (`readAt_emod`, `mr_bib`: MiniRust's `bring_in_bounds` is the
    residue);
  * each operator with a MiniRust counterpart agrees with it, value for value
    and undefined behaviour for undefined behaviour (`intBin_minirust`,
    `intUn_minirust`, `icmp_minirust`, `ovf_minirust`, `ctpop_minirust`), at
    the signedness the counterpart is evaluated at (`mrBin`, `mrRel`):
    `udiv`/`urem`/`lshr` and the unsigned comparisons at the unsigned twin of
    `t`, `sdiv`/`srem`/`ashr` and the signed ones at the signed twin, the rest
    (`and`/`or`/`xor` included, signed or not: `bitwise_resid`) at `t`
    itself; `ctpop` is MiniRust's `CountOnes`, whose count MiniRust types
    `u32` where trust-ir types it at the operand type (the same number);
  * the value level: on operands of the instruction's integer type, SemR's
    `evalBinop`/`evalUnop`/`evalIcmp`/`evalOverflow` are those residue
    operators (`evalBinop_minirust`, …), and `ICmp` on `Bool` operands is
    MiniRust's `Bool` order for the equalities and unsigned comparisons
    (`icmp_bool_minirust`);
  * `isize`/`usize` are MiniRust's at its slice's one target, x86_64: 8
    bytes (`mr_ptr_size`, `mr_usize`), the width trust-ir gives them in a
    module with no target record; a 32-bit target is not covered;
  * what MiniRust has no counterpart for is SemR's own, by name (`mrBin … =
    none`, `mrUn … = none`, `mrRelB … = none`): the `Bool`-valued
    `bAnd`/`bOr`/`bXor` on integers, the rotations, `ctlz`/`cttz`/`bswap`/
    `bitreverse`, the `Bool` binary operators (`boolBin`; this slice's
    `BinOp` has no `Bool` arm), the signed comparisons of `Bool`s, and the
    type and poison checks (trust-ir's dynamic checks).

  No `native_decide`, no `partial def`, no `sorry`, no axiom; every closure is
  in Ax0. Clean re-checks it through its reference entry.

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import SemR
import MiniRust

noncomputable section

namespace SemR
@[simp] theorem SOut.bind_ok' {α β : Type} (a : α) (f : α → SOut β) : (SOut.ok a).bind f = f a := rfl

theorem succ_mod_cases (k n : Nat) (hn : 0 < n) :
    ((k + 1) % n = k % n + 1 ∧ k % n + 1 < n) ∨ ((k + 1) % n = 0 ∧ k % n + 1 = n) := by
  have h1 := Nat.mod_lt k hn
  have h2 := Nat.mod_add_div k n
  by_cases h : k % n + 1 < n
  · left
    refine ⟨?_, h⟩
    have e : k + 1 = (k % n + 1) + n * (k / n) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · right
    have h3 : k % n + 1 = n := by omega
    refine ⟨?_, h3⟩
    have e : k + 1 = n * (k / n + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e, Nat.mul_mod_right]

theorem rem_euclid_eq (x : Int) (n : Nat) (hn : 0 < n) :
    SInt.rem_euclid x (Int.ofNat n) = SOut.ok (x % Int.ofNat n) := by
  have hb : SInt.beq (Int.ofNat n) 0 = false := by
    simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
  cases x with
  | ofNat k =>
    simp only [SInt.rem_euclid, SInt.rem, hb, SInt.ofSignedNat, SInt.isNeg, SInt.abs, SOut.bind_ok',
      SInt.blt]
    have : decide (Int.ofNat (k % n) < 0) = false := by
      simp only [decide_eq_false_iff_not, Int.not_lt]; exact Int.ofNat_nonneg _
    rw [this]
    rfl
  | negSucc k =>
    simp only [SInt.rem_euclid, SInt.rem, hb, SInt.ofSignedNat, SInt.isNeg, SInt.abs, SOut.bind_ok',
      SInt.blt]
    have hneg : Int.negSucc k % Int.ofNat n = Int.ofNat n - 1 - Int.ofNat (k % n) := by
      rw [Int.negSucc_emod _ (by simp; omega)]; rfl
    rw [hneg]
    have h1 := Nat.mod_lt k hn
    rcases succ_mod_cases k n hn with ⟨e, lt⟩ | ⟨e, eq⟩
    · rw [e]
      have : decide (-Int.ofNat (k % n + 1) < 0) = true := by simp; omega
      rw [this]; simp only [SOut.ok.injEq]; simp only [Int.ofNat_eq_natCast]; omega
    · rw [e]
      have : decide (-Int.ofNat 0 < 0) = false := by decide
      rw [this]; simp only [SOut.ok.injEq]; simp only [Int.ofNat_eq_natCast]; omega

def readAt (signed : Bool) (w a : Nat) : Int :=
  if signed && decide (half w ≤ a) then Int.ofNat a - Int.ofNat (modulus w) else Int.ofNat a
def sgnOf (s : Bool) : MR_Signedness := if s then .Signed else .Unsigned

theorem half_twice (w : Nat) (hw : 0 < w) : modulus w = 2 * half w := by
  unfold modulus half
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.pow_succ]; simp; omega

/-- The successful branch retains libspecr's exponent conversion domain. -/
theorem bib_in_domain (x : Int) (s : Bool) (B : Nat) (hB : 0 < B)
    (hwidth : B * 8 < 4294967296) :
    SInt.bring_in_bounds x (sgnOf s) (Int.ofNat B) =
      SOut.ok (readAt s (B * 8) (x % Int.ofNat (modulus (B * 8))).toNat) := by
  have hb : SInt.beq (Int.ofNat B) 0 = false := by
    simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
  have hm : 0 < modulus (B * 8) := Nat.pow_pos (by decide)
  have hh := half_twice (B * 8) (by omega)
  have hpow : SInt.pow 2 (Int.ofNat B * 8) = SOut.ok (Int.ofNat (modulus (B * 8))) := by
    change (if B * 8 < 4294967296 then _ else _) = _
    rw [if_pos hwidth]
    rfl
  have hdiv : SInt.div (Int.ofNat (modulus (B * 8))) 2 = SOut.ok (Int.ofNat (half (B * 8))) := by
    simp only [SInt.div, SInt.beq, SInt.ofSignedNat, SInt.isNeg, SInt.abs, SBool.xor]
    have : decide ((2 : Int) = 0) = false := by decide
    rw [this]; show SOut.ok (Int.ofNat (modulus (B * 8) / 2)) = _; congr 2; omega
  have hr := rem_euclid_eq x (modulus (B * 8)) hm
  have hnn : 0 ≤ x % Int.ofNat (modulus (B * 8)) := Int.emod_nonneg _ (by simp [Int.ofNat_eq_natCast]; omega)
  have hlt : x % Int.ofNat (modulus (B * 8)) < Int.ofNat (modulus (B * 8)) :=
    Int.emod_lt_of_pos _ (by simp [Int.ofNat_eq_natCast]; omega)
  generalize x % Int.ofNat (modulus (B * 8)) = r at hr hnn hlt
  unfold SInt.bring_in_bounds
  rw [hb]
  simp only [hpow, SOut.bind_ok', hr]
  cases s
  · simp only [sgnOf, readAt, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    congr 1; simp only [Int.ofNat_eq_natCast]; omega
  · simp only [sgnOf, ↓reduceIte, hdiv, SOut.bind_ok', SInt.ble, readAt, Bool.true_and]
    by_cases hc : Int.ofNat (half (B * 8)) ≤ r
    · have : decide (half (B * 8) ≤ r.toNat) = true := by simp [Int.ofNat_eq_natCast] at hc ⊢; omega
      simp only [hc, decide_true, this, ↓reduceIte]
      congr 1; simp only [Int.ofNat_eq_natCast]; omega
    · have : decide (half (B * 8) ≤ r.toNat) = false := by simp [Int.ofNat_eq_natCast] at hc ⊢; omega
      simp only [hc, decide_false, this, ↓reduceIte, Bool.false_eq_true]
      congr 1; simp only [Int.ofNat_eq_natCast]; omega

/-- A positive raw width can still fail the conversion before any residue
    arithmetic. This is an outcome, not an allocation-room premise. -/
theorem bib_conversion_overflow (x : Int) (s : Bool) (B : Nat)
    (hwidth : 4294967296 ≤ B * 8) :
    SInt.bring_in_bounds x (sgnOf s) (Int.ofNat B) =
      SOut.panic "called `Option::unwrap()` on a `None` value" := by
  have hB : 0 < B := by omega
  have hb : SInt.beq (Int.ofNat B) 0 = false := by
    simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
  have hpow : SInt.pow 2 (Int.ofNat B * 8) =
      SOut.panic "called `Option::unwrap()` on a `None` value" := by
    change (if B * 8 < 4294967296 then _ else _) = _
    rw [if_neg (by omega)]
  unfold SInt.bring_in_bounds
  rw [hb, hpow]
  rfl

/-- The original positive-width domain is retained, with both actual outcomes. -/
theorem bib (x : Int) (s : Bool) (B : Nat) (hB : 0 < B) :
    SInt.bring_in_bounds x (sgnOf s) (Int.ofNat B) =
      if B * 8 < 4294967296 then
        SOut.ok (readAt s (B * 8) (x % Int.ofNat (modulus (B * 8))).toNat)
      else SOut.panic "called `Option::unwrap()` on a `None` value" := by
  by_cases hwidth : B * 8 < 4294967296
  · rw [if_pos hwidth]
    exact bib_in_domain x s B hB hwidth
  · rw [if_neg hwidth]
    exact bib_conversion_overflow x s B (by omega)

def BoundsDomainGoal : Prop := ∀ (x : Int) (s : Bool) (B : Nat), 0 < B →
  SInt.bring_in_bounds x (sgnOf s) (Int.ofNat B) =
    if B * 8 < 4294967296 then
      SOut.ok (readAt s (B * 8) (x % Int.ofNat (modulus (B * 8))).toNat)
    else SOut.panic "called `Option::unwrap()` on a `None` value"

/-- The previous unconditional success claim is retained as a false goal. -/
def WrongBoundsDomainGoal : Prop := ∀ (x : Int) (s : Bool) (B : Nat), 0 < B →
  SInt.bring_in_bounds x (sgnOf s) (Int.ofNat B) =
    SOut.ok (readAt s (B * 8) (x % Int.ofNat (modulus (B * 8))).toNat)

theorem old_bounds_domain_goal_false : ¬ WrongBoundsDomainGoal := by
  intro old
  have success := old 0 false 536870912 (by decide)
  rw [bib_conversion_overflow 0 false 536870912 (by decide)] at success
  cases success

/-! ### The reading of a residue -/

section
variable (w : Nat) (hw : 0 < w)

theorem modulus_pos : 0 < modulus w := Nat.pow_pos (by decide)

theorem readAt_emod (s : Bool) (a : Nat) (ha : a < modulus w) :
    readAt s w a % Int.ofNat (modulus w) = Int.ofNat a := by
  unfold readAt
  have hm := modulus_pos w
  split
  · have e : Int.ofNat a - Int.ofNat (modulus w) = Int.ofNat a + (-1) * Int.ofNat (modulus w) := by omega
    rw [e, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by simp [Int.ofNat_eq_natCast]) (by simp [Int.ofNat_eq_natCast]; omega)
  · exact Int.emod_eq_of_lt (by simp [Int.ofNat_eq_natCast]) (by simp [Int.ofNat_eq_natCast]; omega)

theorem toNat_emod_ofNat (n : Nat) : (Int.ofNat n % Int.ofNat (modulus w)).toNat = n % modulus w := by
  rfl

end


-- `IntTy.bytes` (an integer's size in bytes, which MiniRust's `IntType` carries)
-- is SemR's own: its memory lays integers out by it.

theorem IntTy.bits_eq (t : IntTy) : (t.bits 64) = t.bytes * 8 := by cases t <;> rfl
theorem IntTy.bytes_pos (t : IntTy) : 0 < t.bytes := by cases t <;> decide
theorem IntTy.power_domain (t : IntTy) : t.bytes * 8 < 4294967296 := by
  cases t <;> decide

def mrIntTy (s : Bool) (t : IntTy) : MR_IntType := ⟨sgnOf s, Int.ofNat t.bytes⟩

@[simp] theorem mrIntTy_size (s : Bool) (t : IntTy) : (mrIntTy s t).size = Int.ofNat t.bytes := rfl
@[simp] theorem mrIntTy_signed (s : Bool) (t : IntTy) : (mrIntTy s t).signed = sgnOf s := rfl

theorem mr_bib (fuel : Nat) (s : Bool) (t : IntTy) (x : Int) :
    MRf.IntType.bring_in_bounds (fuel + 1) (mrIntTy s t) x =
      SOut.ok (readAt s (t.bits 64) (x % Int.ofNat (modulus (t.bits 64))).toNat) := by
  simp only [MRf.IntType.bring_in_bounds, mrIntTy]
  rw [IntTy.bits_eq, bib_in_domain x s t.bytes t.bytes_pos t.power_domain]
  rfl

theorem resid_add (w : Nat) (s : Bool) (a b : Nat) (ha : a < modulus w) (hb : b < modulus w) :
    ((readAt s w a + readAt s w b) % Int.ofNat (modulus w)).toNat = (a + b) % modulus w := by
  rw [Int.add_emod, readAt_emod w s a ha, readAt_emod w s b hb]; rfl

theorem add_minirust (fuel : Nat) (M : MR_Machine) (s : Bool) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    MRf.Machine.eval_bin_op (fuel + 4) M (.Int .Add)
        (.Int (readAt s (t.bits 64) a), .Int (mrIntTy s t)) (.Int (readAt s (t.bits 64) b), .Int (mrIntTy s t)) =
      SOut.ok (SRes.ok (.Int (readAt s (t.bits 64) ((a + b) % modulus (t.bits 64))), .Int (mrIntTy s t))) := by
  simp only [MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]
  simp only [SOut.bind_ok', resid_add _ s a b ha hb]
/-! ### Residues and ranges -/

theorem emod_shift (x y k m : Int) (h : x = y + k * m) : x % m = y % m := by
  rw [h, Int.add_mul_emod_self_right]

/-- An integer that is a residue `n` up to a multiple of `m` has residue `n % m`. -/
theorem resid_lin (m : Nat) (x : Int) (n : Nat) (k : Int)
    (h : x = Int.ofNat n + k * Int.ofNat m) : (x % Int.ofNat m).toNat = n % m := by
  rw [emod_shift x (Int.ofNat n) k _ h]; rfl

/-- MiniRust's range of an integer type: `[-2^(w-1), 2^(w-1))` signed, `[0, 2^w)` unsigned. -/
def inRange (s : Bool) (w : Nat) (x : Int) : Bool :=
  if s then decide (-Int.ofNat (half w) ≤ x) && decide (x < Int.ofNat (half w))
  else decide (0 ≤ x) && decide (x < Int.ofNat (modulus w))

theorem readAt_range (s : Bool) (w : Nat) (hw : 0 < w) (a : Nat) (ha : a < modulus w) :
    inRange s w (readAt s w a) = true := by
  have hh := half_twice w hw
  unfold inRange readAt
  cases s <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;>
  (try split) <;> simp_all [Int.ofNat_eq_natCast] <;> omega

theorem readAt_resid_of_range (s : Bool) (w : Nat) (hw : 0 < w) (x : Int) (hx : inRange s w x = true) :
    readAt s w (x % Int.ofNat (modulus w)).toNat = x := by
  have hh := half_twice w hw
  have hm := modulus_pos w
  unfold inRange at hx
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hx
    rw [Int.emod_eq_of_lt hx.1 hx.2]
    simp only [readAt, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]
    omega
  · simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hx
    by_cases hneg : x < 0
    · have e : x % Int.ofNat (modulus w) = x + Int.ofNat (modulus w) := by
        rw [emod_shift x (x + Int.ofNat (modulus w)) (-1) _ (by omega)]
        exact Int.emod_eq_of_lt (by simp [Int.ofNat_eq_natCast] at *; omega)
          (by simp [Int.ofNat_eq_natCast] at *; omega)
      rw [e]
      simp only [readAt, Bool.true_and]
      have : decide (half w ≤ (x + Int.ofNat (modulus w)).toNat) = true := by
        simp [Int.ofNat_eq_natCast] at *; omega
      rw [this]; simp only [↓reduceIte, Int.ofNat_eq_natCast]; simp [Int.ofNat_eq_natCast] at *; omega
    · rw [Int.emod_eq_of_lt (by omega) (by simp [Int.ofNat_eq_natCast] at *; omega)]
      simp only [readAt, Bool.true_and]
      have : decide (half w ≤ x.toNat) = false := by simp [Int.ofNat_eq_natCast] at *; omega
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]; omega

/-- The reading is injective on residues. -/
theorem readAt_inj (s : Bool) (w : Nat) (a b : Nat) (ha : a < modulus w) (hb : b < modulus w)
    (h : readAt s w a = readAt s w b) : a = b := by
  have e1 := readAt_emod w s a ha
  have e2 := readAt_emod w s b hb
  rw [h] at e1; rw [e1] at e2; exact Int.ofNat.inj e2

/-- MiniRust's `can_represent` is the range. -/
theorem mr_can_represent (fuel : Nat) (s : Bool) (t : IntTy) (x : Int) :
    MRf.IntType.can_represent (fuel + 1) (mrIntTy s t) x =
      SOut.ok (inRange s (t.bits 64) x) := by
  have hw : 0 < (t.bits 64) := by rw [IntTy.bits_eq]; have := t.bytes_pos; omega
  simp only [MRf.IntType.can_represent, SInt.in_bounds, mrIntTy]
  rw [IntTy.bits_eq, bib_in_domain x s t.bytes t.bytes_pos t.power_domain, ← IntTy.bits_eq]
  simp only [SOut.bind_ok', SInt.beq]
  congr 1
  by_cases hr : inRange s (t.bits 64) x = true
  · rw [readAt_resid_of_range s (t.bits 64) hw x hr]; simp [hr]
  · have hmpos : (0 : Int) < Int.ofNat (modulus (t.bits 64)) := by
      simp only [Int.ofNat_eq_natCast]; have := modulus_pos (t.bits 64); omega
    have hlt := Int.emod_lt_of_pos x hmpos
    have hnn := Int.emod_nonneg x (Int.ne_of_gt hmpos)
    have hlt' : (x % Int.ofNat (modulus (t.bits 64))).toNat < modulus (t.bits 64) := by
      simp only [Int.ofNat_eq_natCast] at *; omega
    have hin := readAt_range s (t.bits 64) hw _ hlt'
    have hne : x ≠ readAt s (t.bits 64) (x % Int.ofNat (modulus (t.bits 64))).toNat := by
      intro e; rw [← e] at hin; exact hr hin
    simp only [Bool.not_eq_true] at hr
    rw [hr]; exact decide_eq_false hne

/-! ### Binary operators -/

/-- MiniRust's verdict of a binary integer operator: a value of the operand type. -/
abbrev MRRes := SOut (SRes MR_TerminationInfo (MR_Value × MR_Type))

def mrVal (s : Bool) (t : IntTy) (r : Nat) : MRRes :=
  SOut.ok (SRes.ok (.Int (readAt s (t.bits 64) r), .Int (mrIntTy s t)))

def mrUb (msg : String) : MRRes := SOut.ok (SRes.err (.Ub msg))

/-- MiniRust's integer binary operator `mop` on residues `a`, `b` of `t` read
    at signedness `s`: the generated `eval_bin_op`, any machine, any fuel. -/
def mrBinOn (fuel : Nat) (M : MR_Machine) (mop : MR_IntBinOp) (s : Bool) (t : IntTy) (a b : Nat) :
    MRRes :=
  MRf.Machine.eval_bin_op (fuel + 4) M (.Int mop)
    (.Int (readAt s (t.bits 64) a), .Int (mrIntTy s t)) (.Int (readAt s (t.bits 64) b), .Int (mrIntTy s t))

theorem inRange_nat (w n : Nat) (h : n < modulus w) : inRange false w (Int.ofNat n) = true := by
  simp only [inRange, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Int.ofNat_nonneg _, Int.ofNat_lt.mpr h⟩

theorem readAt_false (w a : Nat) : readAt false w a = Int.ofNat a := by
  simp [readAt]

/-! ### Bitwise operators at either signedness

MiniRust's `&`, `|`, `^` are num-bigint's two's-complement operators on
unbounded integers (`SInt.band`/`bor`/`bxor`); on two readings, modulo `2^w`,
they are the residues' bitwise operators, signed readings included. -/

theorem tb_hi {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

/-- Disjoint bits add as they or. -/
theorem add_eq_or_disj (w p q : Nat) (hp : p < 2 ^ w) (hq : q < 2 ^ w) (h : p &&& q = 0) :
    p + q = p ||| q := by
  have hb : BitVec.ofNat w p &&& BitVec.ofNat w q = 0#w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq, h]
  have e1 := BitVec.toNat_add_of_and_eq_zero hb
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hb] at e1
  simp [BitVec.toNat_or, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at e1
  omega

/-- `x - (x &&& y)` keeps the bits of `x` that `y` lacks: `x` and the `w`-bit complement of `y`. -/
theorem sub_and_eq (w x y : Nat) (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    x - (x &&& y) = x &&& (2 ^ w - (y + 1)) := by
  have hd : (x &&& y) &&& (x &&& (2 ^ w - (y + 1))) = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_succ hy, Nat.zero_testBit]
    cases x.testBit i <;> cases y.testBit i <;> simp
  have hs := add_eq_or_disj w _ _ (Nat.and_lt_two_pow _ hy) (Nat.and_lt_two_pow _ (by omega)) hd
  have ho : (x &&& y) ||| (x &&& (2 ^ w - (y + 1))) = x := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_succ hy]
    by_cases hi : i < w
    · cases x.testBit i <;> cases y.testBit i <;> simp [hi]
    · rw [tb_hi hx (by omega)]; simp
  omega


/-- A negative reading is `Int.negSucc` of the complement. -/
theorem readAt_true_negSucc (w a : Nat) (ha : a < modulus w) (hneg : half w ≤ a) :
    readAt true w a = Int.negSucc (modulus w - (a + 1)) := by
  simp only [readAt, Bool.true_and, decide_eq_true hneg, ↓reduceIte, Int.negSucc_eq]
  simp only [Int.ofNat_eq_natCast]; omega

theorem readAt_true_ofNat (w a : Nat) (hpos : ¬ half w ≤ a) : readAt true w a = Int.ofNat a := by
  simp [readAt, hpos]

theorem negSucc_emod (w n : Nat) (hn : n < modulus w) :
    (Int.negSucc n % Int.ofNat (modulus w)).toNat = modulus w - (n + 1) := by
  rw [emod_shift (Int.negSucc n) (Int.ofNat (modulus w - (n + 1))) (-1) _
    (by simp only [Int.negSucc_eq, Int.ofNat_eq_natCast]; omega)]
  rw [toNat_emod_ofNat]; exact Nat.mod_eq_of_lt (by omega)

/-- The complement is an involution on `w`-bit residues. -/
theorem compl_compl (m a : Nat) (ha : a < m) : m - (m - (a + 1) + 1) = a := by omega

theorem compl_lt (m n : Nat) (hm : 0 < m) : m - (n + 1) < m := by omega

theorem tb_compl {w n : Nat} (hn : n < 2 ^ w) (i : Nat) :
    (2 ^ w - (n + 1)).testBit i = (decide (i < w) && !n.testBit i) := Nat.testBit_two_pow_sub_succ hn i

theorem land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
theorem lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
theorem xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

/-- The three bitwise operators on two readings, modulo `2^w`, at either signedness. -/
theorem bitwise_resid (w : Nat) (s : Bool) (a b : Nat) (ha : a < modulus w) (hb : b < modulus w) :
    (SInt.band (readAt s w a) (readAt s w b) % Int.ofNat (modulus w)).toNat = Nat.land a b % modulus w ∧
    (SInt.bor (readAt s w a) (readAt s w b) % Int.ofNat (modulus w)).toNat = Nat.lor a b % modulus w ∧
    (SInt.bxor (readAt s w a) (readAt s w b) % Int.ofNat (modulus w)).toNat = Nat.xor a b % modulus w := by
  have hm : 0 < modulus w := modulus_pos w
  cases s
  · simp only [readAt_false]; exact ⟨rfl, rfl, rfl⟩
  · -- write each negative reading as `negSucc` of its complement
    have key : ∀ x, x < modulus w →
        (half w ≤ x ∧ readAt true w x = Int.negSucc (modulus w - (x + 1))) ∨
        (¬ half w ≤ x ∧ readAt true w x = Int.ofNat x) := by
      intro x hx
      by_cases h : half w ≤ x
      · exact Or.inl ⟨h, readAt_true_negSucc w x hx h⟩
      · exact Or.inr ⟨h, readAt_true_ofNat w x h⟩
    have hmw : modulus w = 2 ^ w := rfl
    rcases key a ha with ⟨_, ea⟩ | ⟨_, ea⟩ <;> rcases key b hb with ⟨_, eb⟩ | ⟨_, eb⟩ <;>
      rw [ea, eb] <;> simp only [SInt.band, SInt.bor, SInt.bxor, land_eq, lor_eq, xor_eq]
    · -- both negative
      generalize hna : modulus w - (a + 1) = na at *
      generalize hnb : modulus w - (b + 1) = nb at *
      have hna' : na < 2 ^ w := by omega
      have hnb' : nb < 2 ^ w := by omega
      have hA : a = 2 ^ w - (na + 1) := by omega
      have hB : b = 2 ^ w - (nb + 1) := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [negSucc_emod w _ (by rw [hmw]; exact Nat.or_lt_two_pow hna' hnb')]
        rw [hmw, Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (by omega)), hA, hB]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (Nat.or_lt_two_pow hna' hnb'), Nat.testBit_and, tb_compl hna', tb_compl hnb',
          Nat.testBit_or]
        cases decide (i < w) <;> cases na.testBit i <;> cases nb.testBit i <;> rfl
      · rw [negSucc_emod w _ (by rw [hmw]; exact Nat.lt_of_le_of_lt (Nat.and_le_left) hna')]
        rw [hmw, Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by omega) (by omega)), hA, hB]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (Nat.lt_of_le_of_lt (Nat.and_le_left) hna'), Nat.testBit_or, tb_compl hna',
          tb_compl hnb', Nat.testBit_and]
        cases decide (i < w) <;> cases na.testBit i <;> cases nb.testBit i <;> rfl
      · show ((Int.ofNat (na ^^^ nb)) % Int.ofNat (modulus w)).toNat = _
        rw [toNat_emod_ofNat, hmw, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hna' hnb'),
          Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega) (by omega)), hA, hB]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_xor, Nat.testBit_xor, tb_compl hna', tb_compl hnb']
        by_cases hi : i < w
        · simp only [hi, decide_true, Bool.true_and]; cases na.testBit i <;> cases nb.testBit i <;> rfl
        · rw [tb_hi hna' (by omega), tb_hi hnb' (by omega)]; simp [hi]
    · -- `a` negative, `b` not
      generalize hna : modulus w - (a + 1) = na at *
      have hna' : na < 2 ^ w := by omega
      have hb' : b < 2 ^ w := hb
      have hA : a = 2 ^ w - (na + 1) := by omega
      have hsub := sub_and_eq w b na hb' hna'
      have hsub' := sub_and_eq w na b hna' hb'
      have hle : na - (na &&& b) < 2 ^ w := by omega
      refine ⟨?_, ?_, ?_⟩
      · show ((Int.ofNat (b - (b &&& na))) % Int.ofNat (modulus w)).toNat = _
        rw [toNat_emod_ofNat, hsub, hA, Nat.and_comm]
      · rw [negSucc_emod w _ (by rw [hmw]; exact hle), hsub', hmw,
          Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by omega) hb'), hA]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (by rw [← hsub']; exact hle), Nat.testBit_and, tb_compl hb', Nat.testBit_or,
          tb_compl hna']
        by_cases hi : i < w
        · simp only [hi, decide_true, Bool.true_and]; cases na.testBit i <;> cases b.testBit i <;> rfl
        · rw [tb_hi hb' (by omega)]; simp [hi]
      · rw [negSucc_emod w _ (by rw [hmw]; exact Nat.xor_lt_two_pow hna' hb'), hmw,
          Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (by omega) hb'), hA]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (Nat.xor_lt_two_pow hna' hb'), Nat.testBit_xor, Nat.testBit_xor, tb_compl hna']
        by_cases hi : i < w
        · simp only [hi, decide_true, Bool.true_and]; cases na.testBit i <;> cases b.testBit i <;> rfl
        · rw [tb_hi hb' (by omega), tb_hi hna' (by omega)]; simp [hi]
    · -- `b` negative, `a` not
      generalize hnb : modulus w - (b + 1) = nb at *
      have hnb' : nb < 2 ^ w := by omega
      have ha' : a < 2 ^ w := ha
      have hB : b = 2 ^ w - (nb + 1) := by omega
      have hsub := sub_and_eq w a nb ha' hnb'
      have hsub' := sub_and_eq w nb a hnb' ha'
      have hle : nb - (nb &&& a) < 2 ^ w := by omega
      refine ⟨?_, ?_, ?_⟩
      · show ((Int.ofNat (a - (a &&& nb))) % Int.ofNat (modulus w)).toNat = _
        rw [toNat_emod_ofNat, hsub, hB]
      · rw [negSucc_emod w _ (by rw [hmw]; exact hle), hsub', hmw,
          Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha' (by omega)), hB]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (by rw [← hsub']; exact hle), Nat.testBit_and, tb_compl ha', Nat.testBit_or,
          tb_compl hnb']
        by_cases hi : i < w
        · simp only [hi, decide_true, Bool.true_and]; cases nb.testBit i <;> cases a.testBit i <;> rfl
        · rw [tb_hi ha' (by omega)]; simp [hi]
      · rw [negSucc_emod w _ (by rw [hmw]; exact Nat.xor_lt_two_pow ha' hnb'), hmw,
          Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha' (by omega)), hB]
        apply Nat.eq_of_testBit_eq; intro i
        rw [tb_compl (Nat.xor_lt_two_pow ha' hnb'), Nat.testBit_xor, Nat.testBit_xor, tb_compl hnb']
        by_cases hi : i < w
        · simp only [hi, decide_true, Bool.true_and]; cases a.testBit i <;> cases nb.testBit i <;> rfl
        · rw [tb_hi ha' (by omega), tb_hi hnb' (by omega)]; simp [hi]
    · exact ⟨rfl, rfl, rfl⟩


section bin
variable (fuel : Nat) (M : MR_Machine) (t : IntTy) (a b : Nat)
  (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64))
include ha hb

theorem bits_pos : 0 < (t.bits 64) := by rw [IntTy.bits_eq]; have := t.bytes_pos; omega

theorem sub_mr (s : Bool) :
    mrBinOn fuel M .Sub s t a b = mrVal s t ((a + (modulus (t.bits 64) - b % modulus (t.bits 64))) % modulus (t.bits 64)) := by
  have key : ((readAt s (t.bits 64) a - readAt s (t.bits 64) b) % Int.ofNat (modulus (t.bits 64))).toNat =
      (a + (modulus (t.bits 64) - b % modulus (t.bits 64))) % modulus (t.bits 64) := by
    rw [Nat.mod_eq_of_lt hb, Int.sub_emod, readAt_emod _ s a ha, readAt_emod _ s b hb]
    refine resid_lin _ _ _ (-1) ?_
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]
  simp only [SOut.bind_ok', mrVal, key]

theorem mul_mr (s : Bool) :
    mrBinOn fuel M .Mul s t a b = mrVal s t ((a * b) % modulus (t.bits 64)) := by
  have key : ((readAt s (t.bits 64) a * readAt s (t.bits 64) b) % Int.ofNat (modulus (t.bits 64))).toNat =
      (a * b) % modulus (t.bits 64) := by
    rw [Int.mul_emod, readAt_emod _ s a ha, readAt_emod _ s b hb]; rfl
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]
  simp only [SOut.bind_ok', mrVal, key]

theorem band_mr (s : Bool) :
    mrBinOn fuel M .BitAnd s t a b = mrVal s t (Nat.land a b % modulus (t.bits 64)) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]; simp only [SOut.bind_ok', mrVal, (bitwise_resid _ s a b ha hb).1]

theorem bor_mr (s : Bool) :
    mrBinOn fuel M .BitOr s t a b = mrVal s t (Nat.lor a b % modulus (t.bits 64)) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]; simp only [SOut.bind_ok', mrVal, (bitwise_resid _ s a b ha hb).2.1]

theorem bxor_mr (s : Bool) :
    mrBinOn fuel M .BitXor s t a b = mrVal s t (Nat.xor a b % modulus (t.bits 64)) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, SOut.bind_ok']
  rw [mr_bib]; simp only [SOut.bind_ok', mrVal, (bitwise_resid _ s a b ha hb).2.2]

theorem udiv_mr :
    mrBinOn fuel M .Div false t a b =
      if b = 0 then mrUb "division by zero" else mrVal false t (a / b) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, readAt_false]
  by_cases hb0 : b = 0
  · subst hb0; simp only [SInt.beq, Int.ofNat_eq_natCast]; rfl
  · have hbe : SInt.beq (Int.ofNat b) 0 = false := by
      simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
    have hq : SInt.div (Int.ofNat a) (Int.ofNat b) = SOut.ok (Int.ofNat (a / b)) := by
      simp only [SInt.div, hbe]; rfl
    have hlt : a / b < modulus (t.bits 64) := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
    have hin : inRange false (t.bits 64) (Int.ofNat (a / b)) = true := inRange_nat _ _ hlt
    simp only [hbe, hq, SOut.bind_ok', mr_can_represent, hin, SBool.not, mr_bib, hb0, ↓reduceIte,
      mrVal, readAt_false, toNat_emod_ofNat, Nat.mod_eq_of_lt hlt]


theorem urem_mr :
    mrBinOn fuel M .Rem false t a b =
      if b = 0 then mrUb "modulus of remainder is zero" else mrVal false t (a % b) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, readAt_false]
  by_cases hb0 : b = 0
  · subst hb0; simp only [SInt.beq, Int.ofNat_eq_natCast]; rfl
  · have hbe : SInt.beq (Int.ofNat b) 0 = false := by
      simp only [SInt.beq, decide_eq_false_iff_not, Int.ofNat_eq_natCast]; omega
    have hq : SInt.div (Int.ofNat a) (Int.ofNat b) = SOut.ok (Int.ofNat (a / b)) := by
      simp only [SInt.div, hbe]; rfl
    have hr : SInt.rem (Int.ofNat a) (Int.ofNat b) = SOut.ok (Int.ofNat (a % b)) := by
      simp only [SInt.rem, hbe]; rfl
    have hlt : a / b < modulus (t.bits 64) := Nat.lt_of_le_of_lt (Nat.div_le_self a b) ha
    have hlt2 : a % b < modulus (t.bits 64) := Nat.lt_of_le_of_lt (Nat.mod_le a b) ha
    have hin : inRange false (t.bits 64) (Int.ofNat (a / b)) = true := inRange_nat _ _ hlt
    simp only [hbe, hq, hr, SOut.bind_ok', mr_can_represent, hin, SBool.not, mr_bib, hb0, ↓reduceIte,
      mrVal, readAt_false, toNat_emod_ofNat, Nat.mod_eq_of_lt hlt2]

theorem bits_le_half : (t.bits 64) ≤ half (t.bits 64) := by
  have hw := bits_pos t a b ha hb
  unfold half
  have := Nat.lt_two_pow_self (n := (t.bits 64) - 1)
  omega

theorem mul_pow_resid (s : Bool) (k : Nat) :
    ((readAt s (t.bits 64) a * Int.ofNat (2 ^ k)) % Int.ofNat (modulus (t.bits 64))).toNat =
      (a * 2 ^ k) % modulus (t.bits 64) := by
  have hm : (Int.ofNat a) % Int.ofNat (modulus (t.bits 64)) = Int.ofNat a :=
    Int.emod_eq_of_lt (Int.ofNat_nonneg _) (Int.ofNat_lt.mpr ha)
  rw [Int.mul_emod, readAt_emod _ s a ha, ← hm, ← Int.mul_emod]
  rfl

/-- The shift amount is out of range exactly when SemR says so, at either signedness. -/
theorem shift_oob (s : Bool) :
    (SInt.blt (readAt s (t.bits 64) b) 0 || SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt s (t.bits 64) b)) =
      decide ((t.bits 64) ≤ b) := by
  have hle := bits_le_half t a b ha hb
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  have hbe := IntTy.bits_eq t
  rw [Bool.eq_iff_iff]
  simp only [SInt.blt, SInt.ble, SSize.bits, Bool.or_eq_true, decide_eq_true_eq]
  unfold readAt
  cases s
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]; omega
  · simp only [Bool.true_and]
    by_cases h2 : half (t.bits 64) ≤ b
    · simp only [h2, decide_true, ↓reduceIte, Int.ofNat_eq_natCast]; omega
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_natCast]; omega

theorem shl_mr (s : Bool) :
    mrBinOn fuel M .ShlUnchecked s t a b =
      if (t.bits 64) ≤ b then mrUb "overflow in unchecked shift"
      else mrVal s t ((a * 2 ^ b) % modulus (t.bits 64)) := by
  have hoob := shift_oob t a b ha hb s
  have hle := bits_le_half t a b ha hb
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, mrIntTy_size]
  by_cases hsh : (t.bits 64) ≤ b
  · have hc : (SInt.blt (readAt s (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt s (t.bits 64) b)) = true := by
      rw [hoob]; simp [hsh]
    revert hc
    cases SInt.blt (readAt s (t.bits 64) b) 0 <;> intro hc <;> simp only [Bool.false_or, Bool.true_or] at hc <;>
      simp only [hc, hsh, ↓reduceIte] <;> rfl
  · have hc : (SInt.blt (readAt s (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt s (t.bits 64) b)) = false := by
      rw [hoob]; simp [hsh]
    have hrb : readAt s (t.bits 64) b = Int.ofNat b := by
      unfold readAt; cases s <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
        ↓reduceIte] <;> (try split) <;> simp_all <;> omega
    simp only [Bool.or_eq_false_iff, hrb] at hc
    simp only [hrb, hc.1, hc.2, hsh, ↓reduceIte, SInt.shl, SNat.pow2, SOut.bind_ok']
    simp only [mr_bib, SOut.bind_ok', mrVal]
    rw [show Int.ofNat (Nat.pow 2 b) = Int.ofNat (2 ^ b) from rfl, mul_pow_resid t a b ha hb s b]


theorem lshr_mr :
    mrBinOn fuel M .ShrUnchecked false t a b =
      if (t.bits 64) ≤ b then mrUb "overflow in unchecked shift" else mrVal false t (a / 2 ^ b) := by
  have hoob := shift_oob t a b ha hb false
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, mrIntTy_size]
  by_cases hsh : (t.bits 64) ≤ b
  · have hc : (SInt.blt (readAt false (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt false (t.bits 64) b)) = true := by
      rw [hoob]; simp [hsh]
    revert hc
    cases SInt.blt (readAt false (t.bits 64) b) 0 <;> intro hc <;>
      simp only [Bool.false_or, Bool.true_or] at hc <;> simp only [hc, hsh, ↓reduceIte] <;> rfl
  · have hc : (SInt.blt (readAt false (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt false (t.bits 64) b)) = false := by
      rw [hoob]; simp [hsh]
    have hlt : a / 2 ^ b < modulus (t.bits 64) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    simp only [Bool.or_eq_false_iff, readAt_false] at hc
    simp only [readAt_false, hc.1, hc.2, hsh, ↓reduceIte, SInt.shr, SNat.shr, SNat.pow2, SOut.bind_ok',
      mr_bib, mrVal]
    rw [show Int.ofNat (a / Nat.pow 2 b) = Int.ofNat (a / 2 ^ b) from rfl, toNat_emod_ofNat,
      Nat.mod_eq_of_lt hlt]

end bin

/-- Complementing then shifting right is shifting then complementing, in `w` bits. -/
theorem shr_compl (w b a : Nat) (hb : b ≤ w) (ha : a < 2 ^ w) :
    (2 ^ w - 1 - a) / 2 ^ b = 2 ^ (w - b) - 1 - a / 2 ^ b := by
  have hp : 0 < 2 ^ b := Nat.pow_pos (by decide)
  have hQ : 0 < 2 ^ (w - b) := Nat.pow_pos (by decide)
  have hm : 2 ^ w = 2 ^ (w - b) * 2 ^ b := by rw [← Nat.pow_add]; congr 1; omega
  have hd := Nat.div_add_mod a (2 ^ b)
  have hr := Nat.mod_lt a hp
  have hq : a / 2 ^ b < 2 ^ (w - b) := by
    rw [Nat.div_lt_iff_lt_mul hp]; rw [← hm]; exact ha
  generalize 2 ^ b = p at *
  generalize 2 ^ (w - b) = Q at *
  generalize a / p = q at *
  generalize a % p = r at *
  have e1 : (Q - 1 - q) * p = Q * p - p - q * p := by
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul]
  have e2 : (Q - 1 - q + 1) * p = Q * p - q * p := by
    rw [show Q - 1 - q + 1 = Q - q by omega, Nat.sub_mul]
  have h1 : (q + 1) * p ≤ Q * p := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at h1
  rw [Nat.mul_comm p q] at hd
  apply Nat.div_eq_of_lt_le
  · rw [e1]; omega
  · rw [e2]; omega

theorem IntTy.bits_ge_8 (t : IntTy) : 8 ≤ (t.bits 64) := by rw [IntTy.bits_eq]; have := t.bytes_pos; omega

theorem half_pos (w : Nat) : 0 < half w := Nat.pow_pos (by decide)

theorem xor_bne (x y : Bool) : SBool.xor x y = (x != y) := by cases x <;> cases y <;> rfl

theorem signed_resid (w : Nat) (neg : Bool) (q : Nat) (hq : q < modulus w) :
    ((SInt.ofSignedNat neg q) % Int.ofNat (modulus w)).toNat =
      if neg then negR w q else q % modulus w := by
  cases neg
  · rfl
  · simp only [SInt.ofSignedNat, ↓reduceIte, negR, Nat.mod_eq_of_lt hq]
    refine resid_lin _ _ _ (-1) ?_
    simp only [Int.ofNat_eq_natCast]; omega


section bin2
variable (fuel : Nat) (M : MR_Machine) (t : IntTy) (a b : Nat)
  (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64))
include ha hb

theorem readAt_true_neg (hneg : half (t.bits 64) ≤ a) :
    readAt true (t.bits 64) a = Int.negSucc (modulus (t.bits 64) - a - 1) := by
  simp only [readAt, Bool.true_and, hneg, decide_true, ↓reduceIte]
  rw [Int.negSucc_eq]; simp only [Int.ofNat_eq_natCast]; omega

theorem readAt_true_pos (hpos : ¬ half (t.bits 64) ≤ a) : readAt true (t.bits 64) a = Int.ofNat a := by
  simp only [readAt, Bool.true_and, hpos, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem ashr_mr :
    mrBinOn fuel M .ShrUnchecked true t a b =
      if (t.bits 64) ≤ b then mrUb "overflow in unchecked shift"
      else mrVal true t (a / 2 ^ b +
        (if isNeg (t.bits 64) a then modulus (t.bits 64) - 2 ^ ((t.bits 64) - b) else 0)) := by
  have hoob := shift_oob t a b ha hb true
  have hle := bits_le_half t a b ha hb
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op, mrIntTy_size]
  by_cases hsh : (t.bits 64) ≤ b
  · have hc : (SInt.blt (readAt true (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt true (t.bits 64) b)) = true := by
      rw [hoob]; simp [hsh]
    revert hc
    cases SInt.blt (readAt true (t.bits 64) b) 0 <;> intro hc <;>
      simp only [Bool.false_or, Bool.true_or] at hc <;> simp only [hc, hsh, ↓reduceIte] <;> rfl
  · have hc : (SInt.blt (readAt true (t.bits 64) b) 0 ||
        SInt.ble (SSize.bits (Int.ofNat t.bytes)) (readAt true (t.bits 64) b)) = false := by
      rw [hoob]; simp [hsh]
    have hrb : readAt true (t.bits 64) b = Int.ofNat b := readAt_true_pos t b a hb ha (by omega)
    simp only [Bool.or_eq_false_iff, hrb] at hc
    simp only [hrb, hc.1, hc.2, hsh, ↓reduceIte, SOut.bind_ok']
    by_cases hneg : half (t.bits 64) ≤ a
    · rw [readAt_true_neg t a b ha hb hneg]
      have hc2 := shr_compl (t.bits 64) b a (by omega) ha
      have hpb : 2 ^ ((t.bits 64) - b) ≤ modulus (t.bits 64) := Nat.pow_le_pow_right (by decide) (by omega)
      have hq : (modulus (t.bits 64) - a - 1) / 2 ^ b ≤ modulus (t.bits 64) - a - 1 := Nat.div_le_self _ _
      have key : (Int.negSucc ((modulus (t.bits 64) - a - 1) / Nat.pow 2 b) %
          Int.ofNat (modulus (t.bits 64))).toNat = a / 2 ^ b + (modulus (t.bits 64) - 2 ^ ((t.bits 64) - b)) := by
        have hq2 : a / 2 ^ b < 2 ^ ((t.bits 64) - b) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
          rw [← Nat.pow_add, show (t.bits 64) - b + b = (t.bits 64) by omega]; exact ha
        have hlt : a / 2 ^ b + (modulus (t.bits 64) - 2 ^ ((t.bits 64) - b)) < modulus (t.bits 64) := by omega
        rw [← Nat.mod_eq_of_lt hlt]
        rw [show Nat.pow 2 b = 2 ^ b from rfl]
        refine resid_lin _ _ _ (-1) ?_
        unfold modulus at *
        rw [show 2 ^ (t.bits 64) - a - 1 = 2 ^ (t.bits 64) - 1 - a by omega, hc2]
        rw [Int.negSucc_eq]
        simp only [Int.ofNat_eq_natCast]; omega
      simp only [SInt.shr, SNat.shr, SNat.pow2, SOut.bind_ok', mr_bib, mrVal, isNeg, hneg,
        decide_true, ↓reduceIte, key]
    · rw [readAt_true_pos t a b ha hb hneg]
      have hlt : a / 2 ^ b < modulus (t.bits 64) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
      simp only [SInt.shr, SNat.shr, SNat.pow2, SOut.bind_ok', mr_bib, mrVal, isNeg, hneg,
        decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [show Int.ofNat (a / Nat.pow 2 b) = Int.ofNat (a / 2 ^ b) from rfl, toNat_emod_ofNat,
        Nat.mod_eq_of_lt hlt]



theorem isNeg_readAt : SInt.isNeg (readAt true (t.bits 64) a) = isNeg (t.bits 64) a := by
  by_cases hneg : half (t.bits 64) ≤ a
  · rw [readAt_true_neg t a b ha hb hneg]; simp [SInt.isNeg, isNeg, hneg]
  · rw [readAt_true_pos t a b ha hb hneg]; simp [SInt.isNeg, isNeg, hneg]

theorem abs_readAt : SInt.abs (readAt true (t.bits 64) a) = mag (t.bits 64) a := by
  by_cases hneg : half (t.bits 64) ≤ a
  · rw [readAt_true_neg t a b ha hb hneg]; simp only [SInt.abs, mag, isNeg, hneg, decide_true,
      ↓reduceIte]; omega
  · rw [readAt_true_pos t a b ha hb hneg]; simp [SInt.abs, mag, isNeg, hneg]

theorem mag_le_half : mag (t.bits 64) a ≤ half (t.bits 64) := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  unfold mag isNeg; split <;> simp_all <;> omega

theorem readAt_true_eq_zero : SInt.beq (readAt true (t.bits 64) b) 0 = decide (b = 0) := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  have hp := half_pos (t.bits 64)
  by_cases hneg : half (t.bits 64) ≤ b
  · rw [readAt_true_neg t b a hb ha hneg]
    have h0 : b ≠ 0 := by omega
    simp only [SInt.beq]
    rw [decide_eq_false h0]; exact decide_eq_false (Int.negSucc_ne_zero _)
  · rw [readAt_true_pos t b a hb ha hneg]; simp only [SInt.beq]
    by_cases h0 : b = 0
    · subst h0; rfl
    · rw [decide_eq_false h0]; exact decide_eq_false (fun e => h0 (Int.ofNat.inj e))

/-- MiniRust's quotient at a signed type overflows exactly on `MIN / -1`,
    SemR's overflow condition (the remainder checks the same quotient). -/
theorem sdiv_in_range (hb0 : b ≠ 0) :
    inRange true (t.bits 64) (SInt.ofSignedNat (isNeg (t.bits 64) a != isNeg (t.bits 64) b)
      (mag (t.bits 64) a / mag (t.bits 64) b)) = !(a == half (t.bits 64) && b == modulus (t.bits 64) - 1) := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  have hhalf : 8 ≤ half (t.bits 64) := Nat.le_trans t.bits_ge_8 (bits_le_half t a b ha hb)
  have hma := mag_le_half t a b ha hb
  have hmb := mag_le_half t b a hb ha
  have hmb1 : 1 ≤ mag (t.bits 64) b := by unfold mag isNeg; split <;> simp_all <;> omega
  have hq : mag (t.bits 64) a / mag (t.bits 64) b ≤ mag (t.bits 64) a := Nat.div_le_self _ _
  have hqm : mag (t.bits 64) a / mag (t.bits 64) b * mag (t.bits 64) b ≤ mag (t.bits 64) a := Nat.div_mul_le_self _ _
  -- what `mag` and `isNeg` say about the residues
  have hmagA : mag (t.bits 64) a = half (t.bits 64) ↔ a = half (t.bits 64) := by
    unfold mag isNeg; constructor
    · intro e; split at e <;> simp_all <;> omega
    · intro e; subst e; simp; omega
  generalize hqdef : mag (t.bits 64) a / mag (t.bits 64) b = q at hq hqm
  rw [Bool.eq_iff_iff]
  cases hx : (isNeg (t.bits 64) a != isNeg (t.bits 64) b)
  · -- same signs: the quotient `q ≥ 0` is in range iff `q < half`
    simp only [SInt.ofSignedNat, inRange, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Int.ofNat_eq_natCast]
    constructor
    · intro ⟨_, hlt⟩
      by_cases h1 : a = half (t.bits 64)
      · right
        intro h2
        have e1 : mag (t.bits 64) a = half (t.bits 64) := hmagA.mpr h1
        have hnb : half (t.bits 64) ≤ b := by omega
        have e2 : mag (t.bits 64) b = 1 := by
          unfold mag isNeg; rw [decide_eq_true hnb, if_pos rfl]; omega
        rw [e1, e2, Nat.div_one] at hqdef
        omega
      · left; exact h1
    · intro hnot
      refine ⟨by omega, ?_⟩
      have hqh : q ≤ half (t.bits 64) := Nat.le_trans hq hma
      apply Int.ofNat_lt.mpr
      apply Nat.lt_of_le_of_ne hqh
      intro heq
      have hmaeq : mag (t.bits 64) a = half (t.bits 64) := by omega
      have hmul : half (t.bits 64) * mag (t.bits 64) b ≤ half (t.bits 64) * 1 := by
        rw [heq, hmaeq] at hqm; rw [Nat.mul_one]; exact hqm
      have hmbeq : mag (t.bits 64) b = 1 := by
        have := Nat.le_of_mul_le_mul_left hmul (by omega); omega
      have ha' : a = half (t.bits 64) := hmagA.mp hmaeq
      have hna : isNeg (t.bits 64) a = true := by simp [isNeg, ha']
      have hnb : isNeg (t.bits 64) b = true := by
        simp only [bne_eq_false_iff_eq] at hx; rw [← hx, hna]
      have hb' : b = modulus (t.bits 64) - 1 := by
        unfold mag at hmbeq; rw [hnb] at hmbeq; simp at hmbeq; omega
      cases hnot with
      | inl h => exact h ha'
      | inr h => exact h hb'
  · -- different signs: `-q` with `q ≤ half` is in range, and `MIN / -1` has equal signs
    have hne : ¬ (a = half (t.bits 64) ∧ b = modulus (t.bits 64) - 1) := by
      intro ⟨h1, h2⟩
      have e1 : isNeg (t.bits 64) a = true := by simp [isNeg, h1]
      have e2 : isNeg (t.bits 64) b = true := by simp [isNeg, h2]; omega
      rw [e1, e2] at hx; exact absurd hx (by decide)
    have hqh : q ≤ half (t.bits 64) := Nat.le_trans hq hma
    simp only [SInt.ofSignedNat, inRange, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Int.ofNat_eq_natCast]
    constructor
    · intro _; omega
    · intro _; omega

theorem sdiv_mr :
    mrBinOn fuel M .Div true t a b =
      if b = 0 then mrUb "division by zero"
      else if (a == half (t.bits 64) && b == modulus (t.bits 64) - 1) = true then mrUb "overflow in division"
      else mrVal true t (if isNeg (t.bits 64) a != isNeg (t.bits 64) b then negR (t.bits 64) (mag (t.bits 64) a / mag (t.bits 64) b)
        else (mag (t.bits 64) a / mag (t.bits 64) b) % modulus (t.bits 64)) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op,
    readAt_true_eq_zero t a b ha hb]
  by_cases hb0 : b = 0
  · simp only [hb0, decide_true, ↓reduceIte]; rfl
  · have hdiv : SInt.div (readAt true (t.bits 64) a) (readAt true (t.bits 64) b) =
        SOut.ok (SInt.ofSignedNat (isNeg (t.bits 64) a != isNeg (t.bits 64) b) (mag (t.bits 64) a / mag (t.bits 64) b)) := by
      simp only [SInt.div, readAt_true_eq_zero t a b ha hb, hb0, decide_false, isNeg_readAt t a b ha hb,
        isNeg_readAt t b a hb ha, abs_readAt t a b ha hb, abs_readAt t b a hb ha, xor_bne]
    have hr := sdiv_in_range t a b ha hb hb0
    have hlt : mag (t.bits 64) a / mag (t.bits 64) b < modulus (t.bits 64) := by
      have := mag_le_half t a b ha hb; have := Nat.div_le_self (mag (t.bits 64) a) (mag (t.bits 64) b)
      have := half_twice (t.bits 64) (bits_pos t a b ha hb); have := half_pos (t.bits 64)
      omega
    simp only [hb0, decide_false, hdiv, SOut.bind_ok', mr_can_represent, hr, ↓reduceIte]
    cases hov : (a == half (t.bits 64) && b == modulus (t.bits 64) - 1)
    · simp only [Bool.not_false, SBool.not, SOut.bind_ok', mr_bib, mrVal, Bool.false_eq_true,
        ↓reduceIte, signed_resid _ _ _ hlt]
    · simp only [Bool.not_true, SBool.not, ↓reduceIte]; rfl

theorem srem_mr :
    mrBinOn fuel M .Rem true t a b =
      if b = 0 then mrUb "modulus of remainder is zero"
      else if (a == half (t.bits 64) && b == modulus (t.bits 64) - 1) = true then mrUb "overflow in remainder"
      else mrVal true t (if isNeg (t.bits 64) a then negR (t.bits 64) (mag (t.bits 64) a % mag (t.bits 64) b)
        else (mag (t.bits 64) a % mag (t.bits 64) b) % modulus (t.bits 64)) := by
  simp only [mrBinOn, MRf.Machine.eval_bin_op, MRf.Machine.eval_int_bin_op,
    readAt_true_eq_zero t a b ha hb]
  by_cases hb0 : b = 0
  · simp only [hb0, decide_true, ↓reduceIte]; rfl
  · have hdiv : SInt.div (readAt true (t.bits 64) a) (readAt true (t.bits 64) b) =
        SOut.ok (SInt.ofSignedNat (isNeg (t.bits 64) a != isNeg (t.bits 64) b) (mag (t.bits 64) a / mag (t.bits 64) b)) := by
      simp only [SInt.div, readAt_true_eq_zero t a b ha hb, hb0, decide_false, isNeg_readAt t a b ha hb,
        isNeg_readAt t b a hb ha, abs_readAt t a b ha hb, abs_readAt t b a hb ha, xor_bne]
    have hrem : SInt.rem (readAt true (t.bits 64) a) (readAt true (t.bits 64) b) =
        SOut.ok (SInt.ofSignedNat (isNeg (t.bits 64) a) (mag (t.bits 64) a % mag (t.bits 64) b)) := by
      simp only [SInt.rem, readAt_true_eq_zero t a b ha hb, hb0, decide_false, isNeg_readAt t a b ha hb,
        abs_readAt t a b ha hb, abs_readAt t b a hb ha]
    have hr := sdiv_in_range t a b ha hb hb0
    have hlt : mag (t.bits 64) a % mag (t.bits 64) b < modulus (t.bits 64) := by
      have := mag_le_half t a b ha hb; have := Nat.mod_le (mag (t.bits 64) a) (mag (t.bits 64) b)
      have := half_twice (t.bits 64) (bits_pos t a b ha hb); have := half_pos (t.bits 64)
      omega
    simp only [hb0, decide_false, hdiv, SOut.bind_ok', mr_can_represent, hr, ↓reduceIte]
    cases hov : (a == half (t.bits 64) && b == modulus (t.bits 64) - 1)
    · simp only [Bool.not_false, SBool.not, SOut.bind_ok', hrem, mr_bib, mrVal, Bool.false_eq_true,
        ↓reduceIte, signed_resid _ _ _ hlt]
    · simp only [Bool.not_true, SBool.not, ↓reduceIte]; rfl

end bin2


/-! ### Unary operators -/

/-- MiniRust's sanity check of an integer result passes on every residue's reading. -/
theorem check_value_int (fuel : Nat) (M : MR_Machine) (s : Bool) (t : IntTy) (r : Nat)
    (hr : r < modulus (t.bits 64)) :
    MRf.Machine.check_value (fuel + 3) M (.Int (readAt s (t.bits 64) r)) (.Int (mrIntTy s t)) =
      SOut.ok (SRes.ok ()) := by
  have hw : 0 < (t.bits 64) := by have := t.bits_ge_8; omega
  simp only [MRf.Machine.check_value, MR_rec_94.tie, MRf.Machine.check_value_open, mr_can_represent,
    readAt_range s (t.bits 64) hw r hr, SOut.bind_ok', MRf.fn.ensure_else_ub, SBool.not]

/-- MiniRust's integer unary operator `uop` on residue `a` of `t` read at signedness `s`. -/
def mrUnOn (fuel : Nat) (M : MR_Machine) (uop : MR_IntUnOp) (s : Bool) (t : IntTy) (a : Nat) : MRRes :=
  MRf.Machine.eval_un_op (fuel + 4) M (.Int uop) (.Int (readAt s (t.bits 64) a), .Int (mrIntTy s t))

theorem neg_mr (fuel : Nat) (M : MR_Machine) (s : Bool) (t : IntTy) (a : Nat) (ha : a < modulus (t.bits 64)) :
    mrUnOn fuel M .Neg s t a = mrVal s t (negR (t.bits 64) a) := by
  have key : ((0 - readAt s (t.bits 64) a) % Int.ofNat (modulus (t.bits 64))).toNat = negR (t.bits 64) a := by
    rw [Int.sub_emod, readAt_emod _ s a ha]
    unfold negR
    rw [Nat.mod_eq_of_lt ha]
    refine resid_lin _ _ _ (-1) ?_
    have : (0 : Int) % Int.ofNat (modulus (t.bits 64)) = 0 := Int.zero_emod _
    rw [this]; simp only [Int.ofNat_eq_natCast]; omega
  have hr : negR (t.bits 64) a < modulus (t.bits 64) := by
    unfold negR; exact Nat.mod_lt _ (modulus_pos _)
  simp only [mrUnOn, MRf.Machine.eval_un_op, MRf.Machine.eval_int_un_op, SOut.bind_ok', mr_bib, mrVal,
    key, check_value_int _ _ _ _ _ hr, SRes.expect]

theorem not_mr (fuel : Nat) (M : MR_Machine) (s : Bool) (t : IntTy) (a : Nat) (ha : a < modulus (t.bits 64)) :
    mrUnOn fuel M .BitNot s t a = mrVal s t (modulus (t.bits 64) - 1 - a % modulus (t.bits 64)) := by
  have key : ((SInt.bnot (readAt s (t.bits 64) a)) % Int.ofNat (modulus (t.bits 64))).toNat =
      modulus (t.bits 64) - 1 - a % modulus (t.bits 64) := by
    unfold SInt.bnot
    rw [Nat.mod_eq_of_lt ha, ← Nat.mod_eq_of_lt (show modulus (t.bits 64) - 1 - a < modulus (t.bits 64) by omega)]
    unfold readAt
    split
    · refine resid_lin _ _ _ 0 ?_; simp only [Int.ofNat_eq_natCast]; omega
    · refine resid_lin _ _ _ (-1) ?_; simp only [Int.ofNat_eq_natCast]; omega
  have hr : modulus (t.bits 64) - 1 - a % modulus (t.bits 64) < modulus (t.bits 64) := by
    have := modulus_pos (t.bits 64); omega
  simp only [mrUnOn, MRf.Machine.eval_un_op, MRf.Machine.eval_int_un_op, SOut.bind_ok', mr_bib, mrVal,
    key, check_value_int _ _ _ _ _ hr, SRes.expect]


/-! ### Comparisons -/

def mrRelOn (fuel : Nat) (M : MR_Machine) (rop : MR_RelOp) (s : Bool) (t : IntTy) (a b : Nat) : MRRes :=
  MRf.Machine.eval_bin_op (fuel + 4) M (.Rel rop)
    (.Int (readAt s (t.bits 64) a), .Int (mrIntTy s t)) (.Int (readAt s (t.bits 64) b), .Int (mrIntTy s t))

theorem cmp_is_lt (x y : Int) : (SInt.cmp x y).is_lt = decide (x < y) := by
  unfold SInt.cmp SInt.blt SInt.beq
  by_cases h1 : x < y
  · simp [h1, SOrdering.is_lt]
  · by_cases h2 : x = y <;> simp [h1, h2, SOrdering.is_lt]
theorem cmp_is_gt (x y : Int) : (SInt.cmp x y).is_gt = decide (y < x) := by
  unfold SInt.cmp SInt.blt SInt.beq
  by_cases h1 : x < y
  · simp [h1, SOrdering.is_gt]; omega
  · by_cases h2 : x = y
    · simp [h1, h2, SOrdering.is_gt]
    · simp [h1, h2, SOrdering.is_gt]; omega
theorem cmp_is_eq (x y : Int) : (SInt.cmp x y).is_eq = decide (x = y) := by
  unfold SInt.cmp SInt.blt SInt.beq
  by_cases h1 : x < y
  · simp [h1, SOrdering.is_eq]; omega
  · by_cases h2 : x = y <;> simp [h1, h2, SOrdering.is_eq]
theorem cmp_is_le (x y : Int) : (SInt.cmp x y).is_le = decide (x ≤ y) := by
  unfold SOrdering.is_le; rw [cmp_is_gt]; by_cases h : y < x <;> simp [h, SBool.not] <;> omega
theorem cmp_is_ge (x y : Int) : (SInt.cmp x y).is_ge = decide (y ≤ x) := by
  unfold SOrdering.is_ge; rw [cmp_is_lt]; by_cases h : x < y <;> simp [h, SBool.not] <;> omega
theorem cmp_is_ne (x y : Int) : (SInt.cmp x y).is_ne = !decide (x = y) := by
  unfold SOrdering.is_ne; rw [cmp_is_eq]; by_cases h : x = y <;> simp [h, SBool.not]

theorem biased_readAt (w a : Nat) (hw : 0 < w) (ha : a < modulus w) :
    (Int.ofNat (biased w a)) = readAt true w a + Int.ofNat (half w) := by
  have hh := half_twice w hw
  unfold biased readAt
  by_cases hneg : half w ≤ a
  · simp only [Bool.true_and, hneg, decide_true, ↓reduceIte]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Int.ofNat_eq_natCast]; omega
  · simp only [Bool.true_and, hneg, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [Int.ofNat_eq_natCast]; omega

/-- The MiniRust comparison (and the signedness it reads at) for SemR's `ICmp`. -/
def mrRel (op : ICmpOp) (t : IntTy) : MR_RelOp × Bool :=
  match op with
  | .eq => (.Eq, t.signed) | .ne => (.Ne, t.signed)
  | .ult => (.Lt, false) | .ule => (.Le, false) | .ugt => (.Gt, false) | .uge => (.Ge, false)
  | .slt => (.Lt, true) | .sle => (.Le, true) | .sgt => (.Gt, true) | .sge => (.Ge, true)

theorem ofNat_lt_iff (a b : Nat) : (Int.ofNat a < Int.ofNat b) ↔ a < b := Int.ofNat_lt
theorem ofNat_le_iff (a b : Nat) : (Int.ofNat a ≤ Int.ofNat b) ↔ a ≤ b := Int.ofNat_le

theorem biased_lt (w a b : Nat) (hw : 0 < w) (ha : a < modulus w) (hb : b < modulus w) :
    (biased w a < biased w b) ↔ readAt true w a < readAt true w b := by
  have ba := biased_readAt w a hw ha
  have bb := biased_readAt w b hw hb
  constructor
  · intro h; have := Int.ofNat_lt.mpr h; simp only [Int.ofNat_eq_natCast] at *; omega
  · intro h; apply Int.ofNat_lt.mp; simp only [Int.ofNat_eq_natCast] at *; omega

theorem biased_le (w a b : Nat) (hw : 0 < w) (ha : a < modulus w) (hb : b < modulus w) :
    (biased w a ≤ biased w b) ↔ readAt true w a ≤ readAt true w b := by
  have ba := biased_readAt w a hw ha
  have bb := biased_readAt w b hw hb
  constructor
  · intro h; have := Int.ofNat_le.mpr h; simp only [Int.ofNat_eq_natCast] at *; omega
  · intro h; apply Int.ofNat_le.mp; simp only [Int.ofNat_eq_natCast] at *; omega

/-- SemR's integer comparisons ARE MiniRust's relational operators, for every
    integer type, comparison and pair of residues. -/
theorem icmp_minirust (fuel : Nat) (M : MR_Machine) (op : ICmpOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    mrRelOn fuel M (mrRel op t).1 (mrRel op t).2 t a b =
      SOut.ok (SRes.ok (.Bool (icmpR op (t.bits 64) a b), .Bool)) := by
  have hw : 0 < (t.bits 64) := by have := t.bits_ge_8; omega
  have eqv : ∀ s, (readAt s (t.bits 64) a = readAt s (t.bits 64) b) ↔ a = b := fun s =>
    ⟨readAt_inj s (t.bits 64) a b ha hb, fun e => e ▸ rfl⟩
  cases op <;>
  simp only [mrRelOn, mrRel, MRf.Machine.eval_bin_op, MRf.Machine.eval_rel_op, SOut.bind_ok', icmpR,
    cmp_is_lt, cmp_is_gt, cmp_is_eq, cmp_is_le, cmp_is_ge, cmp_is_ne, readAt_false, eqv,
    biased_lt (t.bits 64) a b hw ha hb, biased_lt (t.bits 64) b a hw hb ha, biased_le (t.bits 64) a b hw ha hb,
    biased_le (t.bits 64) b a hw hb ha, ofNat_lt_iff, ofNat_le_iff] <;>
  (try simp only [beq_iff_eq, bne_iff_ne, decide_not, ne_eq]) <;>
  (try rfl)


/-! ### The checked trio -/

def mrOvfOn (fuel : Nat) (M : MR_Machine) (mop : MR_IntBinOpWithOverflow) (s : Bool) (t : IntTy)
    (a b : Nat) : MRRes :=
  MRf.Machine.eval_bin_op (fuel + 4) M (.IntWithOverflow mop)
    (.Int (readAt s (t.bits 64) a), .Int (mrIntTy s t)) (.Int (readAt s (t.bits 64) b), .Int (mrIntTy s t))

/-- MiniRust's checked operator's result: the wrapped value and the overflow flag. -/
def mrOvfVal (fuel : Nat) (s : Bool) (t : IntTy) (r : Nat) (f : Bool) : MRRes :=
  (MRf.IntType.with_overflow (fuel + 3) (mrIntTy s t)).bind fun ty =>
    SOut.ok (SRes.ok (.Tuple [.Int (readAt s (t.bits 64) r), .Bool f], ty))

theorem snot_eq (x : Bool) : SBool.not x = !x := by cases x <;> rfl

section ovfs
variable (t : IntTy) (a b : Nat) (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64))
include ha hb

theorem readAt_signed_cases :
    (half (t.bits 64) ≤ a ∧ readAt true (t.bits 64) a = -Int.ofNat (modulus (t.bits 64) - a)) ∨
    (a < half (t.bits 64) ∧ readAt true (t.bits 64) a = Int.ofNat a) := by
  by_cases h : half (t.bits 64) ≤ a
  · left; refine ⟨h, ?_⟩; simp only [readAt, Bool.true_and, h, decide_true, ↓reduceIte,
      Int.ofNat_eq_natCast]; omega
  · right; refine ⟨by omega, ?_⟩; simp only [readAt, Bool.true_and, h, decide_false,
      Bool.false_eq_true, ↓reduceIte]

theorem mod_add_cases :
    (a + b < modulus (t.bits 64) ∧ (a + b) % modulus (t.bits 64) = a + b) ∨
    (modulus (t.bits 64) ≤ a + b ∧ (a + b) % modulus (t.bits 64) = a + b - modulus (t.bits 64)) := by
  by_cases h : a + b < modulus (t.bits 64)
  · left; exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right; refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem add_flag (s : Bool) :
    SBool.not (inRange s (t.bits 64) (readAt s (t.bits 64) a + readAt s (t.bits 64) b)) = (ovf .add s (t.bits 64) a b).2 := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  rw [snot_eq, Bool.eq_iff_iff]
  cases s <;> dsimp only [ovf] <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [inRange, readAt_false, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  · rcases mod_add_cases t a b ha hb with ⟨hs, hm⟩ | ⟨hs, hm⟩ <;> rw [hm] <;>
    rcases readAt_signed_cases t a b ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases readAt_signed_cases t b a hb ha with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    rw [e1, e2] <;>
    simp only [inRange, ↓reduceIte, isNeg, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_decide, Int.ofNat_eq_natCast] <;>
    omega


theorem mod_sub_cases :
    (b ≤ a ∧ (a + (modulus (t.bits 64) - b % modulus (t.bits 64))) % modulus (t.bits 64) = a - b) ∨
    (a < b ∧ (a + (modulus (t.bits 64) - b % modulus (t.bits 64))) % modulus (t.bits 64) = a + modulus (t.bits 64) - b) := by
  rw [Nat.mod_eq_of_lt hb]
  by_cases h : b ≤ a
  · left; refine ⟨h, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · right; refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem sub_flag (s : Bool) :
    SBool.not (inRange s (t.bits 64) (readAt s (t.bits 64) a - readAt s (t.bits 64) b)) = (ovf .sub s (t.bits 64) a b).2 := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  rw [snot_eq, Bool.eq_iff_iff]
  cases s <;> dsimp only [ovf] <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [inRange, readAt_false, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  · rcases mod_sub_cases t a b ha hb with ⟨hs, hm⟩ | ⟨hs, hm⟩ <;> rw [hm] <;>
    rcases readAt_signed_cases t a b ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
    rcases readAt_signed_cases t b a hb ha with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
    rw [e1, e2] <;>
    simp only [inRange, ↓reduceIte, isNeg, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_decide, Int.ofNat_eq_natCast] <;>
    omega

theorem readAt_mul :
    readAt true (t.bits 64) a * readAt true (t.bits 64) b =
      if isNeg (t.bits 64) a != isNeg (t.bits 64) b then -Int.ofNat (mag (t.bits 64) a * mag (t.bits 64) b)
      else Int.ofNat (mag (t.bits 64) a * mag (t.bits 64) b) := by
  have hm : ∀ x, x < modulus (t.bits 64) → mag (t.bits 64) x =
      if half (t.bits 64) ≤ x then modulus (t.bits 64) - x else x := by
    intro x _; unfold mag isNeg; by_cases h : half (t.bits 64) ≤ x <;> simp [h]
  rw [hm a ha, hm b hb]
  rcases readAt_signed_cases t a b ha hb with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
  rcases readAt_signed_cases t b a hb ha with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
  rw [e1, e2] <;>
  simp only [isNeg, h1, h2, decide_true, decide_false, ↓reduceIte, Nat.not_le.mpr, bne_self_eq_false,
    Bool.false_eq_true, Bool.true_bne, Bool.false_bne, Bool.not_true, Bool.not_false,
    Int.ofNat_mul_ofNat, Int.neg_mul_neg, Int.neg_mul, Int.mul_neg] <;>
  (try simp only [show ¬ half (t.bits 64) ≤ a by omega, show ¬ half (t.bits 64) ≤ b by omega, decide_false,
    ↓reduceIte, Bool.false_eq_true, Bool.true_bne, Bool.false_bne, Bool.not_true, Bool.not_false]) <;>
  (try simp only [Int.neg_neg]) <;> rfl

theorem mul_flag (s : Bool) :
    SBool.not (inRange s (t.bits 64) (readAt s (t.bits 64) a * readAt s (t.bits 64) b)) = (ovf .mul s (t.bits 64) a b).2 := by
  have hh := half_twice (t.bits 64) (bits_pos t a b ha hb)
  rw [snot_eq, Bool.eq_iff_iff]
  cases s <;> dsimp only [ovf] <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [readAt_false, show Int.ofNat a * Int.ofNat b = Int.ofNat (a * b) from rfl]
    generalize a * b = p
    simp only [inRange, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
      Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  · rw [readAt_mul t a b ha hb]
    generalize mag (t.bits 64) a * mag (t.bits 64) b = p
    cases isNeg (t.bits 64) a != isNeg (t.bits 64) b <;>
    simp only [inRange, ↓reduceIte, Bool.false_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq, Int.ofNat_eq_natCast] <;> omega

end ovfs


theorem resid_sub (w : Nat) (s : Bool) (a b : Nat) (ha : a < modulus w) (hb : b < modulus w) :
    ((readAt s w a - readAt s w b) % Int.ofNat (modulus w)).toNat =
      (a + (modulus w - b % modulus w)) % modulus w := by
  rw [Nat.mod_eq_of_lt hb, Int.sub_emod, readAt_emod w s a ha, readAt_emod w s b hb]
  refine resid_lin _ _ _ (-1) ?_
  simp only [Int.ofNat_eq_natCast]; omega

theorem resid_mul (w : Nat) (s : Bool) (a b : Nat) (ha : a < modulus w) (hb : b < modulus w) :
    ((readAt s w a * readAt s w b) % Int.ofNat (modulus w)).toNat = (a * b) % modulus w := by
  rw [Int.mul_emod, readAt_emod w s a ha, readAt_emod w s b hb]; rfl

/-- The MiniRust checked operator for SemR's `Overflow` trio. -/
def mrOvf : OvfOp → MR_IntBinOpWithOverflow
  | .add => .Add | .sub => .Sub | .mul => .Mul

/-- SemR's checked trio IS MiniRust's `IntWithOverflow` operators, for every
    integer type, both signednesses and every pair of residues: the wrapped
    value and the overflow flag. -/
theorem ovf_minirust (fuel : Nat) (M : MR_Machine) (op : OvfOp) (s : Bool) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    mrOvfOn fuel M (mrOvf op) s t a b =
      mrOvfVal fuel s t (ovf op s (t.bits 64) a b).1 (ovf op s (t.bits 64) a b).2 := by
  cases op <;>
  simp only [mrOvf, mrOvfOn, mrOvfVal, MRf.Machine.eval_bin_op, SOut.bind_ok', mr_can_represent, mr_bib,
    resid_add _ s a b ha hb, resid_sub _ s a b ha hb, resid_mul _ s a b ha hb,
    add_flag t a b ha hb s, sub_flag t a b ha hb s, mul_flag t a b ha hb s] <;> rfl

/-! ### SemR's operator layer is MiniRust's -/

/-- The MiniRust binary operator SemR's integer `BinOp` is, and the signedness
    MiniRust reads the residues at; `none` for the operators MiniRust has no
    counterpart for (they are SemR's own, by name). -/
def mrBin : BinOp → IntTy → Option (MR_IntBinOp × Bool)
  | .add, t => some (.Add, t.signed)
  | .sub, t => some (.Sub, t.signed)
  | .mul, t => some (.Mul, t.signed)
  | .udiv, _ => some (.Div, false)
  | .sdiv, _ => some (.Div, true)
  | .urem, _ => some (.Rem, false)
  | .srem, _ => some (.Rem, true)
  | .and, t => some (.BitAnd, t.signed)
  | .or, t => some (.BitOr, t.signed)
  | .xor, t => some (.BitXor, t.signed)
  | .shl, t => some (.ShlUnchecked, t.signed)
  | .lshr, _ => some (.ShrUnchecked, false)
  | .ashr, _ => some (.ShrUnchecked, true)
  | .bAnd, _ => none
  | .bOr, _ => none
  | .bXor, _ => none
  | .rotl, _ => none
  | .rotr, _ => none

/-- SemR's verdict and MiniRust's agree: the same value, or undefined
    behaviour on both sides. -/
def AgreeBin (s : Bool) (t : IntTy) : OpRes Nat → MRRes → Prop
  | .ok r, x => x = mrVal s t r
  | .ub _, x => ∃ msg, x = mrUb msg
  | _, _ => False

/-- **The operator lemma (binary).** For every integer type `t`, every binary
    operator with a MiniRust counterpart and every pair of residues, SemR's
    `intBin` is MiniRust's generated `eval_bin_op` (on any machine, with any
    fuel): value for value, undefined behaviour for undefined behaviour. -/
theorem intBin_minirust (fuel : Nat) (M : MR_Machine) (op : BinOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) (mop : MR_IntBinOp) (s : Bool)
    (h : mrBin op t = some (mop, s)) :
    AgreeBin s t (intBin op (t.bits 64) a b) (mrBinOn fuel M mop s t a b) := by
  cases op <;> simp only [mrBin, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [intBin, AgreeBin]
  · exact add_minirust fuel M _ t a b ha hb
  · exact sub_mr fuel M t a b ha hb _
  · exact mul_mr fuel M t a b ha hb _
  · rw [udiv_mr fuel M t a b ha hb]
    by_cases hb0 : b = 0
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
  · rw [sdiv_mr fuel M t a b ha hb]
    by_cases hb0 : b = 0
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
    · cases hov : (a == half (t.bits 64) && b == modulus (t.bits 64) - 1) <;> simp [hb0, hov, AgreeBin] <;> exact ⟨_, rfl⟩
  · rw [urem_mr fuel M t a b ha hb]
    by_cases hb0 : b = 0
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
  · rw [srem_mr fuel M t a b ha hb]
    by_cases hb0 : b = 0
    · simp [hb0, AgreeBin] <;> exact ⟨_, rfl⟩
    · cases hov : (a == half (t.bits 64) && b == modulus (t.bits 64) - 1) <;> simp [hb0, hov, AgreeBin] <;> exact ⟨_, rfl⟩
  · exact band_mr fuel M t a b ha hb _
  · exact bor_mr fuel M t a b ha hb _
  · exact bxor_mr fuel M t a b ha hb _
  · rw [shl_mr fuel M t a b ha hb]
    by_cases hs : (t.bits 64) ≤ b <;> simp [hs, AgreeBin] <;> exact ⟨_, rfl⟩
  · rw [lshr_mr fuel M t a b ha hb]
    by_cases hs : (t.bits 64) ≤ b <;> simp [hs, AgreeBin] <;> exact ⟨_, rfl⟩
  · rw [ashr_mr fuel M t a b ha hb]
    by_cases hs : (t.bits 64) ≤ b <;> simp [hs, AgreeBin] <;> exact ⟨_, rfl⟩

/-- The MiniRust unary operator SemR's integer `UnOp` is; `none` for SemR's own. -/
def mrUn : UnOp → Option MR_IntUnOp
  | .neg => some .Neg
  | .not => some .BitNot
  | .ctpop => none
  | .ctlz => none
  | .cttz => none
  | .bswap => none
  | .bitreverse => none

/-- **The operator lemma (unary).** -/
theorem intUn_minirust (fuel : Nat) (M : MR_Machine) (op : UnOp) (s : Bool) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits 64)) (uop : MR_IntUnOp) (h : mrUn op = some uop) :
    mrUnOn fuel M uop s t a = mrVal s t (intUn op (t.bits 64) a) := by
  cases op <;> simp only [mrUn, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp only [intUn]
  · exact neg_mr fuel M s t a ha
  · exact not_mr fuel M s t a ha

/-! ### `ctpop` (MiniRust's `CountOnes`) -/

theorem band_one (x : Int) : SInt.band x 1 = x % 2 := by
  cases x with
  | ofNat n =>
    show Int.ofNat (Nat.land n 1) = _
    have : Nat.land n 1 = n % 2 := Nat.and_one_is_mod n
    rw [this]; simp only [Int.ofNat_eq_natCast]; omega
  | negSucc n =>
    show Int.ofNat (1 - Nat.land 1 n) = _
    have : Nat.land 1 n = n % 2 := by
      show 1 &&& n = n % 2
      rw [Nat.and_comm]; exact Nat.and_one_is_mod n
    rw [this]; simp only [Int.negSucc_eq, Int.ofNat_eq_natCast]; omega

theorem shr_one (x : Int) : SInt.shr x 1 = SOut.ok (x / 2) := by
  cases x with
  | ofNat n =>
    show SOut.ok (Int.ofNat (n / Nat.pow 2 1)) = _
    congr 1
  | negSucc n =>
    show SOut.ok (Int.negSucc (n / Nat.pow 2 1)) = _
    congr 1

/-- `x` halved `n` times (floor). -/
def halveN : Nat → Int → Int
  | 0, x => x
  | n + 1, x => halveN n (x / 2)

/-- MiniRust's `count_ones` loop: `n` rounds of "add the low bit, shift right"
    from a value congruent to `a` modulo `2^n` add `popcount n a`. -/
theorem forS_count (n : Nat) (body : Int → Int × Int → SOut (SCtl (Int × Int) Int))
    (hbody : ∀ i o x, body i (o, x) = SOut.ok (SCtl.next (o + x % 2, x / 2))) :
    ∀ (i o x : Int) (a : Nat), a < 2 ^ n → (∃ q : Int, x = q * Int.ofNat (2 ^ n) + Int.ofNat a) →
      SLoop.forS (SList.rangeNat i n) (o, x) body =
        SOut.ok (SCtl.next (o + Int.ofNat (popcount n a), halveN n x)) := by
  induction n with
  | zero =>
    intro i o x a ha _
    have : a = 0 := by simp at ha; omega
    subst this
    simp [SList.rangeNat, SLoop.forS, popcount, halveN]
  | succ n ih =>
    intro i o x a ha ⟨q, hq⟩
    simp only [SList.rangeNat, SLoop.forS, hbody, SOut.bind_ok']
    have hp : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    generalize hP : (2 : Nat) ^ n = P at *
    rw [hp] at hq ha
    have hy : x = 2 * (q * Int.ofNat P) + Int.ofNat a := by
      rw [hq]; simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
      rw [Int.mul_left_comm]; rfl
    generalize hY : q * Int.ofNat P = y at hy
    have e1 : x % 2 = Int.ofNat (a % 2) := by simp only [Int.ofNat_eq_natCast] at *; omega
    have e2 : x / 2 = q * Int.ofNat P + Int.ofNat (a / 2) := by
      rw [hY]; simp only [Int.ofNat_eq_natCast] at *; omega
    rw [e1, ih (i + 1) (o + Int.ofNat (a % 2)) (x / 2) (a / 2) (by omega) ⟨q, e2⟩]
    simp only [popcount, halveN]
    congr 3
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]; omega

theorem readAt_lin (s : Bool) (w a : Nat) :
    ∃ q : Int, readAt s w a = q * Int.ofNat (2 ^ w) + Int.ofNat a := by
  unfold readAt
  split
  · exact ⟨-1, by simp only [modulus, Int.ofNat_eq_natCast]; omega⟩
  · exact ⟨0, by simp⟩

theorem count_range (t : IntTy) :
    SList.range 0 (SSize.bits (mrIntTy s t).size) = SList.rangeNat 0 (t.bits 64) := by
  cases t <;> rfl

theorem popcount_le : ∀ (w a : Nat), popcount w a ≤ w
  | 0, _ => Nat.le_refl 0
  | w + 1, a => by
    have := popcount_le w (a / 2)
    have : a % 2 < 2 := Nat.mod_lt _ (by decide)
    simp only [popcount]; omega

/-- MiniRust's `count_ones` on the reading of residue `a` is SemR's `popcount`. -/
theorem count_ones_mr (fuel : Nat) (s : Bool) (t : IntTy) (a : Nat) (ha : a < modulus (t.bits 64)) :
    MRf.Machine.eval_count_ones (fuel + 1) (readAt s (t.bits 64) a) (mrIntTy s t) =
      SOut.ok (Int.ofNat (popcount (t.bits 64) a)) := by
  obtain ⟨q, hq⟩ := readAt_lin s (t.bits 64) a
  simp only [MRf.Machine.eval_count_ones]
  rw [count_range, forS_count (t.bits 64) _ ?hb 0 0 _ a ha ⟨q, hq⟩]
  · simp only [SOut.bind_ok']; congr 1; simp only [Int.ofNat_eq_natCast]; omega
  · intro i o x
    simp only [band_one, shr_one, SOut.bind_ok']

/-- **The operator lemma (`ctpop`).** MiniRust's `CountOnes` counts the ones
    of the reading at the operand's width, as SemR's `ctpop` does; MiniRust
    types the count `u32` (Rust's `count_ones`), SemR at the operand type (the
    trust-ir instruction's result type). The count is the same number, below
    `2^8` either way. -/
theorem ctpop_minirust (fuel : Nat) (M : MR_Machine) (s : Bool) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits 64)) :
    mrUnOn fuel M .CountOnes s t a =
      SOut.ok (SRes.ok (.Int (Int.ofNat (intUn .ctpop (t.bits 64) a)), .Int (mrIntTy false .u32))) := by
  have hc : intUn .ctpop (t.bits 64) a < modulus (IntTy.u32.bits 64) := by
    have h1 := popcount_le (t.bits 64) a
    have h2 : (t.bits 64) ≤ 128 := by cases t <;> decide
    show popcount (t.bits 64) a < 2 ^ 32
    have : (128 : Nat) < 2 ^ 32 := by decide
    omega
  have hv := check_value_int fuel M false .u32 _ hc
  rw [readAt_false] at hv
  simp only [mrUnOn, MRf.Machine.eval_un_op, MRf.Machine.eval_int_un_op, count_ones_mr _ _ _ _ ha]
  have hu : SOption.unwrap (SSize.from_bytes 4) = SOut.ok 4 := rfl
  rw [hu]
  simp only [SOut.bind_ok']
  show SOut.bind (MRf.Machine.check_value (fuel + 3) M (MR_Value.Int (Int.ofNat (intUn .ctpop (t.bits 64) a)))
      (MR_Type.Int (mrIntTy false .u32))) _ = _
  rw [hv]
  rfl

/-! ### The value level

On operands of the instruction's integer type, SemR's value operators
(`evalBinop`, `evalUnop`, `evalIcmp`, `evalOverflow`) pass their type and
poison checks and are the residue operators, so the lemmas above hold of
them: SemR's value verdict and MiniRust's `eval_bin_op`/`eval_un_op` agree
value for value and undefined behaviour for undefined behaviour. What has no
MiniRust counterpart stays SemR's own, by name: the type and poison checks
themselves (trust-ir's dynamic checks; MiniRust's operators are typed
statically and have no poison operand — an uninitialized byte is refused when
it is loaded), the `Bool` binary operators (`boolBin`: this slice of
MiniRust's `BinOp` has no `Bool` arm), and the signed comparisons of `Bool`s. -/

theorem Ty.beq_int (t : IntTy) : (Ty.int t).beq (Ty.int t) = true := by cases t <;> rfl

/-- The executable value layer accepts a well-formed residue at this target. -/
theorem expectTy_int64 (t : IntTy) (a : Nat) (ha : a < modulus (t.bits 64)) :
    expectTy 64 (.int t a) (.int t) = .ok () := by
  simp [expectTy, Val.ty, Ty.beq_int, ha]

/-- On integer operands of its type, `evalBinop` is the residue operator `intBin`:
    the type and poison checks pass, and the verdict is `intBin`'s. -/
theorem evalBinop_int (op : BinOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    evalBinop 64 op (.int t) (.int t a) (.int t b) =
      (liftOp (intBin op (t.bits 64) a b) >>= fun r => pure (Val.int t r)) := by
  unfold evalBinop
  rw [expectTy_int64 t a ha]
  simp only [ok_bind]
  rw [expectTy_int64 t b hb]
  cases t <;> rfl

theorem evalUnop_int (op : UnOp) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits 64)) :
    evalUnop 64 op (.int t) (.int t a) = .ok (.int t (intUn op (t.bits 64) a)) := by
  unfold evalUnop
  rw [expectTy_int64 t a ha]
  cases t <;> rfl

theorem evalIcmp_int (op : ICmpOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    evalIcmp 64 op (.int t) (.int t a) (.int t b) = .ok (.bool (icmpR op (t.bits 64) a b)) := by
  unfold evalIcmp
  rw [expectTy_int64 t a ha]
  simp only [ok_bind]
  rw [expectTy_int64 t b hb]
  cases t <;> rfl

theorem evalOverflow_int (op : OvfOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    evalOverflow 64 op (.int t) (.int t a) (.int t b) =
      .ok [.int t (ovf op t.signed (t.bits 64) a b).1, .bool (ovf op t.signed (t.bits 64) a b).2] := by
  unfold evalOverflow
  rw [expectTy_int64 t a ha]
  simp only [ok_bind]
  rw [expectTy_int64 t b hb]
  cases t <;> rfl

/-- A SemR value verdict and MiniRust's agree: an integer of type `t` whose
    residue MiniRust holds (read at `s`), or undefined behaviour on both sides. -/
def AgreeVal (s : Bool) (t : IntTy) : R Val → MRRes → Prop
  | .ok v, x => ∃ r, v = .int t r ∧ x = mrVal s t r
  | .stop (.ub _), x => ∃ msg, x = mrUb msg
  | _, _ => False

/-- **The operator lemma at the value level (binary).** -/
theorem evalBinop_minirust (fuel : Nat) (M : MR_Machine) (op : BinOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) (mop : MR_IntBinOp) (s : Bool)
    (h : mrBin op t = some (mop, s)) :
    AgreeVal s t (evalBinop 64 op (.int t) (.int t a) (.int t b)) (mrBinOn fuel M mop s t a b) := by
  have hl := intBin_minirust fuel M op t a b ha hb mop s h
  rw [evalBinop_int op t a b ha hb]
  generalize intBin op (t.bits 64) a b = res at hl
  cases res with
  | ok r => exact ⟨r, rfl, hl⟩
  | ub m => exact hl
  | tyErr m => exact hl.elim
  | unsup f => exact hl.elim

theorem evalUnop_minirust (fuel : Nat) (M : MR_Machine) (op : UnOp) (s : Bool) (t : IntTy) (a : Nat)
    (ha : a < modulus (t.bits 64)) (uop : MR_IntUnOp) (h : mrUn op = some uop) :
    AgreeVal s t (evalUnop 64 op (.int t) (.int t a)) (mrUnOn fuel M uop s t a) := by
  rw [evalUnop_int op t a ha, intUn_minirust fuel M op s t a ha uop h]
  exact ⟨_, rfl, rfl⟩

theorem evalIcmp_minirust (fuel : Nat) (M : MR_Machine) (op : ICmpOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    evalIcmp 64 op (.int t) (.int t a) (.int t b) = .ok (.bool (icmpR op (t.bits 64) a b)) ∧
    mrRelOn fuel M (mrRel op t).1 (mrRel op t).2 t a b =
      SOut.ok (SRes.ok (.Bool (icmpR op (t.bits 64) a b), .Bool)) :=
  ⟨evalIcmp_int op t a b ha hb, icmp_minirust fuel M op t a b ha hb⟩

theorem evalOverflow_minirust (fuel : Nat) (M : MR_Machine) (op : OvfOp) (t : IntTy) (a b : Nat)
    (ha : a < modulus (t.bits 64)) (hb : b < modulus (t.bits 64)) :
    evalOverflow 64 op (.int t) (.int t a) (.int t b) =
      .ok [.int t (ovf op t.signed (t.bits 64) a b).1, .bool (ovf op t.signed (t.bits 64) a b).2] ∧
    mrOvfOn fuel M (mrOvf op) t.signed t a b =
      mrOvfVal fuel t.signed t (ovf op t.signed (t.bits 64) a b).1 (ovf op t.signed (t.bits 64) a b).2 :=
  ⟨evalOverflow_int op t a b ha hb, ovf_minirust fuel M op t.signed t a b ha hb⟩

/-- MiniRust's pointer size is 8 bytes (its slice's only target, x86_64): the
    width `mrIntTy` gives `isize`/`usize`, and the width trust-ir's interpreter
    gives them in a module with no target record. -/
theorem mr_ptr_size (fuel : Nat) : MRf.x86_64.PTR_SIZE (fuel + 1) = SOut.ok (mrIntTy true .isize).size :=
  rfl

theorem mr_usize (fuel : Nat) : MRf.IntType.usize_ty (fuel + 2) = SOut.ok (mrIntTy false .usize) :=
  rfl

/-- The MiniRust relational operator SemR's `ICmp` on `Bool` operands is: the
    equalities and the unsigned orders (`false < true`, MiniRust's `Bool`
    order); `none` for the signed ones, which read a `Bool` as a 1-bit signed
    integer (`true` is −1) and have no MiniRust counterpart. -/
def mrRelB : ICmpOp → Option MR_RelOp
  | .eq => some .Eq | .ne => some .Ne | .ult => some .Lt | .ule => some .Le | .ugt => some .Gt
  | .uge => some .Ge | .slt => none | .sle => none | .sgt => none | .sge => none

theorem evalIcmp_bool (op : ICmpOp) (x y : Bool) :
    evalIcmp 64 op .bool (.bool x) (.bool y) = .ok (.bool (icmpR op 1 (b2n x) (b2n y))) := rfl

/-- **The operator lemma (`ICmp` on `Bool`).** -/
theorem icmp_bool_minirust (fuel : Nat) (M : MR_Machine) (op : ICmpOp) (x y : Bool) (rop : MR_RelOp)
    (h : mrRelB op = some rop) :
    MRf.Machine.eval_bin_op (fuel + 4) M (.Rel rop) (.Bool x, .Bool) (.Bool y, .Bool) =
      SOut.ok (SRes.ok (.Bool (icmpR op 1 (b2n x) (b2n y)), .Bool)) := by
  cases op <;> simp only [mrRelB, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    cases x <;> cases y <;> rfl

end SemR

end
