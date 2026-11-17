/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import AlignNatWordSemR

set_option autoImplicit false

namespace AlignNatWordSemRContracts

-- Independent complete proposition literals, never the type of a named proof.
def divGuarded : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64, b ≠ 0 →
  SemR.evalBinop pointerBits .udiv (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.div64 a b))

def modGuarded : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64, b ≠ 0 →
  SemR.evalBinop pointerBits .urem (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.mod64 a b))

def divSuccess : Prop := ∀ pointerBits : Nat, ∀ a b q : UInt64,
  SemR.evalBinop pointerBits .udiv (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) = .ok (AlignNatWordSemR.word q) ↔
      b ≠ 0 ∧ q = AlignNatWord.div64 a b

def modSuccess : Prop := ∀ pointerBits : Nat, ∀ a b q : UInt64,
  SemR.evalBinop pointerBits .urem (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) = .ok (AlignNatWordSemR.word q) ↔
      b ≠ 0 ∧ q = AlignNatWord.mod64 a b

def divZero : Prop := ∀ pointerBits : Nat, ∀ a : UInt64,
  SemR.evalBinop pointerBits .udiv (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word 0) =
      .stop (.ub "unsigned division by zero")

def modZero : Prop := ∀ pointerBits : Nat, ∀ a : UInt64,
  SemR.evalBinop pointerBits .urem (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word 0) =
      .stop (.ub "unsigned remainder by zero")

-- Each swap changes exactly the one logical result-operation constant.
def swappedDiv : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64, b ≠ 0 →
  SemR.evalBinop pointerBits .udiv (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.mod64 a b))

def swappedMod : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64, b ≠ 0 →
  SemR.evalBinop pointerBits .urem (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.div64 a b))

-- Each omission deletes exactly the one nonzero binder from the guarded literal.
def unguardedDiv : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64,
  SemR.evalBinop pointerBits .udiv (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.div64 a b))

def unguardedMod : Prop := ∀ pointerBits : Nat, ∀ a b : UInt64,
  SemR.evalBinop pointerBits .urem (.int .u64)
    (AlignNatWordSemR.word a) (AlignNatWordSemR.word b) =
      .ok (AlignNatWordSemR.word (AlignNatWord.mod64 a b))

theorem swappedDiv_refuted : ¬ swappedDiv := by
  intro h
  have witness := h 64 5 2 (by decide)
  rw [AlignNatWordSemR.udiv_word 64 5 2 (by decide)] at witness
  have bad : (2 : UInt64) = 1 := AlignNatWordSemR.word_inj.mp (SemR.R.ok.inj witness)
  exact (by decide : (2 : UInt64) ≠ 1) bad

theorem swappedMod_refuted : ¬ swappedMod := by
  intro h
  have witness := h 64 5 2 (by decide)
  rw [AlignNatWordSemR.urem_word 64 5 2 (by decide)] at witness
  have bad : (1 : UInt64) = 2 := AlignNatWordSemR.word_inj.mp (SemR.R.ok.inj witness)
  exact (by decide : (1 : UInt64) ≠ 2) bad

theorem unguardedDiv_refuted : ¬ unguardedDiv := by
  intro h
  have witness := h 64 0 0
  rw [AlignNatWordSemR.udiv_zero] at witness
  cases witness

theorem unguardedMod_refuted : ¬ unguardedMod := by
  intro h
  have witness := h 64 0 0
  rw [AlignNatWordSemR.urem_zero] at witness
  cases witness

end AlignNatWordSemRContracts
