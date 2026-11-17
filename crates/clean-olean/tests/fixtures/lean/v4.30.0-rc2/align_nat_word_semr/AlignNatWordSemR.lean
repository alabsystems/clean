/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import Init.Data.UInt.Lemmas
import AlignNatWord
import SemR

set_option autoImplicit false

/-! Canonical scalar semantics only. No compiler bytes, execution body,
    extern or runtime implementation is claimed by these mathematical lemmas. -/
namespace AlignNatWordSemR

def word (a : UInt64) : SemR.Val := .int .u64 a.toNat

theorem word_inj {a b : UInt64} : word a = word b ↔ a = b := by
  constructor
  · intro same
    have raw : a.toNat = b.toNat := (SemR.Val.int.inj same).2
    exact UInt64.toNat_inj.mp raw
  · intro same
    cases same
    rfl

theorem expect_word (pointerBits : Nat) (a : UInt64) :
    SemR.expectTy pointerBits (word a) (.int .u64) = .ok () := by
  change (if a.toNat < 2 ^ 64 then SemR.R.ok () else
    SemR.tyR "TypeError: integer value is out of range for the target width") = .ok ()
  exact if_pos a.toNat_lt

theorem nat_nonzero {b : UInt64} (nonzero : b ≠ 0) : b.toNat ≠ 0 := by
  intro zero
  apply nonzero
  exact UInt64.toNat_inj.mp zero

theorem udiv_word (pointerBits : Nat) (a b : UInt64) (nonzero : b ≠ 0) :
    SemR.evalBinop pointerBits .udiv (.int .u64) (word a) (word b) =
      .ok (word (AlignNatWord.div64 a b)) := by
  have nz := nat_nonzero nonzero
  unfold SemR.evalBinop
  rw [expect_word, SemR.ok_bind, expect_word, SemR.ok_bind]
  change SemR.R.bind
    (SemR.liftOp (if b.toNat == 0 then .ub "unsigned division by zero"
      else .ok (a.toNat / b.toNat)))
    (fun r => .ok (.int .u64 r)) = .ok (word (AlignNatWord.div64 a b))
  rw [show (b.toNat == 0) = false from beq_eq_false_iff_ne.mpr nz]
  rfl

theorem urem_word (pointerBits : Nat) (a b : UInt64) (nonzero : b ≠ 0) :
    SemR.evalBinop pointerBits .urem (.int .u64) (word a) (word b) =
      .ok (word (AlignNatWord.mod64 a b)) := by
  have nz := nat_nonzero nonzero
  unfold SemR.evalBinop
  rw [expect_word, SemR.ok_bind, expect_word, SemR.ok_bind]
  change SemR.R.bind
    (SemR.liftOp (if b.toNat == 0 then .ub "unsigned remainder by zero"
      else .ok (a.toNat % b.toNat)))
    (fun r => .ok (.int .u64 r)) = .ok (word (AlignNatWord.mod64 a b))
  rw [show (b.toNat == 0) = false from beq_eq_false_iff_ne.mpr nz]
  rfl

-- The raw operator stops with UB. Rust's preceding Assert has a separate panic
-- semantics and is not executed or asserted by these propositions.
theorem udiv_zero (pointerBits : Nat) (a : UInt64) :
    SemR.evalBinop pointerBits .udiv (.int .u64) (word a) (word 0) =
      .stop (.ub "unsigned division by zero") := by
  unfold SemR.evalBinop
  rw [expect_word, SemR.ok_bind, expect_word, SemR.ok_bind]
  rfl

theorem urem_zero (pointerBits : Nat) (a : UInt64) :
    SemR.evalBinop pointerBits .urem (.int .u64) (word a) (word 0) =
      .stop (.ub "unsigned remainder by zero") := by
  unfold SemR.evalBinop
  rw [expect_word, SemR.ok_bind, expect_word, SemR.ok_bind]
  rfl

theorem udiv_success_iff (pointerBits : Nat) (a b q : UInt64) :
    SemR.evalBinop pointerBits .udiv (.int .u64) (word a) (word b) = .ok (word q) ↔
      b ≠ 0 ∧ q = AlignNatWord.div64 a b := by
  by_cases nonzero : b = 0
  · subst b
    rw [udiv_zero]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact (impossible.1 rfl).elim
  · rw [udiv_word pointerBits a b nonzero]
    constructor
    · intro result
      exact ⟨nonzero, (word_inj.mp (SemR.R.ok.inj result)).symm⟩
    · rintro ⟨_, rfl⟩
      rfl

theorem urem_success_iff (pointerBits : Nat) (a b q : UInt64) :
    SemR.evalBinop pointerBits .urem (.int .u64) (word a) (word b) = .ok (word q) ↔
      b ≠ 0 ∧ q = AlignNatWord.mod64 a b := by
  by_cases nonzero : b = 0
  · subst b
    rw [urem_zero]
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact (impossible.1 rfl).elim
  · rw [urem_word pointerBits a b nonzero]
    constructor
    · intro result
      exact ⟨nonzero, (word_inj.mp (SemR.R.ok.inj result)).symm⟩
    · rintro ⟨_, rfl⟩
      rfl

end AlignNatWordSemR
