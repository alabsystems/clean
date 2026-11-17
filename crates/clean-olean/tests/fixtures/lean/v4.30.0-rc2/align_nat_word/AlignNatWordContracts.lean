/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
import AlignNatWord

set_option autoImplicit false

namespace AlignNatWordContracts

-- Independent complete proposition literals, not the type of a named lemma.
def divBridge : Prop :=
  ∀ a b : UInt64, b ≠ 0 →
    (AlignNatWord.div64 a b).toNat =
      CICL.LiteralRules.NatBinOp.eval .div a.toNat b.toNat

def modBridge : Prop :=
  ∀ a b : UInt64, b ≠ 0 →
    (AlignNatWord.mod64 a b).toNat =
      CICL.LiteralRules.NatBinOp.eval .mod a.toNat b.toNat

-- Each literal is exactly one operation substitution in its real contract.
def swappedDivBridge : Prop :=
  ∀ a b : UInt64, b ≠ 0 →
    (AlignNatWord.mod64 a b).toNat =
      CICL.LiteralRules.NatBinOp.eval .div a.toNat b.toNat

def swappedModBridge : Prop :=
  ∀ a b : UInt64, b ≠ 0 →
    (AlignNatWord.div64 a b).toNat =
      CICL.LiteralRules.NatBinOp.eval .mod a.toNat b.toNat

theorem swappedDivBridge_refuted : ¬ swappedDivBridge := by
  intro h
  have witness := h 7 2 (by decide)
  change (1 : Nat) = 3 at witness
  exact (by decide : (1 : Nat) ≠ 3) witness

theorem swappedModBridge_refuted : ¬ swappedModBridge := by
  intro h
  have witness := h 7 2 (by decide)
  change (3 : Nat) = 1 at witness
  exact (by decide : (3 : Nat) ≠ 1) witness

end AlignNatWordContracts
