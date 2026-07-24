-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Public demo: SOUND MUTUAL STRUCTURAL RECURSION (Track H, task 2).
--
-- A `mutual ... end` block whose members all recurse structurally on a single
-- shared inductive argument — the canonical even/odd:
--
--   mutual
--     def isEven : Nat -> Bool | 0 => true  | Nat.succ n => isOdd n
--     def isOdd  : Nat -> Bool | 0 => false | Nat.succ n => isEven n
--   end
--
-- Before this change the cross-references registered as `Const isOdd` before
-- `isOdd` existed, so the kernel rejected them ("Unknown constant: isOdd"); and
-- even with both registered, two mutually self-referencing `Const` values are
-- not a kernel-acceptable terminating definition.
--
-- Clean now lowers the block — with NO `WellFounded.fix`, `sorry`, or faked
-- termination axiom — into ONE structurally-recursive packed function returning
-- a tuple of the components' results, plus thin projection wrappers:
--
--   def isEven.isOdd.pack : Nat -> Prod Bool Bool
--     | 0          => Prod.mk true false
--     | Nat.succ n => Prod.mk (Prod.snd (isEven.isOdd.pack n))
--                             (Prod.fst (isEven.isOdd.pack n))
--   def isEven (x : Nat) : Bool := Prod.fst (isEven.isOdd.pack x)
--   def isOdd  (x : Nat) : Bool := Prod.snd (isEven.isOdd.pack x)
--
-- The packed function is an ordinary single-argument structural recursion on
-- the shared inductive, so it reuses the already-proven equation-form `T.rec`
-- lowering verbatim. Each cross-call becomes a product projection of the pack;
-- the wrappers are non-recursive projections. Soundness is inherited wholesale
-- from the structural-recursion path plus the kernel's `Prod` eliminator. The
-- `rfl` theorems force the kernel to reduce the single lowered `Nat.rec`
-- application across the mutual cycle.

mutual
  def isEven : Nat -> Bool
    | 0 => true
    | Nat.succ n => isOdd n
  def isOdd : Nat -> Bool
    | 0 => false
    | Nat.succ n => isEven n
end

theorem ev0 : isEven 0 = true := rfl
theorem ev4 : isEven 4 = true := rfl
theorem ev3 : isEven 3 = false := rfl
theorem od0 : isOdd 0 = false := rfl
theorem od3 : isOdd 3 = true := rfl
theorem od4 : isOdd 4 = false := rfl

-- Three-way mutual cycle: residue classes mod 3, lowered to ONE structural
-- `Nat.rec` returning a `Prod Bool (Prod Bool Bool)`.
mutual
  def isZeroMod3 : Nat -> Bool
    | 0 => true
    | Nat.succ n => isTwoMod3 n
  def isOneMod3 : Nat -> Bool
    | 0 => false
    | Nat.succ n => isZeroMod3 n
  def isTwoMod3 : Nat -> Bool
    | 0 => false
    | Nat.succ n => isOneMod3 n
end

theorem z6 : isZeroMod3 6 = true := rfl
theorem o4 : isOneMod3 4 = true := rfl
theorem t5 : isTwoMod3 5 = true := rfl
theorem z5 : isZeroMod3 5 = false := rfl
