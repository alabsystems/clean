-- p21 — CLASS I risk axis (a): AMBIGUITY. Two instances can answer one goal;
-- which one wins must not have moved.
--
-- The candidate-side match is consulted only after the primary search has
-- already returned `None`, so no goal that resolved before can resolve
-- differently now. This file is that claim made observable rather than
-- asserted, in two halves that only mean something together:
--
--   HALF 1 (`globalWinsIsSeven`) — THE COMPARABLE HALF, and the one that
--     carries the claim. Inside `globalWins`, the goal `MyC Nat` can be
--     answered by the global `globalMyCNat` OR by the telescoped local
--     `[h : MyCAll]`, where `MyCAll := (a : Type) → MyC a`. `rfl` is what
--     measures the choice: `globalWins` reduces to `7` only if the GLOBAL was
--     selected. The instance is applied EXPLICITLY (`@globalWins h`) on
--     purpose — that is what makes this half elaborate on a pre-stage-I-1
--     binary too, so BEFORE and AFTER are the same measurement and not two
--     different ones. Measured 2026-08-26: 6 passed / 0 failed on BOTH
--     binaries, same tree.
--
--   HALF 2 (`localSupplies`) — the half that stops half 1 being vacuous. The
--     same telescoped shape at a class with NO global instance registered:
--     the local supplies the goal. A candidate that could never be chosen
--     anyway would prove nothing about precedence. This half is necessarily
--     AFTER-only — before stage I-1 it failed
--     `UnsynthesizedInstanceGoal { goal: "MyE Nat" }`.
--
-- Together: the new candidate is real, and it still loses to everything that
-- already won.
class MyC (a : Type) where
  w : Nat

class MyE (a : Type) where
  v : Nat

instance globalMyCNat : MyC Nat where
  w := 7

def MyCAll : Type 1 := (a : Type) → MyC a

def MyEAll : Type 1 := (a : Type) → MyE a

def wAt (a : Type) [MyC a] : Nat := MyC.w

def vAt (a : Type) [MyE a] : Nat := MyE.v

def globalWins [h : MyCAll] : Nat := wAt Nat

theorem globalWinsIsSeven (h : MyCAll) : @globalWins h = 7 := rfl

def localSupplies [h : MyEAll] : Nat := vAt Nat
