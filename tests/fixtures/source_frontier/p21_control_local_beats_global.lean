-- p21 — CLASS I selection: a valid local dictionary precedes a global one.
--
-- Updated 2026-11-06 after actual Lean4.30/4.35 comparison. Reducible
-- definition aliases are valid bracketed headers. The local dictionary wins
-- at MyC Nat even with globalMyCNat available; rfl checks its exact field.
-- A second class has no global dictionary, so localSupplies independently
-- checks the local's availability. Explicit class projection parameters keep
-- both programs valid Lean source.
--
-- Original source, old global-choice assertion and actual refusal evidence
-- remain in reports/source-frontier-header-2026-11-06/. That old positive was
-- not a valid Lean control. The source battery retains its exact10-decl pin.
class MyC (a : Type) where
  w : Nat

class MyE (a : Type) where
  v : Nat

instance globalMyCNat : MyC Nat where
  w := 7

@[reducible] def MyCAll : Type 1 := (a : Type) → MyC a

@[reducible] def MyEAll : Type 1 := (a : Type) → MyE a

def wAt (a : Type) [MyC a] : Nat := MyC.w a

def vAt (a : Type) [MyE a] : Nat := MyE.v a

def localWins [h : MyCAll] : Nat := wAt Nat

theorem localWinsEqDictionary (h : MyCAll) : @localWins h = (h Nat).w := rfl

def localSupplies [h : MyEAll] : Nat := vAt Nat
