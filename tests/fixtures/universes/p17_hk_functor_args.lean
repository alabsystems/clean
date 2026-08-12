-- Type→Type functor arguments (the ITree-HK lane, probed 2026-08-08):
-- lambda functors, monomorphic def/inductive functors, and implicit
-- higher-kinded metavariable solving all WORK today.
def apF (E : Type → Type) (X : Type) : Type := E X

def viaLambda : Type := apF (fun X => Prod X Nat) Nat
def viaEta : Type := apF (fun X => Option X) Nat

inductive BoxM (A : Type) where
  | mk : A → BoxM A
def viaMonoInductive : Type := apF BoxM Nat

def idHK {F : Type → Type} {X : Type} (v : F X) : F X := v
def hkMetaSolved : Option Nat := idHK (some Nat.zero)
