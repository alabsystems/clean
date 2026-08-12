-- The prelude binder-fidelity battery (4-lane audit, 2026-08-10):
-- every Lean-valid spelling here previously FAILED against the
-- hand-registered prelude. Fixed: Decidable.isTrue/isFalse +
-- Nonempty.intro + Subtype.mk/val/property + Nat.le.refl params →
-- implicit; Eq.refl's a + decide's p + OfNat.ofNat's n → explicit;
-- Prod/PProd/Inhabited/BEq/DecidableEq/Add/Mul/Sub/LE/LT/OfNat/
-- HAdd-family/Pow TYPE FORMERS → explicit (the P18 class); PSum wired
-- in; imax(?u,?v) =?= concrete solver arm (congrFun/congr).
def dt : Decidable True := Decidable.isTrue True.intro
def df : Decidable False := Decidable.isFalse (fun h => h)
def ne1 : Nonempty Nat := Nonempty.intro 0
def er : (a : Nat) → Eq a a := Eq.refl
theorem er2 : Eq 2 2 := Eq.refl 2
def hof2 (F : Type → Type → Type) : Type := F Nat Bool
def useProd : Type := hof2 Prod
def usePProd : Type := hof2 PProd
def sm : Subtype (fun n : Nat => n = n) := Subtype.mk 5 rfl
def sv (s : Subtype (fun n : Nat => n = n)) : Nat := Subtype.val s
def sp (s : Subtype (fun n : Nat => n = n)) : s.val = s.val := Subtype.property s
def hofI (F : Type → Type) : Type := F Nat
def useInh : Type := hofI Inhabited
def useBEq : Type := hofI BEq
def useAdd : Type := hofI Add
def useMul : Type := hofI Mul
def useSub : Type := hofI Sub
def useLE : Type := hofI LE
def useLT : Type := hofI LT
def dec1 : Bool := Decidable.decide (Eq 2 2)
theorem cf2 (f g : Nat → Nat) (h : f = g) (a : Nat) : f a = g a := congrFun h a
def ps1 : PSum Nat Bool := PSum.inl 3
def on1 : Nat := OfNat.ofNat 5
