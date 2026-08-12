-- The TWO-UNIVERSE indexed-M core probe (index I : Type v, families at
-- Type u, carriers at Type (max u v)) — the seed shape for indexed
-- codata .{u}. Also pins the level-expression precedence fix:
-- `max u v + 1` is `(max u v) + 1` (Lean grammar), which this file's
-- PUnit.{max u v + 1} law exercises unparenthesized.
def isigmaStep2.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (X : I → Type (max u v)) (i : I) :
    Type (max u v) :=
  Sigma (fun a : A i => (b : B i a) → X (t i a b))

def iapprox2.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (n : Nat) : I → Type (max u v) :=
  Nat.rec (motive := fun _ => I → Type (max u v))
    (fun _ => PUnit)
    (fun _ ih => isigmaStep2 A B t ih) n

def izero2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} :
    iapprox2 A B t Nat.zero i := PUnit.unit

def iasStep2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : iapprox2 A B t (Nat.succ n) i) : isigmaStep2 A B t (iapprox2 A B t n) i := x

def ifromStep2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : isigmaStep2 A B t (iapprox2 A B t n) i) : iapprox2 A B t (Nat.succ n) i := x

def imkAt2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat) (i : I)
    (a : A i) (f : (b : B i a) → iapprox2 A B t n (t i a b)) :
    isigmaStep2 A B t (iapprox2 A B t n) i :=
  Sigma.mk a f

def itruncBase2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (i : I) → iapprox2 A B t (Nat.succ Nat.zero) i → iapprox2 A B t Nat.zero i :=
  fun i _ => @izero2.{u, v} I A B t i

def itruncStep2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat)
    (ih : (i : I) → iapprox2 A B t (Nat.succ n) i → iapprox2 A B t n i) :
    (i : I) → iapprox2 A B t (Nat.succ (Nat.succ n)) i → iapprox2 A B t (Nat.succ n) i :=
  fun i x =>
    @ifromStep2.{u, v} I A B t n i
      (@imkAt2.{u, v} I A B t n i (@iasStep2.{u, v} I A B t (Nat.succ n) i x).1
        (fun (b : B i (@iasStep2.{u, v} I A B t (Nat.succ n) i x).1) =>
          ih (t i (@iasStep2.{u, v} I A B t (Nat.succ n) i x).1 b)
            ((@iasStep2.{u, v} I A B t (Nat.succ n) i x).2 b)))

def itruncate2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (n : Nat) → (i : I) → iapprox2 A B t (Nat.succ n) i → iapprox2 A B t n i :=
  Nat.rec
    (motive := fun n => (i : I) → iapprox2 A B t (Nat.succ n) i → iapprox2 A B t n i)
    (@itruncBase2.{u, v} I A B t)
    (@itruncStep2.{u, v} I A B t)

def IMPred2.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    ((n : Nat) → iapprox2 A B t n i) → Prop :=
  fun f => ∀ n : Nat, @itruncate2.{u, v} I A B t n i (f (Nat.succ n)) = f n

def IMIntl2.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) : Type (max u v) :=
  Subtype (IMPred2 A B t i)

theorem iapprox2_zero.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    iapprox2 A B t Nat.zero i = PUnit.{max u v + 1} := rfl

-- the concrete indexed-lane instantiation shape: Nat index (v:=0), Type-u families
def natIdx.{u} (A : Nat → Type u) (B : (i : Nat) → A i → Type u)
    (t : (i : Nat) → (a : A i) → B i a → Nat) (i : Nat) : Type (max u 0) :=
  isigmaStep2 A B t (fun j => iapprox2 A B t Nat.zero j) i
