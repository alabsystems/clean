def isigmaStep.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (X : I → Type u) (i : I) : Type u :=
  Sigma (fun a : A i => (b : B i a) → X (t i a b))

def isigmaStepMk.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {X : I → Type u} {i : I}
    (a : A i) (f : (b : B i a) → X (t i a b)) : isigmaStep A B t X i :=
  Sigma.mk a f

def iapprox.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (n : Nat) : I → Type u :=
  Nat.rec (motive := fun _ => I → Type u)
    (fun _ => PUnit)
    (fun _ ih => isigmaStep A B t ih) n

theorem iapprox_zero.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    iapprox A B t Nat.zero i = PUnit := rfl

theorem iapprox_succ.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (n : Nat) (i : I) :
    iapprox A B t (Nat.succ n) i = isigmaStep A B t (iapprox A B t n) i := rfl

def izero.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} :
    iapprox A B t Nat.zero i := PUnit.unit

def iasStep.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : iapprox A B t (Nat.succ n) i) : isigmaStep A B t (iapprox A B t n) i := x

def imkAt.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat) (i : I)
    (a : A i) (f : (b : B i a) → iapprox A B t n (t i a b)) :
    isigmaStep A B t (iapprox A B t n) i :=
  Sigma.mk a f

def ifromStep.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : isigmaStep A B t (iapprox A B t n) i) : iapprox A B t (Nat.succ n) i := x

def itruncBase.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (i : I) → iapprox A B t (Nat.succ Nat.zero) i → iapprox A B t Nat.zero i :=
  fun i _ => @izero I A B t i

def itruncStep.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat)
    (ih : (i : I) → iapprox A B t (Nat.succ n) i → iapprox A B t n i) :
    (i : I) → iapprox A B t (Nat.succ (Nat.succ n)) i → iapprox A B t (Nat.succ n) i :=
  fun i x =>
    @ifromStep I A B t n i
      (@imkAt I A B t n i (@iasStep I A B t (Nat.succ n) i x).1
        (fun (b : B i (@iasStep I A B t (Nat.succ n) i x).1) =>
          ih (t i (@iasStep I A B t (Nat.succ n) i x).1 b)
            ((@iasStep I A B t (Nat.succ n) i x).2 b)))

def itruncate.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (n : Nat) → (i : I) → iapprox A B t (Nat.succ n) i → iapprox A B t n i :=
  Nat.rec
    (motive := fun n => (i : I) → iapprox A B t (Nat.succ n) i → iapprox A B t n i)
    (@itruncBase I A B t)
    (@itruncStep I A B t)

def IMPred.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    ((n : Nat) → iapprox A B t n i) → Prop :=
  fun f => ∀ n : Nat, @itruncate I A B t n i (f (Nat.succ n)) = f n

def IMIntl.{u} {I : Type u} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) : Type u :=
  Subtype (IMPred A B t i)

def IMhead.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl A B t i) : A i :=
  (@iasStep I A B t Nat.zero i (m.val (Nat.succ Nat.zero))).1

theorem ilabel_step.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl A B t i) (n : Nat) :
    (@iasStep I A B t (Nat.succ n) i (m.val (Nat.succ (Nat.succ n)))).1
      = (@iasStep I A B t n i (m.val (Nat.succ n))).1 :=
  congrArg
    (fun z : isigmaStep A B t (iapprox A B t n) i => z.1)
    (m.property (Nat.succ n))

theorem ilabel_stable.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl A B t i) :
    ∀ n : Nat,
      (@iasStep I A B t n i (m.val (Nat.succ n))).1 = IMhead m :=
  Nat.rec
    (motive := fun n =>
      (@iasStep I A B t n i (m.val (Nat.succ n))).1 = IMhead m)
    rfl
    (fun n ih => Eq.trans (ilabel_step m n) ih)

def icorecApprox.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type u}
    (g : (j : I) → S j → isigmaStep A B t S j) :
    (n : Nat) → (j : I) → S j → iapprox A B t n j :=
  Nat.rec (motive := fun k => (j : I) → S j → iapprox A B t k j)
    (fun j _ => @izero I A B t j)
    (fun n ih => fun j s =>
      @ifromStep I A B t n j
        (@imkAt I A B t n j (g j s).1
          (fun b => ih (t j (g j s).1 b) ((g j s).2 b))))

theorem icorec_coherent.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type u}
    (g : (j : I) → S j → isigmaStep A B t S j) :
    ∀ (n : Nat) (j : I) (s : S j),
      @itruncate I A B t n j (icorecApprox g (Nat.succ n) j s)
        = icorecApprox g n j s :=
  Nat.rec
    (motive := fun n =>
      ∀ (j : I) (s : S j),
        @itruncate I A B t n j (icorecApprox g (Nat.succ n) j s)
          = icorecApprox g n j s)
    (fun j s => rfl)
    (fun n ih => fun j s =>
      congrArg
        (fun f : (b : B j (g j s).1) → iapprox A B t n (t j (g j s).1 b) =>
          @ifromStep I A B t n j (@imkAt I A B t n j (g j s).1 f))
        (funext (fun b =>
          ih (t j (g j s).1 b) ((g j s).2 b))))

def IMcorec.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type u}
    (g : (j : I) → S j → isigmaStep A B t S j) (j : I) (s : S j) :
    IMIntl A B t j :=
  Subtype.mk (IMPred A B t j)
    (fun n => icorecApprox g n j s)
    (fun n => icorec_coherent g n j s)

theorem IMcorec_head.{u} {I : Type u} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type u}
    (g : (j : I) → S j → isigmaStep A B t S j) (j : I) (s : S j) :
    IMhead (IMcorec g j s) = (g j s).1 := rfl
