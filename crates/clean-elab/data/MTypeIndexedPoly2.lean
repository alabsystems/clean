/- MTypeIndexedPoly2 — the .{u, v} TWO-UNIVERSE sibling of
   MTypeIndexedPoly.lean (U2 rung 7, designs/2026-08-08-u2-universe-
   polymorphism-ladder.md). Same 229 declarations; the generic core is
   lifted to the p16-validated two-universe shape: index {I : Type v},
   families A,B : ... → Type u, towers/carriers at Type (max u v), tower
   base bare PUnit in value positions and PUnit.{max u v + 1} where an
   explicit type-level unit is needed. Decl heads gain .{u, v}; every
   reference to a lifted name is pinned with explicit .{u, v} levels
   (@-form and plain form — never positional). The QPFTypes capstones /
   mutual TreeS-ForestS / IStream / Grid sections and the concrete ITree
   computation instances stay monomorphic on purpose (Type 0 carriers,
   u := 0 / v := 0 through level metas). Kept at one universe by design:
   NoPos/itreeShape/itreePos/noEv/noAns (event-signature layer, Type u),
   isubtype_ext/iunit_eq (single-level helpers instantiated at max u v).

   Lift provenance: mechanical per-decl transform of MTypeIndexedPoly
   (script: transform.py, session 2026-08-08) — index binder u→v, family
   slots X/S and carriers u→max u v, u-lane index PUnit.{u+1}→PUnit.{v+1}
   (state PUnit in ispin → PUnit.{max u v + 1}), ibindSt/ITree carriers
   → Type (max u v), + .{u, v} reference pinning. Green 229/229 on first
   probe; split-universe instantiations (u,v)=(0,1) and (1,0) validated
   in a separate appendix probe with a negative control. -/

/- R2 brick 1: the INDEXED container M-tower (rung R2 of
   designs/2026-08-06-indexed-m-codata.md — the QPFTypes answers).

   An I-indexed container: shapes A i, positions B i a, target indices
   t i a b. The M-family carrier is the same Nat.rec approximation tower
   as the unindexed MType.lean, now valued in I → Type; the coherence
   predicate and Subtype carrier follow identically.

   Elaborator-battery lessons burned in here (each cost a probe cycle):
   - no `_` index holes under Nat.rec-into-family (free-variable leak);
   - the family-instance mk must be a raw Sigma.mk under a fully-ascribed
     per-instance wrapper (imkAt) — the generic isigmaStepMk's implicit
     family instantiation trips the whnf gap;
   - motives and signatures must spell their Pis SYNTACTICALLY — a type
     alias at an application site re-opens the gap as ExpectedPi;
   - plain `=` elaborates where the @Eq spelling fails (the reverse of
     the usual dodge). -/
def isigmaStep.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (X : I → Type (max u v)) (i : I) : Type (max u v) :=
  Sigma (fun a : A i => (b : B i a) → X (t i a b))

def isigmaStepMk.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {X : I → Type (max u v)} {i : I}
    (a : A i) (f : (b : B i a) → X (t i a b)) : isigmaStep.{u, v} A B t X i :=
  Sigma.mk a f

def iapprox.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (n : Nat) : I → Type (max u v) :=
  Nat.rec (motive := fun _ => I → Type (max u v))
    (fun _ => PUnit)
    (fun _ ih => isigmaStep.{u, v} A B t ih) n

theorem iapprox_zero.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    iapprox.{u, v} A B t Nat.zero i = PUnit.{max u v + 1} := rfl

theorem iapprox_succ.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (n : Nat) (i : I) :
    iapprox.{u, v} A B t (Nat.succ n) i = isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i := rfl

-- ascribed base inhabitant (same whnf-gap dodge, level zero)
def izero.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} :
    iapprox.{u, v} A B t Nat.zero i := PUnit.unit

-- ascribed identity coercions across the definitional iapprox unfolding
-- (dodges the ExpectedSort-without-whnf elaborator gap, as asStep did)
def iasStep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : iapprox.{u, v} A B t (Nat.succ n) i) : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i := x

def ifromStep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i) : iapprox.{u, v} A B t (Nat.succ n) i := x

def imkAt.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat) (i : I)
    (a : A i) (f : (b : B i a) → iapprox.{u, v} A B t n (t i a b)) :
    isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i :=
  Sigma.mk a f

-- hoisted, fully-ascribed base and step with SYNTACTIC Pi types (an
-- itruncTy alias at USE sites re-opens the whnf gap as an ExpectedPi
-- failure — the elaborator must see the Pi syntactically)
def itruncBase.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (i : I) → iapprox.{u, v} A B t (Nat.succ Nat.zero) i → iapprox.{u, v} A B t Nat.zero i :=
  fun i _ => @izero.{u, v} I A B t i

def itruncStep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} (n : Nat)
    (ih : (i : I) → iapprox.{u, v} A B t (Nat.succ n) i → iapprox.{u, v} A B t n i) :
    (i : I) → iapprox.{u, v} A B t (Nat.succ (Nat.succ n)) i → iapprox.{u, v} A B t (Nat.succ n) i :=
  fun i x =>
    @ifromStep.{u, v} I A B t n i
      (@imkAt.{u, v} I A B t n i (@iasStep.{u, v} I A B t (Nat.succ n) i x).1
        (fun (b : B i (@iasStep.{u, v} I A B t (Nat.succ n) i x).1) =>
          ih (t i (@iasStep.{u, v} I A B t (Nat.succ n) i x).1 b)
            ((@iasStep.{u, v} I A B t (Nat.succ n) i x).2 b)))

def itruncate.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} :
    (n : Nat) → (i : I) → iapprox.{u, v} A B t (Nat.succ n) i → iapprox.{u, v} A B t n i :=
  Nat.rec
    (motive := fun n => (i : I) → iapprox.{u, v} A B t (Nat.succ n) i → iapprox.{u, v} A B t n i)
    (@itruncBase.{u, v} I A B t)
    (@itruncStep.{u, v} I A B t)

def IMPred.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) :
    ((n : Nat) → iapprox.{u, v} A B t n i) → Prop :=
  fun f => ∀ n : Nat, @itruncate.{u, v} I A B t n i (f (Nat.succ n)) = f n

def IMIntl.{u, v} {I : Type v} (A : I → Type u) (B : (i : I) → A i → Type u)
    (t : (i : I) → (a : A i) → B i a → I) (i : I) : Type (max u v) :=
  Subtype (IMPred.{u, v} A B t i)

-- ── R2 brick 2: destructor head + label stability ── -/

def IMhead.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) : A i :=
  (@iasStep.{u, v} I A B t Nat.zero i (m.val (Nat.succ Nat.zero))).1

theorem ilabel_step.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) :
    (@iasStep.{u, v} I A B t (Nat.succ n) i (m.val (Nat.succ (Nat.succ n)))).1
      = (@iasStep.{u, v} I A B t n i (m.val (Nat.succ n))).1 :=
  congrArg
    (fun z : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i => z.1)
    (m.property (Nat.succ n))

theorem ilabel_stable.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) :
    ∀ n : Nat,
      (@iasStep.{u, v} I A B t n i (m.val (Nat.succ n))).1 = IMhead.{u, v} m :=
  Nat.rec
    (motive := fun n =>
      (@iasStep.{u, v} I A B t n i (m.val (Nat.succ n))).1 = IMhead.{u, v} m)
    rfl
    (fun n ih => Eq.trans (ilabel_step.{u, v} m n) ih)

-- the target-index transport: moving b across a label equality moves the
-- child's index correspondingly (Eq.rec; base collapses by cast-iota)
theorem it_congr.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} {l h : A i}
    (e : l = h) (b : B i h) :
    t i l (cast (congrArg (B i) (Eq.symm e)) b) = t i h b :=
  @Eq.rec (A i) l
    (fun h' e' =>
      ∀ b' : B i h',
        t i l (cast (congrArg (B i) (Eq.symm e')) b') = t i h' b')
    (fun b' => rfl) h e b

-- ascribed index-cast on approximants (hoisted; congrArg-in-statement
-- positions trip the whnf gap)
def icastAppr.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I}
    (e : j = j') (n : Nat) (x : iapprox.{u, v} A B t n j) : iapprox.{u, v} A B t n j' :=
  cast (congrArg (iapprox.{u, v} A B t n) e) x

-- minimal: itruncate applied to a plain binder
def lhs2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j' : I} (n : Nat)
    (y : iapprox.{u, v} A B t (Nat.succ n) j') : iapprox.{u, v} A B t n j' :=
  @itruncate.{u, v} I A B t n j' y


-- unblocked by the pattern-unifier fix: composition through the cast
def icastComp.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I} (e : j = j') (n : Nat)
    (x : iapprox.{u, v} A B t (Nat.succ n) j) : iapprox.{u, v} A B t n j' :=
  lhs2.{u, v} n (@icastAppr.{u, v} I A B t j j' e (Nat.succ n) x)

-- the commutation equation as an ascribed Prop (const-headed motive)
def itruncCastEq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I} (j' : I)
    (e : j = j') (n : Nat) (x : iapprox.{u, v} A B t (Nat.succ n) j) : Prop :=
  @itruncate.{u, v} I A B t n j' (@icastAppr.{u, v} I A B t j j' e (Nat.succ n) x)
    = @icastAppr.{u, v} I A B t j j' e n (@itruncate.{u, v} I A B t n j x)

theorem itrunc_cast.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I} (e : j = j') (n : Nat)
    (x : iapprox.{u, v} A B t (Nat.succ n) j) : itruncCastEq.{u, v} j' e n x :=
  @Eq.rec I j
    (fun j'' e' => itruncCastEq.{u, v} j'' e' n x)
    rfl j' e

-- ── R2 brick 3 prep: the child's cast + named label ──
-- (the blocker was the @-explicit-mode leak, fixed in clean-elab —
-- regression lock: elab_explicit_scope_regression.lean)

def icastB.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} {l h : A i}
    (e : l = h) (b : B i h) : B i l :=
  cast (congrArg (B i) (Eq.symm e)) b

def ilabelN.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : A i :=
  (@iasStep.{u, v} I A B t n i (m.val (Nat.succ n))).1

theorem ilabelN_stable.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : ilabelN.{u, v} m n = IMhead.{u, v} m :=
  ilabel_stable.{u, v} m n

-- ── R2 brick 3: the indexed child (unblocked by the explicit-mode fix) ──


-- position cast across a label equality (ascribed)
def ichildIdxN.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) : I :=
  t i (ilabelN.{u, v} m n) (@icastB.{u, v} I A B t i (ilabelN.{u, v} m n) (IMhead.{u, v} m) (ilabelN_stable.{u, v} m n) b)

def ichildIdx0.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) : I :=
  t i (IMhead.{u, v} m) b

-- the raw child projection at the label-transported position
def ichildRaw.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    iapprox.{u, v} A B t n (ichildIdxN.{u, v} m b n) :=
  (@iasStep.{u, v} I A B t n i (m.val (Nat.succ n))).2
    (@icastB.{u, v} I A B t i (ilabelN.{u, v} m n) (IMhead.{u, v} m) (ilabelN_stable.{u, v} m n) b)

-- the child's level-n approximant: raw projection, index-transported
theorem ichildIdx_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    ichildIdxN.{u, v} m b n = ichildIdx0.{u, v} m b :=
  @it_congr.{u, v} I A B t i (ilabelN.{u, v} m n) (IMhead.{u, v} m) (ilabelN_stable.{u, v} m n) b

def ichildVal.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    iapprox.{u, v} A B t n (ichildIdx0.{u, v} m b) :=
  @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b n) (ichildIdx0.{u, v} m b)
    (ichildIdx_eq.{u, v} m b n) n (ichildRaw.{u, v} m b n)

-- ── R2 brick 3b: coherence machinery for the indexed child ──

-- index-cast composition (Eq.rec on the outer equality; both sides
-- collapse by iota at the diagonal — Eq.trans reduces on its second arg)
theorem icastAppr_comp.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' j'' : I}
    (e1 : j = j') (e2 : j' = j'') (n : Nat) (x : iapprox.{u, v} A B t n j) :
    @icastAppr.{u, v} I A B t j' j'' e2 n (@icastAppr.{u, v} I A B t j j' e1 n x)
      = @icastAppr.{u, v} I A B t j j'' (Eq.trans e1 e2) n x :=
  @Eq.rec I j'
    (fun j3 e3 =>
      @icastAppr.{u, v} I A B t j' j3 e3 n (@icastAppr.{u, v} I A B t j j' e1 n x)
        = @icastAppr.{u, v} I A B t j j3 (Eq.trans e1 e3) n x)
    rfl j'' e2

-- position-cast composition (Eq.rec on the INNER equality so that both
-- icastB rfl and Eq.trans e2 rfl reduce by iota at the diagonal)
theorem icastB_comp.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} {l m : A i} {h : A i}
    (e2 : l = m) (e1 : m = h) (b : B i h) :
    @icastB.{u, v} I A B t i l m e2 (@icastB.{u, v} I A B t i m h e1 b)
      = @icastB.{u, v} I A B t i l h (Eq.trans e2 e1) b :=
  @Eq.rec (A i) m
    (fun h' e1' =>
      ∀ b' : B i h',
        @icastB.{u, v} I A B t i l m e2 (@icastB.{u, v} I A B t i m h' e1' b')
          = @icastB.{u, v} I A B t i l h' (Eq.trans e2 e1') b')
    (fun b' => rfl) h e1 b

-- congruence into the ascribed step coercion
theorem iasStep_congr.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (x y : iapprox.{u, v} A B t (Nat.succ n) i) (e : x = y) :
    @iasStep.{u, v} I A B t n i x = @iasStep.{u, v} I A B t n i y :=
  congrArg (fun z : iapprox.{u, v} A B t (Nat.succ n) i => @iasStep.{u, v} I A B t n i z) e

-- first-projection congruence, hoisted (named const application)
def ifstEq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (p q : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i) (e : p = q) : p.1 = q.1 :=
  congrArg (fun z : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i => z.1) e

-- the indexed second-projection congruence: equal steps have equal
-- children up to the position cast AND the index transport
theorem isigma_snd_congr.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (p q : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i) (e : p = q) :
    ∀ b : B i q.1,
      @icastAppr.{u, v} I A B t
          (t i p.1 (@icastB.{u, v} I A B t i p.1 q.1 (ifstEq.{u, v} p q e) b))
          (t i q.1 b)
          (@it_congr.{u, v} I A B t i p.1 q.1 (ifstEq.{u, v} p q e) b) n
          (p.2 (@icastB.{u, v} I A B t i p.1 q.1 (ifstEq.{u, v} p q e) b))
        = q.2 b :=
  @Eq.rec (isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i) p
    (fun q' e' =>
      ∀ b : B i q'.1,
        @icastAppr.{u, v} I A B t
            (t i p.1 (@icastB.{u, v} I A B t i p.1 q'.1 (ifstEq.{u, v} p q' e') b))
            (t i q'.1 b)
            (@it_congr.{u, v} I A B t i p.1 q'.1 (ifstEq.{u, v} p q' e') b) n
            (p.2 (@icastB.{u, v} I A B t i p.1 q'.1 (ifstEq.{u, v} p q' e') b))
          = q'.2 b)
    (fun b => rfl) q e

-- dependent congruence for a child function: transporting the result
-- across the index equation induced by the argument equation
theorem idcongr.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I} {a : A i}
    (f : (b : B i a) → iapprox.{u, v} A B t n (t i a b)) {x y : B i a} (e : x = y) :
    @icastAppr.{u, v} I A B t (t i a x) (t i a y) (congrArg (t i a) e) n (f x) = f y :=
  @Eq.rec (B i a) x
    (fun y' e' =>
      @icastAppr.{u, v} I A B t (t i a x) (t i a y') (congrArg (t i a) e') n (f x) = f y')
    rfl y e

-- proof-irrelevance banks: casts along different proofs of the same
-- equation are definitionally equal (Eq is a Prop) — minted as named
-- rfl lemmas so later links never lean on unifier-level irrelevance
theorem icastAppr_irrel.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I}
    (e e' : j = j') (n : Nat) (x : iapprox.{u, v} A B t n j) :
    @icastAppr.{u, v} I A B t j j' e n x = @icastAppr.{u, v} I A B t j j' e' n x := rfl

theorem icastB_irrel.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I} {l h : A i}
    (e e' : l = h) (b : B i h) :
    @icastB.{u, v} I A B t i l h e b = @icastB.{u, v} I A B t i l h e' b := rfl

-- ── R2 brick 3c: the child coherence ──

-- hoisted step terms (named const applications keep every later
-- statement inside the elaborator's safe zone)
def ipstep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i :=
  @iasStep.{u, v} I A B t n i
    (@itruncate.{u, v} I A B t (Nat.succ n) i (m.val (Nat.succ (Nat.succ n))))

def iqstep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i :=
  @iasStep.{u, v} I A B t n i (m.val (Nat.succ n))

theorem ipq_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : ipstep.{u, v} m n = iqstep.{u, v} m n :=
  @iasStep_congr.{u, v} I A B t n i
    (@itruncate.{u, v} I A B t (Nat.succ n) i (m.val (Nat.succ (Nat.succ n))))
    (m.val (Nat.succ n))
    (m.property (Nat.succ n))

-- the level-n position, named
def ibpos.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) : B i (ilabelN.{u, v} m n) :=
  @icastB.{u, v} I A B t i (ilabelN.{u, v} m n) (IMhead.{u, v} m) (ilabelN_stable.{u, v} m n) b

-- successive labels agree (the fst-congruence of the tower coherence)
theorem ilabelNN_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (n : Nat) : ilabelN.{u, v} m (Nat.succ n) = ilabelN.{u, v} m n :=
  @ifstEq.{u, v} I A B t n i (ipstep.{u, v} m n) (iqstep.{u, v} m n) (ipq_eq.{u, v} m n)

-- the level-(n+1) position splits as a two-step cast (proof-irrelevance
-- bank + cast composition)
theorem ibpos_split.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    ibpos.{u, v} m b (Nat.succ n)
      = @icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
          (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n) :=
  Eq.trans
    (@icastB_irrel.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (IMhead.{u, v} m)
      (ilabelN_stable.{u, v} m (Nat.succ n))
      (Eq.trans (ilabelNN_eq.{u, v} m n) (ilabelN_stable.{u, v} m n)) b)
    (Eq.symm
      (@icastB_comp.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n) (IMhead.{u, v} m)
        (ilabelNN_eq.{u, v} m n) (ilabelN_stable.{u, v} m n) b))

-- the mid-transport index and the two index equations
def ichildIdxMid.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) : I :=
  t i (ilabelN.{u, v} m (Nat.succ n))
    (@icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
      (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n))

def ichildIdx_split_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    ichildIdxN.{u, v} m b (Nat.succ n) = ichildIdxMid.{u, v} m b n :=
  congrArg (t i (ilabelN.{u, v} m (Nat.succ n))) (ibpos_split.{u, v} m b n)

def ieit.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    ichildIdxMid.{u, v} m b n = ichildIdxN.{u, v} m b n :=
  @it_congr.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
    (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n)

-- the dependent-congruence instance: transporting the p-step child
-- across the position split
theorem ichild_dd.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n)) (ichildIdxMid.{u, v} m b n)
        (ichildIdx_split_eq.{u, v} m b n) n
        ((ipstep.{u, v} m n).2 (ibpos.{u, v} m b (Nat.succ n)))
      = (ipstep.{u, v} m n).2
          (@icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
            (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n)) :=
  @idcongr.{u, v} I A B t n i (ilabelN.{u, v} m (Nat.succ n)) ((ipstep.{u, v} m n).2)
    (ibpos.{u, v} m b (Nat.succ n))
    (@icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
      (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n))
    (ibpos_split.{u, v} m b n)

-- the snd-congruence instance: the transported p-step child IS the
-- level-n raw child
theorem ichild_snd.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    @icastAppr.{u, v} I A B t (ichildIdxMid.{u, v} m b n) (ichildIdxN.{u, v} m b n)
        (ieit.{u, v} m b n) n
        ((ipstep.{u, v} m n).2
          (@icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
            (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n)))
      = ichildRaw.{u, v} m b n :=
  @isigma_snd_congr.{u, v} I A B t n i (ipstep.{u, v} m n) (iqstep.{u, v} m n) (ipq_eq.{u, v} m n)
    (ibpos.{u, v} m b n)

-- the truncation step: itrunc_cast + the definitional collapse of
-- truncating the raw child into the p-step child
theorem ichild_truncstep.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    @itruncate.{u, v} I A B t n (ichildIdx0.{u, v} m b) (ichildVal.{u, v} m b (Nat.succ n))
      = @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n)) (ichildIdx0.{u, v} m b)
          (ichildIdx_eq.{u, v} m b (Nat.succ n)) n
          ((ipstep.{u, v} m n).2 (ibpos.{u, v} m b (Nat.succ n))) :=
  @itrunc_cast.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n)) (ichildIdx0.{u, v} m b)
    (ichildIdx_eq.{u, v} m b (Nat.succ n)) n (ichildRaw.{u, v} m b (Nat.succ n))

-- proof-irrelevance recast: swap the one-step index proof for the
-- composed three-step proof
theorem ichild_recast.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) (n : Nat) :
    @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n)) (ichildIdx0.{u, v} m b)
        (ichildIdx_eq.{u, v} m b (Nat.succ n)) n
        ((ipstep.{u, v} m n).2 (ibpos.{u, v} m b (Nat.succ n)))
      = @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n)) (ichildIdx0.{u, v} m b)
          (Eq.trans (ichildIdx_split_eq.{u, v} m b n)
            (Eq.trans (ieit.{u, v} m b n) (ichildIdx_eq.{u, v} m b n))) n
          ((ipstep.{u, v} m n).2 (ibpos.{u, v} m b (Nat.succ n))) := rfl

-- the child coherence: the transported children form a coherent tower
theorem ichild_coherent.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) :
    ∀ n : Nat,
      @itruncate.{u, v} I A B t n (ichildIdx0.{u, v} m b) (ichildVal.{u, v} m b (Nat.succ n))
        = ichildVal.{u, v} m b n :=
  fun n =>
    Eq.trans (ichild_truncstep.{u, v} m b n)
      (Eq.trans (ichild_recast.{u, v} m b n)
        (Eq.trans
          (Eq.symm
            (@icastAppr_comp.{u, v} I A B t (ichildIdxN.{u, v} m b (Nat.succ n))
              (ichildIdxMid.{u, v} m b n) (ichildIdx0.{u, v} m b)
              (ichildIdx_split_eq.{u, v} m b n)
              (Eq.trans (ieit.{u, v} m b n) (ichildIdx_eq.{u, v} m b n)) n
              ((ipstep.{u, v} m n).2 (ibpos.{u, v} m b (Nat.succ n)))))
          (Eq.trans
            (congrArg
              (fun z : iapprox.{u, v} A B t n (ichildIdxMid.{u, v} m b n) =>
                @icastAppr.{u, v} I A B t (ichildIdxMid.{u, v} m b n) (ichildIdx0.{u, v} m b)
                  (Eq.trans (ieit.{u, v} m b n) (ichildIdx_eq.{u, v} m b n)) n z)
              (ichild_dd.{u, v} m b n))
            (Eq.trans
              (Eq.symm
                (@icastAppr_comp.{u, v} I A B t (ichildIdxMid.{u, v} m b n)
                  (ichildIdxN.{u, v} m b n) (ichildIdx0.{u, v} m b)
                  (ieit.{u, v} m b n) (ichildIdx_eq.{u, v} m b n) n
                  ((ipstep.{u, v} m n).2
                    (@icastB.{u, v} I A B t i (ilabelN.{u, v} m (Nat.succ n)) (ilabelN.{u, v} m n)
                      (ilabelNN_eq.{u, v} m n) (ibpos.{u, v} m b n)))))
              (congrArg
                (fun z : iapprox.{u, v} A B t n (ichildIdxN.{u, v} m b n) =>
                  @icastAppr.{u, v} I A B t (ichildIdxN.{u, v} m b n) (ichildIdx0.{u, v} m b)
                    (ichildIdx_eq.{u, v} m b n) n z)
                (ichild_snd.{u, v} m b n))))))

-- the indexed child as a member of the M-family at the transported index
def IMchild.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) (b : B i (IMhead.{u, v} m)) :
    IMIntl.{u, v} A B t (ichildIdx0.{u, v} m b) :=
  Subtype.mk (IMPred.{u, v} A B t (ichildIdx0.{u, v} m b))
    (fun n => ichildVal.{u, v} m b n)
    (fun n => ichild_coherent.{u, v} m b n)

-- the indexed destructor

-- ascribed mk wrapper for the M-family instance (imkAt lesson: the
-- family instance needs a fully-ascribed per-instance wrapper)
def imkDest.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (a : A i) (f : (b : B i a) → IMIntl.{u, v} A B t (t i a b)) :
    isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i :=
  Sigma.mk a f

def IMdest.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m : IMIntl.{u, v} A B t i) :
    isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i :=
  @imkDest.{u, v} I A B t i (IMhead.{u, v} m) (fun b => IMchild.{u, v} m b)

-- ── R2 brick 4: the indexed constructor ──

def imkApprox.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (x : isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i) :
    (n : Nat) → iapprox.{u, v} A B t n i :=
  Nat.rec (motive := fun n => iapprox.{u, v} A B t n i)
    (@izero.{u, v} I A B t i)
    (fun n _ =>
      @ifromStep.{u, v} I A B t n i
        (@imkAt.{u, v} I A B t n i x.1 (fun b => (x.2 b).val n)))

theorem imk_coherent.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (x : isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i) :
    ∀ n : Nat,
      @itruncate.{u, v} I A B t n i (imkApprox.{u, v} x (Nat.succ n)) = imkApprox.{u, v} x n :=
  Nat.rec
    (motive := fun n =>
      @itruncate.{u, v} I A B t n i (imkApprox.{u, v} x (Nat.succ n)) = imkApprox.{u, v} x n)
    rfl
    (fun n _ =>
      congrArg
        (fun f : (b : B i x.1) → iapprox.{u, v} A B t n (t i x.1 b) =>
          @ifromStep.{u, v} I A B t n i (@imkAt.{u, v} I A B t n i x.1 f))
        (funext (fun b => (x.2 b).property n)))

def IMmk.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (x : isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i) : IMIntl.{u, v} A B t i :=
  Subtype.mk (IMPred.{u, v} A B t i) (imkApprox.{u, v} x) (fun n => imk_coherent.{u, v} x n)

-- ── R2 brick 5: the indexed corecursor ──

def icorecApprox.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) :
    (n : Nat) → (j : I) → S j → iapprox.{u, v} A B t n j :=
  Nat.rec (motive := fun k => (j : I) → S j → iapprox.{u, v} A B t k j)
    (fun j _ => @izero.{u, v} I A B t j)
    (fun n ih => fun j s =>
      @ifromStep.{u, v} I A B t n j
        (@imkAt.{u, v} I A B t n j (g j s).1
          (fun b => ih (t j (g j s).1 b) ((g j s).2 b))))

theorem icorec_coherent.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) :
    ∀ (n : Nat) (j : I) (s : S j),
      @itruncate.{u, v} I A B t n j (icorecApprox.{u, v} g (Nat.succ n) j s)
        = icorecApprox.{u, v} g n j s :=
  Nat.rec
    (motive := fun n =>
      ∀ (j : I) (s : S j),
        @itruncate.{u, v} I A B t n j (icorecApprox.{u, v} g (Nat.succ n) j s)
          = icorecApprox.{u, v} g n j s)
    (fun j s => rfl)
    (fun n ih => fun j s =>
      congrArg
        (fun f : (b : B j (g j s).1) → iapprox.{u, v} A B t n (t j (g j s).1 b) =>
          @ifromStep.{u, v} I A B t n j (@imkAt.{u, v} I A B t n j (g j s).1 f))
        (funext (fun b =>
          ih (t j (g j s).1 b) ((g j s).2 b))))

def IMcorec.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) (j : I) (s : S j) :
    IMIntl.{u, v} A B t j :=
  Subtype.mk (IMPred.{u, v} A B t j)
    (fun n => icorecApprox.{u, v} g n j s)
    (fun n => icorec_coherent.{u, v} g n j s)

-- ── destructor computation laws ──

-- the corecursor's head is the generator's label, definitionally
theorem iIMhead_corec.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) (j : I) (s : S j) :
    IMhead.{u, v} (IMcorec.{u, v} g j s) = (g j s).1 := rfl

-- the constructor's head is the packed label, definitionally
theorem iIMhead_mk.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (x : isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i) :
    IMhead.{u, v} (IMmk.{u, v} x) = x.1 := rfl

-- the full destructor computation law: destructing a corecursion is one
-- generator step followed by corecursion on the children (rfl — kernel
-- proof irrelevance collapses the label cast, as in the unindexed file)
theorem iIMdest_corec.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) (j : I) (s : S j) :
    IMdest.{u, v} (IMcorec.{u, v} g j s)
      = @imkDest.{u, v} I A B t j (g j s).1
          (fun b => IMcorec.{u, v} g (t j (g j s).1 b) ((g j s).2 b)) := rfl

-- ── R3 PUnit.{u+1}-instance layer (the codata command's I := PUnit.{u+1} lane) ──
-- Named state family + j-generic step/corecursor, so command-generated
-- code never places a lambda family in an isigmaStep slot (the
-- IMdest/tfMk wrapper lesson) and never needs unit-eta in the unifier
-- (every helper is generic over the index j).

def uFam.{u, v} (S : Type (max u v)) : PUnit.{v+1} → Type (max u v) := fun _ => S

def umkStep.{u, v} {A : PUnit.{v+1} → Type u} {B : (i : PUnit.{v+1}) → A i → Type u}
    {t : (i : PUnit.{v+1}) → (a : A i) → B i a → PUnit.{v+1}} {S : Type (max u v)}
    (j : PUnit.{v+1}) (a : A j) (f : B j a → S) :
    isigmaStep.{u, v} A B t (uFam.{u, v} S) j :=
  Sigma.mk a f

def ucorec.{u, v} {A : PUnit.{v+1} → Type u} {B : (i : PUnit.{v+1}) → A i → Type u}
    {t : (i : PUnit.{v+1}) → (a : A i) → B i a → PUnit.{v+1}} {S : Type (max u v)}
    (g : (j : PUnit.{v+1}) → S → isigmaStep.{u, v} A B t (uFam.{u, v} S) j) (s : S) :
    IMIntl.{u, v} A B t PUnit.unit :=
  @IMcorec.{u, v} PUnit.{v+1} A B t (uFam.{u, v} S) g PUnit.unit s


-- computation laws for the PUnit.{u+1} lane, all definitional (@-pinned
-- statements: implicit inference through ucorec's uFam trips the
-- occurs check)
theorem uhead_corec.{u, v} {A : PUnit.{v+1} → Type u} {B : (i : PUnit.{v+1}) → A i → Type u}
    {t : (i : PUnit.{v+1}) → (a : A i) → B i a → PUnit.{v+1}} {S : Type (max u v)}
    (g : (j : PUnit.{v+1}) → S → isigmaStep.{u, v} A B t (uFam.{u, v} S) j) (s : S) :
    @IMhead.{u, v} PUnit.{v+1} A B t PUnit.unit (ucorec.{u, v} g s) = (g PUnit.unit s).1 := rfl

theorem udest_corec.{u, v} {A : PUnit.{v+1} → Type u} {B : (i : PUnit.{v+1}) → A i → Type u}
    {t : (i : PUnit.{v+1}) → (a : A i) → B i a → PUnit.{v+1}} {S : Type (max u v)}
    (g : (j : PUnit.{v+1}) → S → isigmaStep.{u, v} A B t (uFam.{u, v} S) j) (s : S) :
    @IMdest.{u, v} PUnit.{v+1} A B t PUnit.unit (ucorec.{u, v} g s)
      = @imkDest.{u, v} PUnit.{v+1} A B t PUnit.unit ((g PUnit.unit s).1)
          (fun b => ucorec.{u, v} g ((g PUnit.unit s).2 b)) := rfl

theorem uchild_corec.{u, v} {A : PUnit.{v+1} → Type u} {B : (i : PUnit.{v+1}) → A i → Type u}
    {t : (i : PUnit.{v+1}) → (a : A i) → B i a → PUnit.{v+1}} {S : Type (max u v)}
    (g : (j : PUnit.{v+1}) → S → isigmaStep.{u, v} A B t (uFam.{u, v} S) j) (s : S)
    (b : B PUnit.unit (@IMhead.{u, v} PUnit.{v+1} A B t PUnit.unit (ucorec.{u, v} g s))) :
    @IMchild.{u, v} PUnit.{v+1} A B t PUnit.unit (ucorec.{u, v} g s) b = ucorec.{u, v} g ((g PUnit.unit s).2 b) := rfl

-- ── R2 capstone A: the source-index answer (QPFTypes failure 3) ──
-- An indexed stream family where the container index IS the source
-- index: the node at index n has one child at index n+1 (design
-- SectionA: `istream : Nat → Type` has `next n tail = n + 1`).

def natA : Nat → Type := fun _ => Nat
def natB : (i : Nat) → natA i → Type := fun _ _ => Unit
def natT : (i : Nat) → (a : natA i) → natB i a → Nat :=
  fun n _ _ => Nat.succ n
def natS : Nat → Type := fun _ => Unit

-- the enumerator coalgebra: at index j, emit label j, child at j+1
def enumMk (j : Nat) : isigmaStep natA natB natT natS j :=
  Sigma.mk j (fun _ => Unit.unit)

def enumG : (j : Nat) → natS j → isigmaStep natA natB natT natS j :=
  fun j _ => enumMk j

def enumFrom (j : Nat) : IMIntl natA natB natT j :=
  IMcorec enumG j Unit.unit

-- computation laws, all definitional
theorem enum_head (j : Nat) : IMhead (enumFrom j) = j := rfl

theorem enum_child_idx (j : Nat) (b : natB j (IMhead (enumFrom j))) :
    ichildIdx0 (enumFrom j) b = Nat.succ j := rfl

theorem enum_dest (j : Nat) :
    IMdest (enumFrom j)
      = @imkDest Nat natA natB natT j j (fun _ => enumFrom (Nat.succ j)) :=
  rfl

-- ── R2 capstone B: the tag-index answer (QPFTypes failure 2, mutual
-- blocks) ── two mutually-coinductive families over the two-point tag
-- index: a Tree (tag true, Nat label, one child = its Forest) and a
-- Forest (tag false, two children: a Tree and a Forest).

def tfA : Bool → Type :=
  fun tg => Bool.rec (motive := fun _ => Type) Unit Nat tg

def tfB : (i : Bool) → tfA i → Type :=
  fun tg _ => Bool.rec (motive := fun _ => Type) Bool Unit tg

def tfT : (i : Bool) → (a : tfA i) → tfB i a → Bool :=
  fun tg =>
    Bool.rec (motive := fun tg' => (a : tfA tg') → tfB tg' a → Bool)
      (fun _ b => b) (fun _ _ => false) tg

def tfS : Bool → Type := fun _ => Nat

-- generic ascribed mk (the imkAt lesson: the family-instance Sigma.mk
-- needs a wrapper whose signature spells the field types syntactically)
def tfMk (tg : Bool) (a : tfA tg)
    (f : (b : tfB tg a) → tfS (tfT tg a b)) :
    isigmaStep tfA tfB tfT tfS tg :=
  Sigma.mk a f

-- per-tag coalgebra steps
def tfMkT (k : Nat) : isigmaStep tfA tfB tfT tfS true :=
  tfMk true k (fun _ => k)

def tfMkF (k : Nat) : isigmaStep tfA tfB tfT tfS false :=
  tfMk false Unit.unit (fun _ => k)

def tfG : (j : Bool) → tfS j → isigmaStep tfA tfB tfT tfS j :=
  fun j =>
    Bool.rec (motive := fun tg => tfS tg → isigmaStep tfA tfB tfT tfS tg)
      (fun k => tfMkF k) (fun k => tfMkT k) j

-- the mutually-coinductive pair, built by ONE corec over the tag index
def constTree (k : Nat) : IMIntl tfA tfB tfT true := IMcorec tfG true k
def constForest (k : Nat) : IMIntl tfA tfB tfT false := IMcorec tfG false k

-- computation laws: the labels, and the MUTUAL links (a Tree's child
-- lives at the Forest tag; a Forest's true-position child at the Tree
-- tag) — all definitional
theorem constTree_head (k : Nat) : IMhead (constTree k) = k := rfl

theorem constTree_child_is_forest (k : Nat)
    (b : tfB true (IMhead (constTree k))) :
    ichildIdx0 (constTree k) b = false := rfl

theorem constForest_child_true_is_tree (k : Nat) :
    ichildIdx0 (constForest k) true = true := rfl

theorem constForest_child_false_is_forest (k : Nat) :
    ichildIdx0 (constForest k) false = false := rfl

-- ── R3+ native ITree over the indexed machinery (container events) ──
-- Events as a CONTAINER signature (E : Type, Ans : E → Type u) — the
-- strictly-positive core of `Type → Type` event functors (the functor
-- surface itself is the U2 lane). Nodes: Ret r | Tau t | Vis e k.

inductive NoPos.{u} : Type u

def itreeShape.{u} (E : Type u) (R : Type u) : Type u := Sum R (Sum PUnit.{u+1} E)

def itreePos.{u} (E : Type u) (R : Type u) (Ans : E → Type u) :
    itreeShape E R → Type u :=
  fun s =>
    @Sum.rec R (Sum PUnit.{u+1} E) (fun _ => Type u)
      (fun _ => NoPos)
      (fun s2 =>
        @Sum.rec PUnit.{u+1} E (fun _ => Type u) (fun _ => PUnit.{u+1}) (fun e => Ans e) s2)
      s

def itreeA.{u, v} (E : Type u) (R : Type u) : PUnit.{v+1} → Type u := fun _ => itreeShape E R

def itreeB.{u, v} (E : Type u) (R : Type u) (Ans : E → Type u) :
    (i : PUnit.{v+1}) → itreeA.{u, v} E R i → Type u :=
  fun _ s => itreePos E R Ans s

def itreeT.{u, v} (E : Type u) (R : Type u) (Ans : E → Type u) :
    (i : PUnit.{v+1}) → (a : itreeA.{u, v} E R i) → itreeB.{u, v} E R Ans i a → PUnit.{v+1} :=
  fun _ _ _ => PUnit.unit

def ITree.{u, v} (E : Type u) (Ans : E → Type u) (R : Type u) : Type (max u v) :=
  @IMIntl.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit

-- generic mk/dest computation law (dest of a packed step is that step)
theorem iIMdest_mk.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (x : isigmaStep.{u, v} A B t (IMIntl.{u, v} A B t) i) :
    IMdest.{u, v} (IMmk.{u, v} x) = x := rfl

-- per-container ascribed mk (the tfMk lesson: the generic imkDest's
-- ascription fights the Sum.rec-unfolded position family; a wrapper
-- whose signature spells the ITree vocabulary syntactically does not)
def itreeMk.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u}
    (a : itreeA.{u, v} E R PUnit.unit)
    (f : (b : itreeB.{u, v} E R Ans PUnit.unit a) →
      IMIntl.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans)
        (itreeT.{u, v} E R Ans PUnit.unit a b)) :
    isigmaStep.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans)
      (IMIntl.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans)) PUnit.unit :=
  Sigma.mk a f

-- the three node constructors
def iRet.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (r : R) :
    ITree.{u, v} E Ans R :=
  @IMmk.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
    (itreeMk.{u, v} (Ans := Ans) (Sum.inl r)
      (fun b => @NoPos.rec (fun _ => ITree.{u, v} E Ans R) b))

def iTau.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (t0 : ITree.{u, v} E Ans R) :
    ITree.{u, v} E Ans R :=
  @IMmk.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
    (itreeMk.{u, v} (Sum.inr (Sum.inl PUnit.unit)) (fun _ => t0))

def iVis.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (e : E)
    (k : Ans e → ITree.{u, v} E Ans R) : ITree.{u, v} E Ans R :=
  @IMmk.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
    (itreeMk.{u, v} (Sum.inr (Sum.inr e)) k)

-- head observations, all definitional
theorem iRet_head.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (r : R) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (iRet.{u, v} (Ans := Ans) r) = Sum.inl r := rfl

theorem iTau_head.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u}
    (t0 : ITree.{u, v} E Ans R) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (iTau.{u, v} t0) = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem iVis_head.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (e : E)
    (k : Ans e → ITree.{u, v} E Ans R) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (iVis.{u, v} e k) = Sum.inr (Sum.inr e) := rfl

-- child observations (dest-of-mk collapses definitionally)
theorem iTau_child.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u}
    (t0 : ITree.{u, v} E Ans R)
    (b : itreePos E R Ans (Sum.inr (Sum.inl PUnit.unit))) :
    @IMchild.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (iTau.{u, v} t0) b = t0 := rfl

theorem iVis_child.{u, v} {E : Type u} {R : Type u} {Ans : E → Type u} (e : E)
    (k : Ans e → ITree.{u, v} E Ans R) (b : Ans e) :
    @IMchild.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (iVis.{u, v} e k) b = k b := rfl

-- the divergent computation: an infinite Tau chain by corecursion
def ispin.{u, v} (E : Type u) (R : Type u) (Ans : E → Type u) : ITree.{u, v} E Ans R :=
  @ucorec.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.{max u v + 1}
    (fun j _ =>
      @umkStep.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.{max u v + 1} j
        (Sum.inr (Sum.inl PUnit.unit)) (fun _ => PUnit.unit))
    PUnit.unit

theorem ispin_head.{u, v} (E : Type u) (R : Type u) (Ans : E → Type u) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (ispin.{u, v} E R Ans) = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem ispin_child.{u, v} (E : Type u) (R : Type u) (Ans : E → Type u)
    (b : itreePos E R Ans (Sum.inr (Sum.inl PUnit.unit))) :
    @IMchild.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans) PUnit.unit
      (ispin.{u, v} E R Ans) b = ispin.{u, v} E R Ans := rfl

-- ── ITree bind: sequencing by Sum-state corecursion ──
-- State: Sum (source tree over R) (continuation tree over S). The
-- coalgebra copies continuation steps verbatim (inr) and translates
-- source steps (inl), entering the continuation when a Ret is reached.

-- the bind state
def ibindSt.{u, v} (E : Type u) (Ans : E → Type u) (R : Type u) (S : Type u) : Type (max u v) :=
  Sum (ITree.{u, v} E Ans R) (ITree.{u, v} E Ans S)

-- copy one step of a continuation tree, children re-tagged inr
def icopyStep.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (j : PUnit.{v+1}) (t0 : ITree.{u, v} E Ans S) :
    isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
      (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j :=
  @Sigma.rec (itreeA.{u, v} E S PUnit.unit)
    (fun a => (b : itreeB.{u, v} E S Ans PUnit.unit a) →
      IMIntl.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
        (itreeT.{u, v} E S Ans PUnit.unit a b))
    (fun _ =>
      isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
        (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j)
    (fun a f =>
      @umkStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
        (ibindSt.{u, v} E Ans R S) j a (fun b => Sum.inr (f b)))
    (@IMdest.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
      PUnit.unit t0)

-- translate one source step: Ret r enters the continuation (emitting
-- its first step), Tau/Vis re-emit with inl-tagged children. The
-- Sum.rec tower abstracts the child function so each branch sees it at
-- the branch's CONCRETE label (positions reduce, no casts).
def itransStep.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (k : R → ITree.{u, v} E Ans S) (j : PUnit.{v+1}) (t0 : ITree.{u, v} E Ans R) :
    isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
      (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j :=
  @Sigma.rec (itreeA.{u, v} E R PUnit.unit)
    (fun a => (b : itreeB.{u, v} E R Ans PUnit.unit a) →
      IMIntl.{u, v} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans)
        (itreeT.{u, v} E R Ans PUnit.unit a b))
    (fun _ =>
      isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
        (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j)
    (fun a =>
      @Sum.rec R (Sum PUnit.{u+1} E)
        (fun a' =>
          ((b : itreePos E R Ans a') → ITree.{u, v} E Ans R) →
          isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
            (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j)
        (fun r => fun _ => @icopyStep.{u, v} E R S Ans j (k r))
        (fun s2 =>
          @Sum.rec PUnit.{u+1} E
            (fun s2' =>
              ((b : itreePos E R Ans (Sum.inr s2')) → ITree.{u, v} E Ans R) →
              isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
                (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j)
            (fun _ => fun f =>
              @umkStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
                (ibindSt.{u, v} E Ans R S) j (Sum.inr (Sum.inl PUnit.unit))
                (fun b => Sum.inl (f b)))
            (fun e => fun f =>
              @umkStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
                (ibindSt.{u, v} E Ans R S) j (Sum.inr (Sum.inr e))
                (fun b => Sum.inl (f b)))
            s2)
        a)
    (@IMdest.{u, v} PUnit.{v+1} (itreeA.{u, v} E R) (itreeB.{u, v} E R Ans) (itreeT.{u, v} E R Ans)
      PUnit.unit t0)

-- the bind coalgebra and bind itself
def ibindG.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (k : R → ITree.{u, v} E Ans S) :
    (j : PUnit.{v+1}) → ibindSt.{u, v} E Ans R S →
      isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
        (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j :=
  fun j st =>
    @Sum.rec (ITree.{u, v} E Ans R) (ITree.{u, v} E Ans S)
      (fun _ =>
        isigmaStep.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
          (uFam.{u, v} (ibindSt.{u, v} E Ans R S)) j)
      (fun tl => @itransStep.{u, v} E R S Ans k j tl)
      (fun tr => @icopyStep.{u, v} E R S Ans j tr)
      st

def ibind.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (t0 : ITree.{u, v} E Ans R) (k : R → ITree.{u, v} E Ans S) : ITree.{u, v} E Ans S :=
  @ucorec.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
    (ibindSt.{u, v} E Ans R S) (ibindG.{u, v} k) (Sum.inl t0)


-- ── bind computation laws ──
-- Heads are raw rfl. Child laws are the uchild_corec instance: the
-- generic law keeps both sides ucorec-headed, so the kernel compares
-- small state terms instead of structurally normalizing the Subtype
-- tower (raw rfl there sends defeq into a blowup — measured).

theorem ibind_ret_head.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (r : R) (k : R → ITree.{u, v} E Ans S) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans) PUnit.unit
      (ibind.{u, v} (iRet.{u, v} (Ans := Ans) r) k)
      = @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
          PUnit.unit (k r) := rfl

theorem ibind_tau_head.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (t0 : ITree.{u, v} E Ans R) (k : R → ITree.{u, v} E Ans S) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans) PUnit.unit
      (ibind.{u, v} (iTau.{u, v} t0) k) = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem ibind_vis_head.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (e : E) (kv : Ans e → ITree.{u, v} E Ans R) (k : R → ITree.{u, v} E Ans S) :
    @IMhead.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans) PUnit.unit
      (ibind.{u, v} (iVis.{u, v} e kv) k) = Sum.inr (Sum.inr e) := rfl

-- generic bind child laws: binding continues through Tau and Vis
-- children (uchild_corec instances; unblocked by the FVarId-allocator
-- fix — the old quadratic scan made these look like a kernel wall)
theorem ibind_tau_child.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (t0 : ITree.{u, v} E Ans R) (k : R → ITree.{u, v} E Ans S)
    (b : itreePos E S Ans (Sum.inr (Sum.inl PUnit.unit))) :
    @IMchild.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans) PUnit.unit
      (ibind.{u, v} (iTau.{u, v} t0) k) b = ibind.{u, v} t0 k :=
  @uchild_corec.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
    (ibindSt.{u, v} E Ans R S) (ibindG.{u, v} k) (Sum.inl (iTau.{u, v} t0)) b

theorem ibind_vis_child.{u, v} {E : Type u} {R : Type u} {S : Type u} {Ans : E → Type u}
    (e : E) (kv : Ans e → ITree.{u, v} E Ans R) (k : R → ITree.{u, v} E Ans S)
    (b : Ans e) :
    @IMchild.{u, v} PUnit.{v+1} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans) PUnit.unit
      (ibind.{u, v} (iVis.{u, v} e kv) k) b = ibind.{u, v} (kv b) k :=
  @uchild_corec.{u, v} (itreeA.{u, v} E S) (itreeB.{u, v} E S Ans) (itreeT.{u, v} E S Ans)
    (ibindSt.{u, v} E Ans R S) (ibindG.{u, v} k) (Sum.inl (iVis.{u, v} e kv)) b


-- a two-step concrete program over a trivial event signature: bind
-- walks THROUGH a Tau into the continuation, and the continuation's
-- answer is observable two observation-steps deep — all by rfl.
def noEv.{u} : Type u := PUnit.{u+1}
def noAns.{u} : noEv → Type u := fun _ => NoPos

-- concrete computation instances: MONOMORPHIC on purpose (R := Nat is
-- Type 0, so these pin u := 0 through fresh level metas)
def prog1 : ITree noEv noAns Nat := iTau (iRet 1)

def kSucc : Nat → ITree noEv noAns Nat :=
  fun n => iRet (Nat.succ n)

theorem bind_step1 :
    @IMhead PUnit (itreeA noEv Nat) (itreeB noEv Nat noAns)
      (itreeT noEv Nat noAns) PUnit.unit (ibind prog1 kSucc)
      = Sum.inr (Sum.inl PUnit.unit) := rfl

theorem bind_step2 :
    @IMhead PUnit (itreeA noEv Nat) (itreeB noEv Nat noAns)
      (itreeT noEv Nat noAns) PUnit.unit
      (@IMchild PUnit (itreeA noEv Nat) (itreeB noEv Nat noAns)
        (itreeT noEv Nat noAns) PUnit.unit (ibind prog1 kSucc) PUnit.unit)
      = Sum.inl 2 := rfl

-- ── R4: bisimilarity IS equality in the tower model ──
-- Rocq/Mathlib reach codata equality through a bisimilarity quotient
-- (Cofix := Quot M bisim). In the approximation-tower model the quotient
-- is DEGENERATE: tower agreement (the model's bisimilarity) already
-- implies equality, so Quot adds nothing. Proven, both directions.

theorem isubtype_ext.{u} {X : Type u} {p : X → Prop} (x y : Subtype p)
    (h : x.val = y.val) : x = y :=
  @Eq.rec X x.val (fun v _ => ∀ hv : p v, x = Subtype.mk p v hv)
    (fun _ => rfl) y.val h y.property

-- tower agreement → equality (M-extensionality)
theorem iM_ext.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m1 m2 : IMIntl.{u, v} A B t i)
    (h : ∀ n : Nat, m1.val n = m2.val n) : m1 = m2 :=
  isubtype_ext m1 m2 (funext h)

-- equality → tower agreement (the converse, trivially)
theorem iM_bisim_of_eq.{u, v} {I : Type v} {A : I → Type u}
    {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {i : I}
    (m1 m2 : IMIntl.{u, v} A B t i) (e : m1 = m2) :
    ∀ n : Nat, m1.val n = m2.val n :=
  fun n => congrArg (fun z : IMIntl.{u, v} A B t i => z.val n) e

-- ── coinduction-principle machinery (the relation-based principle's
-- three pillars; the assembly — Nat.rec over towers with the
-- icastB/icastAppr composition dance through hhead/hchild closure
-- hypotheses — is the next brick, following ichild_coherent's recipe) ──

-- index-cast on M-family members
def icastM.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I}
    (e : j = j') (m : IMIntl.{u, v} A B t j) : IMIntl.{u, v} A B t j' :=
  cast (congrArg (IMIntl.{u, v} A B t) e) m

-- the member cast commutes with the tower (Eq.rec; diagonal rfl)
theorem icastM_val.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j j' : I}
    (e : j = j') (m : IMIntl.{u, v} A B t j) (n : Nat) :
    (icastM.{u, v} e m).val n = @icastAppr.{u, v} I A B t j j' e n (m.val n) :=
  @Eq.rec I j
    (fun j2 e2 =>
      (icastM.{u, v} e2 m).val n = @icastAppr.{u, v} I A B t j j2 e2 n (m.val n))
    rfl j' e

-- converse sigma extensionality: equal labels + transported-equal
-- children give equal steps (Eq.rec on the label equality generalized
-- over the second component, then funext + Sigma eta)
theorem isigma_ext.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {n : Nat} {i : I}
    (p q : isigmaStep.{u, v} A B t (iapprox.{u, v} A B t n) i)
    (e : p.1 = q.1)
    (h : ∀ b : B i q.1,
      @icastAppr.{u, v} I A B t
        (t i p.1 (@icastB.{u, v} I A B t i p.1 q.1 e b)) (t i q.1 b)
        (@it_congr.{u, v} I A B t i p.1 q.1 e b) n
        (p.2 (@icastB.{u, v} I A B t i p.1 q.1 e b))
      = q.2 b) : p = q :=
  @Eq.rec (A i) p.1
    (fun a' e' =>
      ∀ f' : (b : B i a') → iapprox.{u, v} A B t n (t i a' b),
        (∀ b : B i a',
          @icastAppr.{u, v} I A B t
            (t i p.1 (@icastB.{u, v} I A B t i p.1 a' e' b)) (t i a' b)
            (@it_congr.{u, v} I A B t i p.1 a' e' b) n
            (p.2 (@icastB.{u, v} I A B t i p.1 a' e' b))
          = f' b) →
        p = @imkAt.{u, v} I A B t n i a' f')
    (fun f' hf =>
      congrArg (fun f : (b : B i p.1) → iapprox.{u, v} A B t n (t i p.1 b) =>
        @imkAt.{u, v} I A B t n i p.1 f)
        (funext hf))
    q.1 e q.2 h

-- ── the relation-based coinduction principle: assembly ──

-- any two Units are equal (eta) — the towers' base case, hoisted so
-- the appeal runs through argument-position defeq, not raw unification
theorem iunit_eq.{u} (x y : PUnit.{u+1}) : x = y := rfl

-- level-zero tower agreement for ANY two members at the same index
theorem ival_zero_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) : m1.val Nat.zero = m2.val Nat.zero :=
  iunit_eq (m1.val Nat.zero) (m2.val Nat.zero)

-- hoisted step data: the label-n equality and the two positions
def icoind_b2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m2 : IMIntl.{u, v} A B t j) (n : Nat) (b : B j (ilabelN.{u, v} m2 n)) :
    B j (IMhead.{u, v} m2) :=
  @icastB.{u, v} I A B t j (IMhead.{u, v} m2) (ilabelN.{u, v} m2 n)
    (Eq.symm (ilabelN_stable.{u, v} m2 n)) b

def icoind_b1.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) : B j (IMhead.{u, v} m1) :=
  @icastB.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)

def icoind_elab.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat) :
    ilabelN.{u, v} m1 n = ilabelN.{u, v} m2 n :=
  Eq.trans (ilabelN_stable.{u, v} m1 n)
    (Eq.trans hh (Eq.symm (ilabelN_stable.{u, v} m2 n)))

-- position collapse on the m2 side: casting down to the head and back
-- up to level n is the identity (composition + irrelevance-to-rfl)
theorem icoind_pos2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m2 : IMIntl.{u, v} A B t j) (n : Nat) (b : B j (ilabelN.{u, v} m2 n)) :
    ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n = b :=
  Eq.trans
    (@icastB_comp.{u, v} I A B t j (ilabelN.{u, v} m2 n) (IMhead.{u, v} m2) (ilabelN.{u, v} m2 n)
      (ilabelN_stable.{u, v} m2 n) (Eq.symm (ilabelN_stable.{u, v} m2 n)) b)
    (@icastB_irrel.{u, v} I A B t j (ilabelN.{u, v} m2 n) (ilabelN.{u, v} m2 n)
      (Eq.trans (ilabelN_stable.{u, v} m2 n) (Eq.symm (ilabelN_stable.{u, v} m2 n)))
      rfl b)

-- position collapse on the m1 side: the triple cast is the single
-- label-n cast (two compositions; the composite proof IS icoind_elab)
theorem icoind_pos1.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n
      = @icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
          (icoind_elab.{u, v} m1 m2 hh n) b :=
  Eq.trans
    (congrArg
      (fun z : B j (IMhead.{u, v} m1) =>
        @icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (IMhead.{u, v} m1)
          (ilabelN_stable.{u, v} m1 n) z)
      (@icastB_comp.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) (ilabelN.{u, v} m2 n)
        hh (Eq.symm (ilabelN_stable.{u, v} m2 n)) b))
    (@icastB_comp.{u, v} I A B t j (ilabelN.{u, v} m1 n) (IMhead.{u, v} m1) (ilabelN.{u, v} m2 n)
      (ilabelN_stable.{u, v} m1 n)
      (Eq.trans hh (Eq.symm (ilabelN_stable.{u, v} m2 n))) b)

-- dependent-congr instances: moving each side's step child from the
-- head-position spelling to the level-n position spelling
theorem icoind_q2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m2 : IMIntl.{u, v} A B t j) (n : Nat) (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t
        (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))
        (t j (ilabelN.{u, v} m2 n) b)
        (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)) n
        ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))
      = (iqstep.{u, v} m2 n).2 b :=
  @idcongr.{u, v} I A B t n j (ilabelN.{u, v} m2 n) ((iqstep.{u, v} m2 n).2)
    (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) b (icoind_pos2.{u, v} m2 n b)

theorem icoind_p1.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t
        (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
        (t j (ilabelN.{u, v} m1 n)
          (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
            (icoind_elab.{u, v} m1 m2 hh n) b))
        (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) n
        ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
      = (iqstep.{u, v} m1 n).2
          (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
            (icoind_elab.{u, v} m1 m2 hh n) b) :=
  @idcongr.{u, v} I A B t n j (ilabelN.{u, v} m1 n) ((iqstep.{u, v} m1 n).2)
    (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)
    (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
      (icoind_elab.{u, v} m1 m2 hh n) b)
    (icoind_pos1.{u, v} m1 m2 hh n b)

-- the IH bridge: the transported-children agreement, re-spelled onto
-- the raw step children (icastM_val + the definitional IMchild towers)
theorem icoind_ih_eq.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n))
    (ihv : (icastM.{u, v}
        (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh
          (icoind_b2.{u, v} m2 n b))
        (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b))).val n
      = (IMchild.{u, v} m2 (icoind_b2.{u, v} m2 n b)).val n) :
    @icastAppr.{u, v} I A B t
        (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b))
        (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b))
        (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh
          (icoind_b2.{u, v} m2 n b)) n
        (@icastAppr.{u, v} I A B t
          (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
          (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b))
          (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) n
          ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)))
      = @icastAppr.{u, v} I A B t
          (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))
          (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b))
          (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) n
          ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) :=
  Eq.trans
    (Eq.symm
      (icastM_val.{u, v}
        (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh
          (icoind_b2.{u, v} m2 n b))
        (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b)) n))
    ihv


-- icoind_s1: rewrite the goal's child through icoind_p1
theorem icoind_s1.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n ((iqstep.{u, v} m1 n).2 (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n
          (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))) :=
  congrArg
    (fun z : iapprox.{u, v} A B t n (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) =>
      @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n z)
    (Eq.symm (icoind_p1.{u, v} m1 m2 hh n b))

-- icoind_s2: compose the stacked casts
theorem icoind_s2.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n
        (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) :=
  @icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))

-- icoind_s3: proof-irrelevance swap to the BIG composite
theorem icoind_s3.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) :=
  @icastAppr_irrel.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (Eq.trans (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))

-- icoind_s4: unstack BIG
theorem icoind_s4.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
      = @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n
          (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))) :=
  Eq.symm
    (@icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b)
      (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)))

-- icoind_s5a: just the unstack
theorem icoind_s5a.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
      = @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) n
          (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))) :=
  Eq.symm (@icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)))

-- icoind_s5b: just the IH application at the unstacked spelling
theorem icoind_s5b.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n))
    (ihv : (icastM.{u, v} (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b))).val n
      = (IMchild.{u, v} m2 (icoind_b2.{u, v} m2 n b)).val n) :
    @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) n
        (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) :=
  Eq.trans
    (Eq.symm
      (icastM_val.{u, v}
        (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))
        (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b)) n))
    ihv

-- icoind_s6: fold the right side
theorem icoind_s6.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n
        (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (ilabelN.{u, v} m2 n) b)
          (Eq.trans (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) :=
  @icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b) (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)
    (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))

-- icoind_s7: proof-irrelevance back to E3
theorem icoind_s7.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (ilabelN.{u, v} m2 n) b)
        (Eq.trans (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (ilabelN.{u, v} m2 n) b) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) :=
  @icastAppr_irrel.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (ilabelN.{u, v} m2 n) b)
    (Eq.trans (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)))) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n))

-- icoind_s8: land on the goal's right side
theorem icoind_s8.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (ilabelN.{u, v} m2 n) b) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b)) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) = (iqstep.{u, v} m2 n).2 b :=
  icoind_q2.{u, v} m2 n b

-- partial chain: s1 ∘ s2
theorem snd12.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) (t j (ilabelN.{u, v} m2 n) b) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b) n ((iqstep.{u, v} m1 n).2 (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b))
      = @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) :=
  Eq.trans (icoind_s1.{u, v} m1 m2 hh n b) (icoind_s2.{u, v} m1 m2 hh n b)

-- partial chain: s3 ∘ s4
theorem snd34.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (congrArg (t j (ilabelN.{u, v} m1 n)) (icoind_pos1.{u, v} m1 m2 hh n b)) (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n) (icoind_elab.{u, v} m1 m2 hh n) b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))
      = @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n
          (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (Eq.trans (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b))) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))) :=
  Eq.trans (icoind_s3.{u, v} m1 m2 hh n b) (icoind_s4.{u, v} m1 m2 hh n b)

-- partial chain: s6 ∘ s7 ∘ s8
theorem snd678.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n)) :
    @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b) (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n
        (@icastAppr.{u, v} I A B t (t j (ilabelN.{u, v} m2 n) (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n) n ((iqstep.{u, v} m2 n).2 (ibpos.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)))
      = (iqstep.{u, v} m2 n).2 b :=
  Eq.trans (icoind_s6.{u, v} m1 m2 hh n b)
    (Eq.trans (icoind_s7.{u, v} m1 m2 hh n b) (icoind_s8.{u, v} m1 m2 hh n b))

-- the capstone: partial chains + the s5 seam INLINE in one elaboration
theorem icoind_snd.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {j : I}
    (m1 m2 : IMIntl.{u, v} A B t j) (hh : IMhead.{u, v} m1 = IMhead.{u, v} m2) (n : Nat)
    (b : B j (ilabelN.{u, v} m2 n))
    (ihv : (icastM.{u, v} (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b))).val n
      = (IMchild.{u, v} m2 (icoind_b2.{u, v} m2 n b)).val n) :
    @icastAppr.{u, v} I A B t
        (t j (ilabelN.{u, v} m1 n)
          (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
            (icoind_elab.{u, v} m1 m2 hh n) b))
        (t j (ilabelN.{u, v} m2 n) b)
        (@it_congr.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
          (icoind_elab.{u, v} m1 m2 hh n) b) n
        ((iqstep.{u, v} m1 n).2
          (@icastB.{u, v} I A B t j (ilabelN.{u, v} m1 n) (ilabelN.{u, v} m2 n)
            (icoind_elab.{u, v} m1 m2 hh n) b))
      = (iqstep.{u, v} m2 n).2 b :=
  Eq.trans (snd12.{u, v} m1 m2 hh n b)
    (Eq.trans (snd34.{u, v} m1 m2 hh n b)
      (Eq.trans
        (congrArg
          (fun z : iapprox.{u, v} A B t n (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) =>
            @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b)
              (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n z)
          (Eq.trans
            (Eq.symm
              (@icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n)) (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 hh n b)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh (icoind_b2.{u, v} m2 n b)) n
                ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b) n))))
            (Eq.trans
              (Eq.symm
                (icastM_val.{u, v}
                  (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) hh
                    (icoind_b2.{u, v} m2 n b))
                  (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 hh n b)) n))
              ihv)))
        (snd678.{u, v} m1 m2 hh n b)))

-- the per-level agreement, by Nat-induction over the towers
theorem iM_coind_val.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I}
    (R : (j : I) → IMIntl.{u, v} A B t j → IMIntl.{u, v} A B t j → Prop)
    (hhead : ∀ (j : I) (m1 m2 : IMIntl.{u, v} A B t j), R j m1 m2 →
      @IMhead.{u, v} I A B t j m1 = @IMhead.{u, v} I A B t j m2)
    (hchild : ∀ (j : I) (m1 m2 : IMIntl.{u, v} A B t j) (r : R j m1 m2)
      (b' : B j (@IMhead.{u, v} I A B t j m2)),
      R (t j (@IMhead.{u, v} I A B t j m2) b')
        (icastM.{u, v} (@it_congr.{u, v} I A B t j
            (@IMhead.{u, v} I A B t j m1) (@IMhead.{u, v} I A B t j m2)
            (hhead j m1 m2 r) b')
          (IMchild.{u, v} m1 (@icastB.{u, v} I A B t j
            (@IMhead.{u, v} I A B t j m1) (@IMhead.{u, v} I A B t j m2)
            (hhead j m1 m2 r) b')))
        (IMchild.{u, v} m2 b')) :
    ∀ (n : Nat) (j : I) (m1 m2 : IMIntl.{u, v} A B t j),
      R j m1 m2 → m1.val n = m2.val n :=
  Nat.rec
    (motive := fun n =>
      ∀ (j : I) (m1 m2 : IMIntl.{u, v} A B t j),
        R j m1 m2 → m1.val n = m2.val n)
    (fun j m1 m2 _ => ival_zero_eq.{u, v} m1 m2)
    (fun n ih => fun j m1 m2 r =>
      @isigma_ext.{u, v} I A B t n j (iqstep.{u, v} m1 n) (iqstep.{u, v} m2 n)
        (icoind_elab.{u, v} m1 m2 (hhead j m1 m2 r) n)
        (fun b =>
          Eq.trans (snd12.{u, v} m1 m2 (hhead j m1 m2 r) n b)
            (Eq.trans (snd34.{u, v} m1 m2 (hhead j m1 m2 r) n b)
              (Eq.trans
                (congrArg
                  (fun z : iapprox.{u, v} A B t n (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) =>
                    @icastAppr.{u, v} I A B t (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b)) (t j (ilabelN.{u, v} m2 n) b)
                      (Eq.trans (Eq.symm (ichildIdx_eq.{u, v} m2 (icoind_b2.{u, v} m2 n b) n)) (congrArg (t j (ilabelN.{u, v} m2 n)) (icoind_pos2.{u, v} m2 n b))) n z)
                  (Eq.trans
                    (Eq.symm
                      (@icastAppr_comp.{u, v} I A B t (t j (ilabelN.{u, v} m1 n) (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b) n)) (t j (IMhead.{u, v} m1) (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b)) (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b))
                        (ichildIdx_eq.{u, v} m1 (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b) n) (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) (hhead j m1 m2 r) (icoind_b2.{u, v} m2 n b)) n ((iqstep.{u, v} m1 n).2 (ibpos.{u, v} m1 (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b) n))))
                    (Eq.trans
                      (Eq.symm
                        (icastM_val.{u, v} (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) (hhead j m1 m2 r) (icoind_b2.{u, v} m2 n b))
                          (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b)) n))
                      (ih (t j (IMhead.{u, v} m2) (icoind_b2.{u, v} m2 n b))
                    (icastM.{u, v} (@it_congr.{u, v} I A B t j (IMhead.{u, v} m1) (IMhead.{u, v} m2) (hhead j m1 m2 r) (icoind_b2.{u, v} m2 n b))
                      (IMchild.{u, v} m1 (icoind_b1.{u, v} m1 m2 (hhead j m1 m2 r) n b)))
                    (IMchild.{u, v} m2 (icoind_b2.{u, v} m2 n b))
                    (hchild j m1 m2 r (icoind_b2.{u, v} m2 n b))))))
                (snd678.{u, v} m1 m2 (hhead j m1 m2 r) n b)))))

-- THE COINDUCTION PRINCIPLE: a head-preserving relation closed under
-- transported children implies equality. (Uses the stored iM_coind_val
-- directly — the reapplication failure that once forced inlining was
-- the eta-expanded Miller-solution bug, fixed in clean-elab.)
theorem iM_coind.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I}
    (R : (j : I) → IMIntl.{u, v} A B t j → IMIntl.{u, v} A B t j → Prop)
    (hhead : ∀ (j : I) (m1 m2 : IMIntl.{u, v} A B t j), R j m1 m2 →
      @IMhead.{u, v} I A B t j m1 = @IMhead.{u, v} I A B t j m2)
    (hchild : ∀ (j : I) (m1 m2 : IMIntl.{u, v} A B t j) (r : R j m1 m2)
      (b' : B j (@IMhead.{u, v} I A B t j m2)),
      R (t j (@IMhead.{u, v} I A B t j m2) b')
        (icastM.{u, v} (@it_congr.{u, v} I A B t j
            (@IMhead.{u, v} I A B t j m1) (@IMhead.{u, v} I A B t j m2)
            (hhead j m1 m2 r) b')
          (IMchild.{u, v} m1 (@icastB.{u, v} I A B t j
            (@IMhead.{u, v} I A B t j m1) (@IMhead.{u, v} I A B t j m2)
            (hhead j m1 m2 r) b')))
        (IMchild.{u, v} m2 b'))
    (j0 : I) (mA mB : IMIntl.{u, v} A B t j0) (r0 : R j0 mA mB) : mA = mB :=
  iM_ext.{u, v} mA mB (fun n0 => iM_coind_val.{u, v} R hhead hchild n0 j0 mA mB r0)


-- ── generic-index corecursor observation laws (the PUnit.{u+1}-lane laws'
-- full generalization; needed by the mutual-codata surface) ──
theorem ghead_corec.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) (j : I) (s : S j) :
    @IMhead.{u, v} I A B t j (IMcorec.{u, v} g j s) = (g j s).1 := rfl

theorem gchild_corec.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u}
    {t : (i : I) → (a : A i) → B i a → I} {S : I → Type (max u v)}
    (g : (j : I) → S j → isigmaStep.{u, v} A B t S j) (j : I) (s : S j)
    (b : B j (@IMhead.{u, v} I A B t j (IMcorec.{u, v} g j s))) :
    @IMchild.{u, v} I A B t j (IMcorec.{u, v} g j s) b
      = IMcorec.{u, v} g (t j ((g j s).1) b) ((g j s).2 b) := rfl

-- ═══ hand expansion for:
--   mutual
--     codata TreeS (A : Type) where
--       label : A
--       kids : ForestS A
--     codata ForestS (A : Type) where
--       first : TreeS A
--       rest : ForestS A
--   end
-- tag true = TreeS, false = ForestS (I := Bool)

def TF.shapeF (A : Type) : Bool → Type :=
  fun tg => Bool.rec (motive := fun _ => Type) Unit A tg

def TF.posF (A : Type) : (i : Bool) → TF.shapeF A i → Type :=
  fun tg =>
    Bool.rec (motive := fun tg' => TF.shapeF A tg' → Type)
      (fun _ => Sum Unit Unit) (fun _ => Unit) tg

def TF.tgtF (A : Type) :
    (i : Bool) → (a : TF.shapeF A i) → TF.posF A i a → Bool :=
  fun tg =>
    Bool.rec (motive := fun tg' => (a : TF.shapeF A tg') → TF.posF A tg' a → Bool)
      (fun _ b => @Sum.rec Unit Unit (fun _ => Bool) (fun _ => true) (fun _ => false) b)
      (fun _ _ => false)
      tg

def TreeS (A : Type) : Type :=
  @IMIntl Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) true

def ForestS (A : Type) : Type :=
  @IMIntl Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) false

def TreeS.label {A : Type} (x : TreeS A) : A :=
  @IMhead Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) true x

def TreeS.kids {A : Type} (x : TreeS A) : ForestS A :=
  @IMchild Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) true x Unit.unit

def ForestS.first {A : Type} (x : ForestS A) : TreeS A :=
  @IMchild Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) false x (Sum.inl Unit.unit)

def ForestS.rest {A : Type} (x : ForestS A) : ForestS A :=
  @IMchild Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) false x (Sum.inr Unit.unit)

-- the per-block state family and step wrapper
def TF.stF (S1 : Type) (S2 : Type) : Bool → Type :=
  fun tg => Bool.rec (motive := fun _ => Type) S2 S1 tg

def TF.mkStep {A : Type} {S1 : Type} {S2 : Type} (tg : Bool)
    (a : TF.shapeF A tg)
    (f : (b : TF.posF A tg a) → TF.stF S1 S2 (TF.tgtF A tg a b)) :
    isigmaStep (TF.shapeF A) (TF.posF A) (TF.tgtF A) (TF.stF S1 S2) tg :=
  Sigma.mk a f

-- the mutual coalgebra from the four per-field functions
def TF.step {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) :
    (j : Bool) → TF.stF S1 S2 j →
      isigmaStep (TF.shapeF A) (TF.posF A) (TF.tgtF A) (TF.stF S1 S2) j :=
  fun j =>
    Bool.rec
      (motive := fun tg => TF.stF S1 S2 tg →
        isigmaStep (TF.shapeF A) (TF.posF A) (TF.tgtF A) (TF.stF S1 S2) tg)
      (fun s2 =>
        @TF.mkStep A S1 S2 false Unit.unit
          (fun b =>
            @Sum.rec Unit Unit
              (fun b' => TF.stF S1 S2 (TF.tgtF A false Unit.unit b'))
              (fun _ => firstF s2) (fun _ => restF s2) b))
      (fun s1 => @TF.mkStep A S1 S2 true (labelF s1) (fun _ => kidsF s1))
      j

def TreeS.corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S1) : TreeS A :=
  @IMcorec Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) (TF.stF S1 S2)
    (@TF.step A S1 S2 labelF kidsF firstF restF) true s

def ForestS.corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S2) : ForestS A :=
  @IMcorec Bool (TF.shapeF A) (TF.posF A) (TF.tgtF A) (TF.stF S1 S2)
    (@TF.step A S1 S2 labelF kidsF firstF restF) false s

-- per-field computation laws, all definitional — the MUTUAL links live
theorem TreeS.label_corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S1) :
    TreeS.label (TreeS.corec labelF kidsF firstF restF s) = labelF s := rfl

theorem TreeS.kids_corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S1) :
    TreeS.kids (TreeS.corec labelF kidsF firstF restF s)
      = ForestS.corec labelF kidsF firstF restF (kidsF s) := rfl

theorem ForestS.first_corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S2) :
    ForestS.first (ForestS.corec labelF kidsF firstF restF s)
      = TreeS.corec labelF kidsF firstF restF (firstF s) := rfl

theorem ForestS.rest_corec {A : Type} {S1 : Type} {S2 : Type}
    (labelF : S1 → A) (kidsF : S1 → S2)
    (firstF : S2 → S1) (restF : S2 → S2) (s : S2) :
    ForestS.rest (ForestS.corec labelF kidsF firstF restF s)
      = ForestS.corec labelF kidsF firstF restF (restF s) := rfl

-- concrete computation through the mutual knot
def natTree (n : Nat) : TreeS Nat :=
  TreeS.corec (fun k => k) (fun k => Nat.succ k) (fun k => k) Nat.succ n

theorem nt0 : TreeS.label (natTree 0) = 0 := rfl
theorem nt1 : TreeS.label (ForestS.first (TreeS.kids (natTree 0))) = 1 := rfl
theorem nt2 : TreeS.label (ForestS.first (ForestS.rest (TreeS.kids (natTree 0)))) = 2 := rfl

-- ═══ hand expansion for the INDEXED codata surface:
--   codata IStream : (n : Nat) → Type where
--     val : Nat
--     next : IStream (Nat.succ n)
-- (source-index answer at the surface; index moves per recursive field)

def IStream.shapeF : Nat → Type := fun _ => Nat
def IStream.posF : (i : Nat) → IStream.shapeF i → Type := fun _ _ => Unit
def IStream.tgtF : (i : Nat) → (a : IStream.shapeF i) → IStream.posF i a → Nat :=
  fun n _ _ => Nat.succ n

def IStream (n : Nat) : Type :=
  @IMIntl Nat IStream.shapeF IStream.posF IStream.tgtF n

def IStream.val {n : Nat} (x : IStream n) : Nat :=
  @IMhead Nat IStream.shapeF IStream.posF IStream.tgtF n x

def IStream.next {n : Nat} (x : IStream n) : IStream (Nat.succ n) :=
  @IMchild Nat IStream.shapeF IStream.posF IStream.tgtF n x Unit.unit

def IStream.mkStep {S : Nat → Type} (n : Nat) (a : IStream.shapeF n)
    (f : (b : IStream.posF n a) → S (IStream.tgtF n a b)) :
    isigmaStep IStream.shapeF IStream.posF IStream.tgtF S n :=
  Sigma.mk a f

def IStream.stepFn {S : Nat → Type}
    (valF : (n : Nat) → S n → Nat)
    (nextF : (n : Nat) → S n → S (Nat.succ n)) :
    (j : Nat) → S j →
      isigmaStep IStream.shapeF IStream.posF IStream.tgtF S j :=
  fun j sv => @IStream.mkStep S j (valF j sv) (fun _ => nextF j sv)

def IStream.corec {S : Nat → Type}
    (valF : (n : Nat) → S n → Nat)
    (nextF : (n : Nat) → S n → S (Nat.succ n))
    (n : Nat) (s : S n) : IStream n :=
  @IMcorec Nat IStream.shapeF IStream.posF IStream.tgtF S
    (@IStream.stepFn S valF nextF) n s

theorem IStream.val_corec {S : Nat → Type}
    (valF : (n : Nat) → S n → Nat)
    (nextF : (n : Nat) → S n → S (Nat.succ n))
    (n : Nat) (s : S n) :
    IStream.val (IStream.corec valF nextF n s) = valF n s := rfl

theorem IStream.next_corec {S : Nat → Type}
    (valF : (n : Nat) → S n → Nat)
    (nextF : (n : Nat) → S n → S (Nat.succ n))
    (n : Nat) (s : S n) :
    IStream.next (IStream.corec valF nextF n s)
      = IStream.corec valF nextF (Nat.succ n) (nextF n s) := rfl

-- concrete: the index-tracking stream (state = the index itself)
def idxStream (n : Nat) : IStream n :=
  IStream.corec (S := fun k => Unit) (fun k _ => k) (fun _ _ => Unit.unit)
    n Unit.unit

theorem ix0 : IStream.val (idxStream 5) = 5 := rfl
theorem ix1 : IStream.val (IStream.next (idxStream 5)) = 6 := rfl
theorem ix2 : IStream.val (IStream.next (IStream.next (idxStream 5))) = 7 := rfl

-- ═══ hand expansion for a THREE-member mutual block over Sum-of-Units
-- tags (the Σ-tag generalization; tag0 = inl (), tag1 = inr (inl ()),
-- tag2 = inr (inr ())):
--   mutual
--     codata R1 where a : Nat; nx : R2
--     codata R2 where b : Nat; nx : R3
--     codata R3 where c : Nat; nx : R1
--   end

def T3 : Type := Sum Unit (Sum Unit Unit)
def t0 : T3 := Sum.inl Unit.unit
def t1 : T3 := Sum.inr (Sum.inl Unit.unit)
def t2 : T3 := Sum.inr (Sum.inr Unit.unit)

def R.shapeF : T3 → Type :=
  fun tg =>
    @Sum.rec Unit (Sum Unit Unit) (fun _ => Type)
      (fun _ => Nat)
      (fun s2 =>
        @Sum.rec Unit Unit (fun _ => Type) (fun _ => Nat) (fun _ => Nat) s2)
      tg

def R.posF : (i : T3) → R.shapeF i → Type :=
  fun tg =>
    @Sum.rec Unit (Sum Unit Unit)
      (fun tg' => R.shapeF tg' → Type)
      (fun _ => fun _ => Unit)
      (fun s2 =>
        @Sum.rec Unit Unit
          (fun s2' => R.shapeF (Sum.inr s2') → Type)
          (fun _ => fun _ => Unit)
          (fun _ => fun _ => Unit)
          s2)
      tg

def R.tgtF : (i : T3) → (a : R.shapeF i) → R.posF i a → T3 :=
  fun tg =>
    @Sum.rec Unit (Sum Unit Unit)
      (fun tg' => (a : R.shapeF tg') → R.posF tg' a → T3)
      (fun _ => fun _ _ => t1)
      (fun s2 =>
        @Sum.rec Unit Unit
          (fun s2' => (a : R.shapeF (Sum.inr s2')) → R.posF (Sum.inr s2') a → T3)
          (fun _ => fun _ _ => t2)
          (fun _ => fun _ _ => t0)
          s2)
      tg

def R1 : Type := @IMIntl T3 R.shapeF R.posF R.tgtF t0
def R2 : Type := @IMIntl T3 R.shapeF R.posF R.tgtF t1
def R3 : Type := @IMIntl T3 R.shapeF R.posF R.tgtF t2

def R1.a (x : R1) : Nat := @IMhead T3 R.shapeF R.posF R.tgtF t0 x
def R2.b (x : R2) : Nat := @IMhead T3 R.shapeF R.posF R.tgtF t1 x
def R3.c (x : R3) : Nat := @IMhead T3 R.shapeF R.posF R.tgtF t2 x

def R1.nx (x : R1) : R2 := @IMchild T3 R.shapeF R.posF R.tgtF t0 x Unit.unit
def R2.nx (x : R2) : R3 := @IMchild T3 R.shapeF R.posF R.tgtF t1 x Unit.unit
def R3.nx (x : R3) : R1 := @IMchild T3 R.shapeF R.posF R.tgtF t2 x Unit.unit

def R.stF (S1 : Type) (S2 : Type) (S3 : Type) : T3 → Type :=
  fun tg =>
    @Sum.rec Unit (Sum Unit Unit) (fun _ => Type)
      (fun _ => S1)
      (fun s2 =>
        @Sum.rec Unit Unit (fun _ => Type) (fun _ => S2) (fun _ => S3) s2)
      tg

def R.mkStep {S1 : Type} {S2 : Type} {S3 : Type} (tg : T3)
    (a : R.shapeF tg)
    (f : (b : R.posF tg a) → R.stF S1 S2 S3 (R.tgtF tg a b)) :
    isigmaStep R.shapeF R.posF R.tgtF (R.stF S1 S2 S3) tg :=
  Sigma.mk a f

def R.step {S1 : Type} {S2 : Type} {S3 : Type}
    (aF : S1 → Nat) (nx1F : S1 → S2)
    (bF : S2 → Nat) (nx2F : S2 → S3)
    (cF : S3 → Nat) (nx3F : S3 → S1) :
    (j : T3) → R.stF S1 S2 S3 j →
      isigmaStep R.shapeF R.posF R.tgtF (R.stF S1 S2 S3) j :=
  fun j =>
    @Sum.rec Unit (Sum Unit Unit)
      (fun tg' => R.stF S1 S2 S3 tg' →
        isigmaStep R.shapeF R.posF R.tgtF (R.stF S1 S2 S3) tg')
      (fun _ => fun sv =>
        @R.mkStep S1 S2 S3 t0 (aF sv) (fun _ => nx1F sv))
      (fun s2 =>
        @Sum.rec Unit Unit
          (fun s2' => R.stF S1 S2 S3 (Sum.inr s2') →
            isigmaStep R.shapeF R.posF R.tgtF (R.stF S1 S2 S3) (Sum.inr s2'))
          (fun _ => fun sv =>
            @R.mkStep S1 S2 S3 t1 (bF sv) (fun _ => nx2F sv))
          (fun _ => fun sv =>
            @R.mkStep S1 S2 S3 t2 (cF sv) (fun _ => nx3F sv))
          s2)
      j

def R1.corec {S1 : Type} {S2 : Type} {S3 : Type}
    (aF : S1 → Nat) (nx1F : S1 → S2)
    (bF : S2 → Nat) (nx2F : S2 → S3)
    (cF : S3 → Nat) (nx3F : S3 → S1) (s : S1) : R1 :=
  @IMcorec T3 R.shapeF R.posF R.tgtF (R.stF S1 S2 S3)
    (@R.step S1 S2 S3 aF nx1F bF nx2F cF nx3F) t0 s

def R2.corec {S1 : Type} {S2 : Type} {S3 : Type}
    (aF : S1 → Nat) (nx1F : S1 → S2)
    (bF : S2 → Nat) (nx2F : S2 → S3)
    (cF : S3 → Nat) (nx3F : S3 → S1) (s : S2) : R2 :=
  @IMcorec T3 R.shapeF R.posF R.tgtF (R.stF S1 S2 S3)
    (@R.step S1 S2 S3 aF nx1F bF nx2F cF nx3F) t1 s

theorem R1.a_corec {S1 : Type} {S2 : Type} {S3 : Type}
    (aF : S1 → Nat) (nx1F : S1 → S2)
    (bF : S2 → Nat) (nx2F : S2 → S3)
    (cF : S3 → Nat) (nx3F : S3 → S1) (s : S1) :
    R1.a (R1.corec aF nx1F bF nx2F cF nx3F s) = aF s := rfl

theorem R1.nx_corec {S1 : Type} {S2 : Type} {S3 : Type}
    (aF : S1 → Nat) (nx1F : S1 → S2)
    (bF : S2 → Nat) (nx2F : S2 → S3)
    (cF : S3 → Nat) (nx3F : S3 → S1) (s : S1) :
    R1.nx (R1.corec aF nx1F bF nx2F cF nx3F s)
      = R2.corec aF nx1F bF nx2F cF nx3F (nx1F s) := rfl

-- the three-member ring computes: t0 → t1 → t2 → t0
def ring (n : Nat) : R1 :=
  R1.corec (fun k => k) Nat.succ (fun k => k) Nat.succ (fun k => k) Nat.succ n

theorem rg0 : R1.a (ring 0) = 0 := rfl
theorem rg1 : R2.b (R1.nx (ring 0)) = 1 := rfl
theorem rg2 : R3.c (R2.nx (R1.nx (ring 0))) = 2 := rfl
theorem rg3 : R1.a (R3.nx (R2.nx (R1.nx (ring 0)))) = 3 := rfl
