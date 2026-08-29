-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- SPDX-License-Identifier: Apache-2.0
--
-- The COINDUCTIVE tier of the variant-codata surface, brick VC-6 of
-- designs/2026-08-28-variant-codata-surface.md.
--
-- The codata is DECLARED with `deriving Coind`. `ITr.child`, `ITr.cast`,
-- `ITr.ExtQ` and its companions, `ITr.ext`, every child extractor, every
-- eta law and every extractor computation pin are GENERATED. Everything
-- below the declaration is hand-written and cites only generated names.
--
-- WHY IT EXISTS. Eta is the one law in this surface that is NOT `rfl`:
-- `x = Tau (tauChild x)` cannot be checked by reduction, because `x` is
-- opaque and only the head hypothesis says anything about it. It is the
-- first thing here that needs `Codata.iM_coind`, i.e. actual coinduction.
--
-- The declaration covers all four position shapes VC-1 admits, on purpose:
--   Ret  -- EMPTY    (no recursive argument; `PEmpty.rec` discharge)
--   Tau  -- UNIT     (one bare child)
--   Vis  -- FAMILY   (one child indexed by `Ans e`)
--   Br   -- k-FOLD   (two bare children; dependent `Sum.rec` discharge)
--
-- Replayed by `codata_variant_coind_tests::test_eta_fixture_checks`.

codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
  | Br : ITr E R Ans → ITr E R Ans → ITr E R Ans
deriving Coind

-- ── The eta laws applied to CONSTRUCTOR values, where they are the
-- identity. Cheap, and they pin that the generated statement is the one a
-- caller can actually use.

theorem ITr.eta_on_Tau (E : Type) (R : Type) (Ans : E → Type) (t0 : ITr E R Ans) :
    ITr.Tau E R Ans t0
      = ITr.Tau E R Ans (ITr.TauChild E R Ans (ITr.Tau E R Ans t0) rfl) :=
  ITr.Tau_eta E R Ans (ITr.Tau E R Ans t0) rfl

theorem ITr.eta_on_Br (E : Type) (R : Type) (Ans : E → Type) (l : ITr E R Ans)
    (r : ITr E R Ans) :
    ITr.Br E R Ans l r
      = ITr.Br E R Ans (ITr.BrChild0 E R Ans (ITr.Br E R Ans l r) rfl)
          (ITr.BrChild1 E R Ans (ITr.Br E R Ans l r) rfl) :=
  ITr.Br_eta E R Ans (ITr.Br E R Ans l r) rfl

-- ── THE ANTI-VACUITY CASE: eta on a value with no constructor at its head.
--
-- `spin` is built by `corec`, not by a constructor, so `spin = Tau …` is
-- NOT `rfl` -- it is exactly the equation the tower model can only reach
-- through `iM_coind`. (Verified: stating it with `rfl` as the proof is
-- REJECTED, with a type mismatch on the `Subtype.mk` approximation tower.)

def ITr.spin (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s) PUnit.unit

theorem ITr.spin_unfolds (E : Type) (R : Type) (Ans : E → Type) :
    ITr.spin E R Ans = ITr.Tau E R Ans (ITr.spin E R Ans) :=
  ITr.Tau_eta E R Ans (ITr.spin E R Ans) rfl

def ITr.bspin (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1} (fun j s => ITr.step_Br E R Ans PUnit.{1} j s s) PUnit.unit

theorem ITr.bspin_unfolds (E : Type) (R : Type) (Ans : E → Type) :
    ITr.bspin E R Ans
      = ITr.Br E R Ans (ITr.bspin E R Ans) (ITr.bspin E R Ans) :=
  ITr.Br_eta E R Ans (ITr.bspin E R Ans) rfl

-- ── One-step extensionality used DIRECTLY, not through an eta law:
-- two corecursive values with the same head and pointwise-equal children
-- are equal. This is the general tool the eta laws are instances of.

def ITr.spin2 (E : Type) (R : Type) (Ans : E → Type) : ITr E R Ans :=
  ITr.corec E R Ans PUnit.{1}
    (fun j s => ITr.step_Tau E R Ans PUnit.{1} j s) PUnit.unit

theorem ITr.spin_eq_spin2 (E : Type) (R : Type) (Ans : E → Type) :
    ITr.spin E R Ans = ITr.spin2 E R Ans :=
  ITr.ext E R Ans (ITr.spin E R Ans) (ITr.spin2 E R Ans) rfl (fun b => rfl)

-- ── The remaining two position shapes, cited by name so every template is
-- exercised from the fixture and not merely generated.
theorem ITr.eta_on_Ret (E : Type) (R : Type) (Ans : E → Type) (r : R) :
    ITr.Ret E R Ans r = ITr.Ret E R Ans r :=
  ITr.Ret_eta E R Ans (ITr.Ret E R Ans r) r rfl

theorem ITr.eta_on_Vis (E : Type) (R : Type) (Ans : E → Type) (e : E)
    (k : Ans e → ITr E R Ans) :
    ITr.Vis E R Ans e k
      = ITr.Vis E R Ans e (ITr.VisChild E R Ans (ITr.Vis E R Ans e k) e rfl) :=
  ITr.Vis_eta E R Ans (ITr.Vis E R Ans e k) e rfl

-- ── The N-ary case tower (VC-6b), CONSUMED rather than merely generated.
--
-- `ITr.CasesP` and `ITr.cases` are generated; `ITr.casesOn` below is
-- hand-written on top of them and is the shape a caller actually wants: a
-- value is one of the four constructors, and each branch LEARNS the
-- equation. Writing it out is also what checks that the generated
-- disjunction nests the way the generator claims -- a wrong nesting or a
-- wrong existential arity would not typecheck here.

theorem ITr.casesOn (E : Type) (R : Type) (Ans : E → Type) (x : ITr E R Ans)
    (C : Prop)
    (hRet : ∀ r : R, x = ITr.Ret E R Ans r → C)
    (hTau : ∀ y : ITr E R Ans, x = ITr.Tau E R Ans y → C)
    (hVis : ∀ (e : E) (k : Ans e → ITr E R Ans), x = ITr.Vis E R Ans e k → C)
    (hBr : ∀ l : ITr E R Ans, ∀ r : ITr E R Ans,
      x = ITr.Br E R Ans l r → C) : C :=
  Or.elim (ITr.cases E R Ans x)
    (fun h => Exists.elim h (fun r hr => hRet r hr))
    (fun h =>
      Or.elim h
        (fun h2 => Exists.elim h2 (fun y hy => hTau y hy))
        (fun h2 =>
          Or.elim h2
            (fun h3 =>
              Exists.elim h3 (fun e he => Exists.elim he (fun k hk => hVis e k hk)))
            (fun h3 =>
              Exists.elim h3 (fun l hl => Exists.elim hl (fun r hr => hBr l r hr)))))

-- and the tower applied to a value with NO constructor at its head: `spin`
-- is corec-built, so this genuinely runs the dispatch.
theorem ITr.spin_is_some_constructor (E : Type) (R : Type) (Ans : E → Type) :
    ITr.CasesP E R Ans (ITr.spin E R Ans) :=
  ITr.cases E R Ans (ITr.spin E R Ans)
