-- p03 — CLASS II, Pi sub-shape (35 of the 44 corpus entries).
--
-- PROVES: dot notation whose target does not resolve, on a receiver whose type
-- is a `def`-based Prop alias, reports the failure by NAMING the identifier
-- that failed to resolve (`MyInj.nosuchfield`) — not by dumping the receiver's
-- whnf'd type. `get_type_name` (infer/elab_match/helpers.rs:462) whnf's first,
-- so `MyInj f` becomes a `Pi` and the head is destroyed before it can be read.
--
-- This is the builtin-prelude reproduction of e.g. `Function.Surjective.forall₃`
-- → `cannot extract type name from Pi(Default, FVar(1), App(App(Const(Exists,…`
-- (`Surjective f` δ-unfolded to `∀ b, ∃ a, f a = b`).
--
-- CONTROL: p05 rules out "the diagnostic is wrong for every missing field" —
-- a `Const`-headed receiver already reports the named identifier. p01/p04/p13
-- rule out "non-`Const`-headed receivers cannot do dot notation at all": the
-- same shapes with a RESOLVABLE target pass.
def MyInj (f : Nat → Nat) : Prop := ∀ a b : Nat, f a = f b → a = b

theorem probe_missing_field {f : Nat → Nat} (h : MyInj f) : True :=
  h.nosuchfield
