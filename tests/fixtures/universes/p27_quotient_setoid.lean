-- The Lean 4 core quotient-by-a-setoid package (Equivalence, Setoid,
-- HasEquiv + the ≈ notation, Quotient), registered on top of the kernel's
-- existing Quot primitives. The ≈ notation had been DEAD SYNTAX: Clean's
-- lexer and parser already desugared it to HasEquiv.Equiv, which resolved
-- to no constant. Making it resolve additionally required the instance
-- synthesizer to unify the class constant's UNIVERSE LEVELS, since
-- HasEquiv.{u,v} carries a `v` that appears in no argument (only in the
-- Equiv field) and so could never be pinned by argument unification.
-- KNOWN GAPS still pinned elsewhere: bare `Equivalence.mk f g h` needs
-- @-form or ⟨⟩ (implicit inference from the expected type), and named
-- arguments on kernel-registered constants have no binder-name rows.
def trivRel (_ _ : Nat) : Prop := True
theorem trivEquiv : Equivalence trivRel :=
  ⟨fun _ => True.intro, fun {_ _} _ => True.intro, fun {_ _ _} _ _ => True.intro⟩
instance trivSetoid : Setoid Nat := ⟨trivRel, trivEquiv⟩

-- the ≈ notation, dead until now
theorem eqv1 : (1 : Nat) ≈ 2 := True.intro
theorem eqv_unfolds : ((1 : Nat) ≈ 2) = trivRel 1 2 := rfl

-- Quotient formation and the sound axiom
def Q : Type := Quotient trivSetoid
-- CORRECTION (2026-08-11): an earlier revision of this comment claimed
-- these rfl identities failed on a reducibility fork. That was measured
-- with `def trivSetoid` instead of `instance`, and was WRONG. The δ/ι
-- chain Quotient -> Quot (Setoid.r s) -> Proj -> trivRel fires fine at
-- default transparency with Setoid.r semireducible, so both pin here.
theorem q_is_quot : Quotient trivSetoid = Quot trivRel := rfl
theorem mk_is_quotmk (x : Nat) : Quotient.mk trivSetoid x = Quot.mk trivRel x := rfl
-- Still NOT pinned, and now correctly diagnosed: the same identity with a
-- BARE NUMERIC LITERAL (`... trivSetoid 3 = ... trivRel 3`) fails, and not
-- for any defeq reason -- two syntactically IDENTICAL operands also fail.
-- It is the `bare_nat_literal_in_open_slot` pre-arg-unify gate assigning
-- the still-open expected metavariable. Named as its own brick.
-- (`Quotient.sound` is likewise not pinned yet: it needs the same δ-chain
-- through Quotient/Quotient.mk. Measured: flipping Setoid.r to reducible
-- does not unblock it, so the fork is further down. Named as the next brick.)
