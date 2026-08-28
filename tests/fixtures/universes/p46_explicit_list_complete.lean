-- P46 — the PASS companion to p21's refusal (U2 rung-4 explicitness channel,
-- 2026-08-25).
--
-- p21 pins that an explicit `.{...}` list is CLOSED. A refusal is a claim
-- about what we do NOT accept, so it is only as good as the boundary around
-- it: over-refusing is a regression that a MUST_FAIL probe can never catch,
-- because a broken elaborator satisfies it just as well as a correct one.
-- This file pins the four neighbouring shapes that must keep elaborating —
-- one per way a level can reach declaration close without being a leak out of
-- a closed list.
--
-- Every declaration here PASSED before the channel landed and must still
-- pass; the `@f.{...}` use sites are not decoration, they force the
-- registered ARITY (a dropped or an appended parameter is a
-- `UniverseLevelMismatch` at the use site, which is how p21's divergence was
-- measured in the first place).

-- 1. The direct legitimate twin of p21's `leak`: same body shape, but the
--    written list NAMES both levels. Nothing leaks, so nothing is refused.
def noLeak.{u, v} (A : Type u) (a : A) := fun (B : Type v) (b : B) => b

def useNoLeak : Nat := @noLeak.{0, 0} Nat Nat.zero Nat Nat.zero

-- 2. A written list PLUS a `Type _` hole — the hole is DETERMINED (it unifies
--    with the declared `u`), so it never reaches the leftover set. The
--    refusal fires on UNDETERMINED levels, never on the presence of a hole;
--    a channel that keyed on "this declaration contains `_`" would break
--    here.
def holeDetermined.{u} (A : Type u) (a : A) : A := (fun (B : Type _) (b : B) => b) A a

def useDetermined : Nat := @holeDetermined.{0} Nat Nat.zero

-- 3. NO written list at all: p21's exact body, minus the `.{u}`. Both levels
--    are undetermined and both must still AUTO-GENERALIZE to a real
--    parameter — arity 2, forced by the use site. This is the over-refusal
--    guard for the common case: closure is a property of writing a list, not
--    of having leftover levels.
def leakOpen (A : Type _) (a : A) := fun (B : Type _) (b : B) => b

def useOpen : Nat := @leakOpen.{0, 0} Nat Nat.zero Nat Nat.zero

-- 4. The merged case — the one that caused the rung-4 scope cut. A file-scope
--    `universe` name is folded into the SAME parameter vector as a written
--    list by `preprocess_decl_with_context`, so an implementation that could
--    not tell them apart would have to treat every declaration in this file
--    as closed from here down. `leakScoped` writes NO list, uses the
--    file-scope `w`, and leaves one undetermined level: it must still extend
--    to arity 2.
--
--    Declared here rather than at the top of the file on purpose — the
--    declarations above must be measured with no `universe` command in scope,
--    or this guard and guard 3 would be the same test.
universe w

def leakScoped (A : Type w) (a : A) := fun (B : Type _) (b : B) => b

def useScoped : Nat := @leakScoped.{0, 0} Nat Nat.zero Nat Nat.zero
