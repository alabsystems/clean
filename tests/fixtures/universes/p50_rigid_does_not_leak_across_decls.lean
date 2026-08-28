-- P50 — TRIPWIRE for the direction p47 does NOT cover, probed 2026-08-26 and
-- found CLEAN. U2 stage-3 deferral 1; note
-- docs/analysis/u2-stage3-deferrals-2026-08-26.md §1.6.
--
-- p47 is the "should be RIGID, treated as ASSIGNABLE" direction of the
-- partial rigidity predicate. This file pins the other one — "should be
-- ASSIGNABLE, treated as RIGID" — where the answer today is that the class is
-- NOT reachable. Nothing was implemented for it; these declarations are the
-- tripwire that fails if it ever becomes reachable.
--
-- The concrete hazard. `MetaState::rigid_level_params` is documented as "set
-- once per declaration; never entered into the undo trail because a fresh
-- ElabCtx (hence fresh MetaState) is built per declaration". If that stopped
-- holding — if a rigid name survived into the NEXT declaration while the
-- level mint (one shared monotone counter since U2 stage 3) reissued that
-- same `u_N` string — a fresh universe METAVARIABLE would be born rigid, and
-- `add_level_constraint` would refuse to solve it. The result is a spurious
-- loud reject: `cannot assign rigid universe parameter u_0 := …` on a
-- declaration that never wrote `u_0` at all.
--
-- Each pair below declares a rigid `u_0` FIRST and then asks a later
-- declaration to mint and SOLVE, so a leak shows up as a refusal rather than
-- as a silent pass. All PASS today (measured, release binary, builtin
-- prelude); the deliberate bridge-side rigidity of enclosing level names
-- inside a tactic block is a different, intended thing and is pinned by p42.

-- 1. Declared `.{u_0}`, then a later declaration whose hole must stay
--    solvable.
def leakDeclared.{u_0} (α : Sort u_0) (a : α) : α := a
def leakDeclaredAfter (β : Sort _) (b : β) : β := b

-- 2. The same, but the later declaration's hole must resolve to a CONCRETE
--    level rather than merely stay abstract.
def leakDeclaredForced (n : Nat) : Sort _ := Nat

-- 3. File-scope `universe` is the other writer of the rigid set; it is
--    declared at the bottom so it applies to the declarations after it and
--    the pair above stays a pure `.{u_0}` test.
universe u_1

def leakFile (α : Sort u_1) (a : α) : α := a
def leakFileAfter (n : Nat) : Sort _ := Nat
def leakFileAfterPoly (β : Sort _) (b : β) : β := b
