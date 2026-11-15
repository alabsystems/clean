-- U2 stage 1 — LEVEL IDENTITY ACROSS THE ElabCtx↔ProofState BRIDGE
-- (docs/analysis/u2-implementation-plan-2026-08-24.md §1.3/§3 stage 1,
-- landed 2026-08-25).
--
-- A `by` block used to get a FRESH, EMPTY universe world: the ProofState
-- minted its own `u_0, u_1, …` (aliasing by STRING whatever the enclosing
-- declaration's ElabCtx had minted under those names, with nothing rigid
-- inside the block), its kernel checks were handed raw `Level::Param`s its
-- own unifier had already recorded equal, and level solutions recorded only
-- in `ps.metas` were dropped on the floor at the bridge exit. Measured faces
-- at the 5-file source-elab gate (`369ba0951`, sub-class A, 19 decls:
-- cast_heq_iff_heq, forall₂_true_iff, Subtype.mk_eq_mk, …):
--   `Tactic failed: type check failed: TypeMismatch {
--      expected: Sort(Param(u_X)), inferred: Sort(Param(u_0)) }`
-- and, on the rw face, spurious `RewriteNoMatch` on a lemma the goal
-- matches at a different param name.
--
-- Builtin-prelude repro, no Mathlib. Every probe forces ProofState-side
-- level minting (rw's env-lemma instantiation, apply's constant
-- instantiation, cases' recursor assembly) inside `.{u}`/`Sort v`
-- polymorphic goals. All must elaborate AND kernel-check. The
-- genuinely-conflicting twin stays a loud refusal — p42.

universe u v

def pid {α : Sort u} (a : α) : α := a

theorem pid_eq {α : Sort u} (a : α) : pid a = a := rfl

-- rw through a `.{u}`-polymorphic env lemma inside a `Sort v` goal.
theorem probe_rw {α : Sort v} (a b : α) (h : a = b) : pid a = b := by
  rw [pid_eq]
  exact h

-- apply of a `.{u}`-polymorphic constant against a rigid-`u` goal. The
-- baseline face was the exact sub-class A shape:
-- expected Sort(Param(u_2)), inferred Sort(Param(u)).
theorem probe_apply {α : Sort u} (a b : α) (h : a = b) : b = a := by
  apply Eq.symm
  exact h

-- cases on Eq inside a declared-universe goal, then the polymorphic rw.
theorem probe_cases {α β : Sort u} (e : α = β) (a : α) : pid a = a := by
  cases e
  rw [pid_eq]

-- Two independent declaration params at once: the bridge must keep u and v
-- distinct while solving the lemma instance's fresh param against v.
theorem probe_two_worlds {α : Sort u} {β : Sort v} (a : α) (b : β)
    (h : pid a = a) : pid b = b := by
  rw [pid_eq]

-- In-family control: the simp spelling passed BEFORE the bridge fix (simp's
-- own-name lemma convention plus its own level realization) and must keep
-- passing after it. `h` is in the list because Lean's simp has no
-- `assumption` step (G49): `simp [pid_eq]` alone leaves `a = b` (pinned 4.8.0).
theorem probe_simp_control {α : Sort v} (a b : α) (h : a = b) : pid a = b := by
  simp [pid_eq, h]

-- Same-universe spelling of the rw probe: the lemma's ProofState-minted
-- fresh param must solve against the SAME declared u the enclosing theorem
-- uses, without ever aliasing it by name.
theorem probe_rw_same {α : Sort u} (a b : α) (h : a = b) : pid a = b := by
  rw [pid_eq]
  exact h
