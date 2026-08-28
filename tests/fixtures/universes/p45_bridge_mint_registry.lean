-- U2 stage 3 — THE LEVEL-MINT REGISTRY: two mints cannot alias
-- (docs/analysis/u2-implementation-plan-2026-08-24.md §3 stage 3,
-- landed 2026-08-25; the residual stage 1 documented at its seeding site.)
--
-- Stage 1a seeded the tactic ProofState's universe counter with a `u64`
-- SNAPSHOT of the enclosing ElabCtx's. That closes the aliasing across a
-- whole `by` block but not WITHIN one: both authorities then start at the
-- same value `N`, and a single tactic STEP mints on both — its term
-- arguments through the ElabCtx (`elab_app` mints one level per declared
-- level param of every polymorphic head constant), its lemma instances on
-- the ProofState (`mk_const`, `resolve_env_rewrite_equation`). Level
-- identity IS the `u_N` string, so the first mid-block mint on each side
-- named the SAME level twice.
--
-- MEASURED at HEAD before the fix, on exactly the declarations below
-- (`CLEAN_U2_MINT_TRACE=1`, builtin prelude, no Mathlib): each one
-- double-minted `u_3`, and the two authorities held DIFFERENT values for it
-- at the bridge exit —
--   probe_have_then_rw   elabctx=S(0)  proofstate=u
--   probe_rw_then_have   elabctx=S(0)  proofstate=u
--   probe_two_worlds     elabctx=S(0)  proofstate=v
--   probe_nested_by      elabctx=S(0)  proofstate=u   (the sub-ProofState
--                        path: `create_sub_proof_state` COPIED the counter
--                        too, so a `have := by …` sub-proof and its parent
--                        aliased into one spliced proof term)
--   probe_abstract_have  elabctx=u_3   proofstate=S(0) (the ElabCtx's still
--                        ABSTRACT, awaiting generalization at declaration
--                        close, against a concrete tactic-side solution —
--                        the silent-monomorphization direction)
-- The bridge exit's `ps.metas.instantiate_levels(&proof)` realizes the
-- ProofState's value into EVERY occurrence of that name, the ElabCtx's
-- included.
--
-- These declarations kernel-check before AND after stage 3: at HEAD nothing
-- flipped, because every ElabCtx→ProofState handoff eagerly realizes the
-- ElabCtx's SOLVED levels first, so a conflatable occurrence did not survive
-- in these shapes. This fixture is therefore a REGRESSION pin on the shapes,
-- not a flip pin; the identity property itself is pinned structurally by
-- `infer::tests::tactic_bridge_levels`' stage-3 tests, which is where a
-- future re-split of the counter fails.

universe u v

def pid {α : Sort u} (a : α) : α := a

theorem pid_eq {α : Sort u} (a : α) : pid a = a := rfl

-- ElabCtx mint (the `have`'s Nat instance → level 1) then ProofState mint
-- (the rw lemma's instance → the declared rigid `u`).
theorem probe_have_then_rw {α : Sort u} (a b : α) (h : a = b) : pid a = b := by
  have hn : pid (0 : Nat) = 0 := pid_eq 0
  rw [pid_eq]
  exact h

-- The same collision with the mints in the opposite order.
theorem probe_rw_then_have {α : Sort u} (a b : α) (h : a = b) : pid a = b := by
  rw [pid_eq]
  have hn : pid (0 : Nat) = 0 := pid_eq 0
  exact h

-- Two declared universes in scope: the aliased name must not be able to
-- carry `1` on one side and `v` on the other.
theorem probe_two_worlds {α : Sort v} (a b : α) (h : a = b) : pid a = b := by
  have hn : pid (0 : Nat) = 0 := pid_eq 0
  have hm : pid (1 : Nat) = 1 := pid_eq 1
  rw [pid_eq]
  exact h

-- The sub-ProofState path: `have … := by …` opens a second ProofState whose
-- proof term is spliced into the parent's.
theorem probe_nested_by {α : Sort u} (a b : α) (h : a = b) : pid a = b := by
  have hn : pid (0 : Nat) = 0 := by rw [pid_eq]
  rw [pid_eq]
  exact h

-- The ABSTRACT direction: the `have`'s ascribed type leaves an ElabCtx-minted
-- level unsolved (it is generalized at declaration close), while the tactic
-- side solves its same-named mint concretely.
theorem probe_abstract_have (a b : Nat) (h : a = b) : pid a = b := by
  have hn : ∀ {β : Sort _} (x : β), pid x = x := fun x => pid_eq x
  rw [pid_eq]
  exact h
