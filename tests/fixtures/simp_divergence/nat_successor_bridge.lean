-- Reproducer for docs/issues/2026-08-28-simp-diverges-bridging-nat-successor-spellings.md
--
-- `simp` diverges on a Nat `+` goal whose two sides differ by an ASSOCIATIVE
-- REGROUPING, and finishes in microseconds on everything adjacent. Each row
-- below is a measurement, not an illustration: the numbers are the
-- per-declaration kernel-operation counts read off
-- `CLEAN_CHECK_DECL_BUDGET_TRACE=1` on 2026-08-28 with target/release/clean at
-- 9f035774c. DIVERGED rows spent a whole 20,000,000-operation budget without
-- finishing.
--
--   clean check --json --decl-budget 20000000 \
--     tests/fixtures/simp_divergence/nat_successor_bridge.lean
--
-- MEASURED, not predicted — this exact file, 2026-08-28:
--   status "fail" | 16 declarations | 10 passed | 1 failed | 5 diverged
--
-- The per-declaration counts below drift a few percent with file order (the
-- kernel's memo caches are warm by the time the later rows run: the same
-- `lsf (lsf n) = lsf (lsf n)` goal cost 12,935 as the first probe of its own
-- file and 93 here). Treat them as orders of magnitude, which is the only
-- scale the point needs.
--
-- This file is NOT wired into a cargo test on purpose. Four of its ten
-- declarations do not terminate under any budget yet measured, and it needs a
-- real `import Init` (~55 s) to say anything at all; a suite row would be a
-- multi-minute known-red. It is pinned here so the class has a reproducer that
-- cannot drift, and so the fix — when it lands — has something to flip.
--
-- One instrument does sweep this tree: `scripts/decl_budget_calibrate.sh`
-- runs an UNREACHABLE budget over `demos tests/fixtures`, so it will not
-- finish this file. That script already documents the situation ("some
-- fixtures are deliberately pathological") and already tells its caller to
-- narrow CORPUS_ROOTS; this file is one more of those, named here so the
-- next person to hit it knows which one.
import Init

def lsf (n : Nat) : Nat := n + 1

@[simp] theorem lsf_eq (n : Nat) : lsf n = n + 1 := rfl

-- CONTROLS. Identical sides, or an ordinary nested rewrite, or the kernel
-- doing the whole job definitionally. All cheap.
theorem ok_same_sides_flat (n : Nat) : n + 1 = n + 1 := by simp          -- 13,013
theorem ok_same_sides_nested (n : Nat) : n + 1 + 1 = n + 1 + 1 := by simp --    294
theorem ok_same_sides_var (n m : Nat) : n + m = n + m := by simp         --    136
theorem ok_nested_lemma (n : Nat) : lsf (lsf n) = lsf (lsf n) := by simp --      93
theorem ok_regrouping_by_rfl (n : Nat) : n + 1 + 1 = n + 2 := by rfl     --    364
-- Dear but finishing — the cost curve is already steep two thousand-fold
-- before it goes over the cliff.
theorem ok_zero_regrouping (n : Nat) : n + 0 + 1 = n + 1 := by simp      -- 568,895

-- THE CLASS. Two sides of a Nat `+` that differ only by regrouping.
-- `div_pure_assoc` carries NO literals and no user lemma at all, which is what
-- rules out literal folding and rules out `lsf` as the cause.
theorem div_lit_regrouping (n : Nat) : n + 1 + 1 = n + 2 := by simp
theorem div_lit_regrouping_mirror (n : Nat) : n + 2 = n + 1 + 1 := by simp
theorem div_pure_assoc (n m : Nat) : n + m + 1 = n + (m + 1) := by simp
theorem div_via_local_simp_lemma (n : Nat) : lsf (lsf n) = n + 2 := by simp

-- THE PROXIMATE TRIGGER: bridging two spellings of one Nat successor. ONE
-- bridge costs 285,274 operations where the kernel does the whole goal in 174;
-- TWO does not finish. This is the same cliff with `Nat.succ` in place of
-- `+ 1`, and it is why the G-SIMP row `p_simp_core_27`
-- (`(a :: l).length = l.length + 1`) diverges while its sibling
-- `p_simp_core_28` (`(l.map f).length = l.length`, no `+`) passes.
theorem ok_one_succ_bridge (n : Nat) : Nat.succ n = n + 1 := by simp     -- 285,274
theorem ok_one_succ_bridge_rfl (n : Nat) : Nat.succ n = n + 1 := by rfl  --     174
theorem div_two_succ_bridges (n : Nat) : Nat.succ (Nat.succ n) = n + 2 := by simp

-- The small isolated defect underneath. `Nat.succ_eq_add_one` is the rewrite
-- Lean uses to close this goal; `simp only` accepts the name and the goal does
-- not move. Residual goal measured 2026-08-28, 315 operations:
--   ⊢ Nat.succ (List.length Nat fvar#0) = List.length Nat fvar#0 + 1
-- whose LHS is the post-`List.length_cons` form — so that lemma fired and this
-- one did not. That reading is off the printed goal and is to be CONFIRMED
-- with a lemma-fire tracer, not built on.
theorem fail_succ_eq_add_one_is_a_no_op (l : List Nat) (a : Nat) :
    (a :: l).length = l.length + 1 := by
  simp only [List.length_cons, Nat.succ_eq_add_one]
