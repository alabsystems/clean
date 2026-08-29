import Init

-- G-AUTO family fixture: `decide` + `native_decide` (10 probes).
-- Reconstruction of the 2026-07-29 automation family
-- (docs/plans/TACTICS_TO_100_2026-07-29.md §3) at FAMILY-COUNT level; the
-- original probe fixtures lived in a dead session scratchpad and are not
-- probe-identical to these. Driven by scripts/tactic_parity/g_auto.sh.
--
-- The canary below is TERM-MODE (no tactic layer): it elaborates only if the
-- `import Init` header loaded the real Lean environment. `List.reverse_reverse`
-- exists nowhere in Clean's builtin or stub preludes (grep-verified), so a
-- stub-fallback run fails the canary and the gate refuses the measurement.

-- Environment canary. BOTH facts are absent from Clean's builtin/stub prelude and
-- present in real Init, so this declaration fails unless `import Init` genuinely
-- loaded. Its discriminating power is re-proved on every run rather than assumed
-- (family_gate.py --canary-check); the previous single-fact canary
-- `List.reverse_reverse` was silently disarmed on 2026-08-23 by 3df6e4aad, which
-- registered a kernel-proved copy of it INTO the builtin prelude.
theorem canary_env_g_auto_decide (as bs : List Nat) (n m : Nat) :
    (as ++ bs).reverse = bs.reverse ++ as.reverse ∧ n.succ - m.succ = n - m :=
  And.intro (List.reverse_append as bs) (Nat.succ_sub_succ_eq_sub n m)

theorem p_auto_decide_01 : (2 : Nat) ≤ 3 := by decide
theorem p_auto_decide_02 : ¬((3 : Nat) = 4) := by decide
theorem p_auto_decide_03 : (0 : Nat) < 1 := by decide
theorem p_auto_decide_04 : (true && false) = false := by decide
theorem p_auto_decide_05 : (10 : Nat) * 10 = 100 := by decide
theorem p_auto_decide_06 : Nat.blt 2 5 = true := by decide
theorem p_auto_decide_07 : (5 : Nat) % 2 = 1 := by decide
theorem p_auto_decide_08 : (2 : Nat) < 5 := by decide
theorem p_auto_native_01 : ¬((3 : Nat) = 4) := by native_decide
theorem p_auto_native_02 : (255 : Nat) + 1 = 256 := by native_decide
