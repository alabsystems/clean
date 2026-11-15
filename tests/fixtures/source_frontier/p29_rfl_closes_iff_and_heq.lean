-- p29 — `rfl` closes every `@[refl]` relation Lean core registers, not only
-- `Eq`: `Iff.refl` and `HEq.refl`.
--
-- PROVES: a goal `p ↔ p` (and `HEq n n`) closes by `rfl`, as it does in Lean,
-- whose `rfl` tactic dispatches on the goal's relation. Lean core itself
-- relies on the `Iff` case: every structure field declared
-- `f : ∀ a b, a < b ↔ … := by intros; rfl` (`Preorder.lt_iff_le_not_ge`,
-- `LinearOrder.min_def`, …) is discharged by `rfl` on an `Iff`.
--
-- MEASURED at HEAD f1d00283f (2026-09-10, before the change): 2 passed,
-- 3 failed — `iffRfl`, `iffAfterIntros` and `iffLtAfterIntros` died
-- `rigid head/arity mismatch: Eq vs Iff [raised under tactic rfl]`, the exact
-- failure `Pi.preorder`'s autoParam script hit on `Mathlib/Order/Basic.lean`
-- once the script ran at all. The pinned `lean` v4.30.0-rc2 accepts the file
-- verbatim.
--
-- IN-FILE CONTROLS: `eqRfl` (the `Eq` path, passing before and after) and
-- `iffExact` (an `Iff` goal closed by a hypothesis, so `Iff` goals as such
-- were never the problem — only `rfl` on them).
--
-- CONTROL FOR THE OTHER DIRECTION (`iffNotRefl_MUST_FAIL` is in p29's
-- sibling comment, not this file): `apply Iff.refl` still has to unify both
-- sides, so `p ↔ q` is refused exactly as `a = b` is by `Eq.refl`.
theorem eqRfl (n : Nat) : n = n := by rfl

theorem iffExact (p q : Prop) (h : p ↔ q) : p ↔ q := by exact h

theorem iffRfl (p : Prop) : p ↔ p := by rfl

theorem iffAfterIntros (a b : Nat) : (a ≤ b ↔ a ≤ b) := by intros; rfl

theorem iffLtAfterIntros : (∀ a b : Nat, a < b ↔ a < b) := by intros; rfl

theorem heqRfl (n : Nat) : HEq n n := by rfl
