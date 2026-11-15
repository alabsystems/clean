prelude
import Init.Tactics

/-! `native_decide` under the pinned Lean (v4.30.0-rc2): each use adds a
per-use auxiliary axiom `<decl>._native.native_decide.ax_N_M : decide p = true`
(`Lean.Meta.nativeEqTrue`) and closes the goal with
`of_decide_eq_true p s <that axiom>`. `decide` adds none. Read by
`crates/clean-olean/tests/native_decide_axiom_audit.rs`. -/

theorem nd_two_add : Eq (Nat.add 2 2) 4 := by native_decide
theorem nd_beq : Eq (Nat.beq 3 4) false := by native_decide
theorem dc_two_add : Eq (Nat.add 2 2) 4 := by decide
