import Init.Prelude
set_option genSizeOf false
mutual
  inductive Q2MixedUnit : Type where
    | mk
  inductive Q2MixedRec : Type where
    | zero
    | step : Q2MixedRec → Q2MixedRec
end
-- This true equality needs elimination: the mutual block's shared recursion
-- flag excludes even its field-free member from definitional unit equality.
theorem q2MixedUnitEq (x y : Q2MixedUnit) : x = y := by
  fail_if_success exact Eq.refl x
  cases x
  cases y
  rfl
