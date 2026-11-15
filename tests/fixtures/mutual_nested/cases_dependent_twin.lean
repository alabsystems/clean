-- Class (80) twin: in the `true` case `h` reads `true = true`, which does not
-- prove the goal `true = false`.
theorem bool_dep_twin (b : Bool) (h : b = true) : b = false := by
  cases b with
  | false => rfl
  | true => exact h
