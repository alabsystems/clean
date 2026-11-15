-- B6 control: `simp_all` does not use a sibling either.
axiom Q : Prop
mutual
theorem q1 : Q := by simp_all
theorem q2 : Q := q1
end
