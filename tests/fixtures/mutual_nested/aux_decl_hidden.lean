-- B6 control: `assumption` does not see a sibling (Lean skips auxiliary
-- declarations), so `r1` has no hypothesis to close `True` with.
mutual
theorem r1 : True := by assumption
theorem r2 : True := True.intro
end
