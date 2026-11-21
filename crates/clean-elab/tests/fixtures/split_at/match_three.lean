inductive SplitThree where
  | first
  | second
  | third

theorem split_match_three (tag : SplitThree)
    (h : match tag with | .first => False | .second => True | .third => False) :
    tag = .second := by
  split at h <;> simp_all
