theorem rwa_rollback_source_draft (P : Nat → Prop) (a b : Nat)
    (e : a = b) (h : P a) : P b := by
  first
  | rwa [e, e] at h
  | rwa [e] at h
