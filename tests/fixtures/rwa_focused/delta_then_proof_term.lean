def Wrapped (P : Prop) : Prop := P

theorem rwa_delta_then_proof_term (P Q : Prop) (e : P = Q)
    (h : True) (h : Wrapped P) : Q := by
  rwa [Wrapped, show P = Q from e] at h
