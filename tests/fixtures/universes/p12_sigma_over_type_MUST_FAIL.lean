def probeT (E : Type → Type) : Type := Sigma (fun X : Type => E X)
