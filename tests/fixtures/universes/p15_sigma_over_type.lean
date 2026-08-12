-- The Type→Type event-functor INGREDIENT (P12's positive form): a large
-- Sigma over Type itself, correctly ascribed Type 1, with construction.
-- P12's `: Type` version stays a SOUND forever-reject (ill-typed in Lean
-- too) — this fixture pins the working large-universe forms.
def probeT (E : Type → Type) : Type 1 := Sigma (fun X : Type => E X)
def probeUse (E : Type → Type) (X : Type) (v : E X) : probeT E := Sigma.mk X v
