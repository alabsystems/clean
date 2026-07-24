-- Soundness gate: Pi types, let binding, beta reduction
-- Source: clean-elab integration tests (basic.rs, type_checking.rs)
-- Expected: clean and Lean 4 both accept

def compose (A : Type) (B : Type) (C : Type) (f : B -> C) (g : A -> B) (x : A) := f (g x)
