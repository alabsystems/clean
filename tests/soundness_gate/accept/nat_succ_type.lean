-- Soundness gate: Church-encoded booleans via forall/arrow
-- Source: clean-elab integration tests (type_checking.rs)
-- Expected: clean and Lean 4 both accept

def CBool := forall (A : Type), A -> A -> A
def ctrue : CBool := fun (A : Type) (x : A) (y : A) => x
def cfalse : CBool := fun (A : Type) (x : A) (y : A) => y
