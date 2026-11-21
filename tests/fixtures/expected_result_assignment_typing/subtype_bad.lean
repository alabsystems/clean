theorem subtypeBad (p : Nat → Prop) (f : Nat → Subtype p) (i : Nat) (h : p 0) :
    @Subtype.mk Nat p 0 h = f i := rfl
