theorem subtypeEtaApply (p : Nat → Prop) (f : Nat → Subtype p) (i : Nat) :
    @Subtype.mk Nat p (f i).val (f i).property = f i := rfl
