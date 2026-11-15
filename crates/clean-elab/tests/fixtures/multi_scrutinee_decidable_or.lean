theorem overflow_decide_or (p q : Prop) (dp : Decidable p) (dq : Decidable q) :
    @Decidable.decide (p ∨ q) (@instDecidableOr p q dp dq) =
      (@Decidable.decide p dp || @Decidable.decide q dq) :=
  match dp, dq with
  | .isTrue _, .isTrue _ => rfl
  | .isTrue _, .isFalse _ => rfl
  | .isFalse _, .isTrue _ => rfl
  | .isFalse _, .isFalse _ => rfl
