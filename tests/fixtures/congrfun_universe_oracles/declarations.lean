theorem q {β : Sort _} {F G : β → β} (h : F = G) : ∀ x, F x = G x := congrFun h

theorem q_at_prop (p : Prop) (F G : p → p) (h : F = G) : ∀ x, F x = G x :=
  @q p F G h

theorem q_at_bool (F G : Bool → Bool) (h : F = G) : ∀ x, F x = G x :=
  @q Bool F G h

theorem q_at_higher_type (F G : (Type → Type) → (Type → Type)) (h : F = G) :
    ∀ x, F x = G x :=
  @q (Type → Type) F G h
