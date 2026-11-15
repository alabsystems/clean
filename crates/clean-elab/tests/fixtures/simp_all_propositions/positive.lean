theorem parts (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  simp_all only [and_self]

theorem nested (P Q R : Prop) (h : P ∧ (Q ∧ R)) : R ∧ P := by
  simp_all only [and_self]

theorem duplicate (P : Prop) (h1 h2 : P) : P := by
  simp_all only [and_self]

theorem shadowed (P Q : Prop) (h : P) (h : Q) : P ∧ Q := by
  simp_all only [and_self]

theorem implication (P Q : Prop) (hp : P) (h : P → Q) : Q := by
  simp_all only [and_self]

theorem contradiction (P Q : Prop) (hp : P) (hn : ¬ P) : Q := by
  simp_all only [and_self]

theorem erased_shadow (P Q : Prop) (h : P) (h : Q) (hq : Q) : P ∧ Q := by
  simp_all only [-h, and_self]

theorem erased_other (P Q : Prop) (hp : P) (hq : Q) : Q := by
  simp_all only [-hp]
