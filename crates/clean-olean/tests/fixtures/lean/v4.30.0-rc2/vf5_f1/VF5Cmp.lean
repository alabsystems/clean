import VF5Bin

namespace VF5
open SemR

variable {m : Module}

theorem biased_lo {w a : Nat} (hw : 1 ≤ w) (h : a < half w) : biased w a = a + half w := by
  simp only [biased]; rw [mod_of_lt]; rw [modulus_two_half hw]; omega

theorem biased_hi {w a : Nat} (hw : 1 ≤ w) (ha : a < modulus w) (h : half w ≤ a) :
    biased w a = a - half w := by
  simp only [biased]; have := modulus_two_half hw
  rw [mod_of_lt2 (by omega) (by omega)]; omega

theorem biasSplit_cover {w : Nat} {e : Aff} {ρ : Nat → Int} {a : Nat} (hw : 1 ≤ w)
    (he : e.eval ρ = (a : Int)) (ha : a < modulus w) :
    ∃ p ∈ biasSplit w e, Sat p.1 ρ ∧ p.2.eval ρ = (biased w a : Int) := by
  by_cases h : a < half w
  · refine ⟨_, mem2 (Or.inl rfl), sat_one ?_, ?_⟩
    · rw [sat_le0]; simp [Hw, he]; omega
    · simp [biased_lo hw h, he, Hw]
  · refine ⟨_, mem2 (Or.inr rfl), sat_one ?_, ?_⟩
    · rw [sat_le0]; simp [Hw, he]; omega
    · simp [biased_hi hw ha (by omega), he, Hw]; omega

theorem biasSplit_scoped {w n : Nat} {e : Aff} (hs : e.Scoped n) :
    ∀ p ∈ biasSplit w e, CsScoped n p.1 ∧ p.2.Scoped n := by
  intro p hp
  simp only [biasSplit, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨scoped_one (scoped_le0 (scoped_addC _ hs)), scoped_addC _ hs⟩
  · exact ⟨scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) hs)), scoped_addC _ hs⟩

/-- Two-case comparisons on affine values decide the comparison. -/
theorem ult_cover {ρ : Nat → Int} {x y : Aff} {a b : Nat}
    (hx : x.eval ρ = (a : Int)) (hy : y.eval ρ = (b : Int)) :
    ∃ p ∈ ([([leAn x 1 y], true), ([leA y x], false)] : List (List Cons × Bool)),
      Sat p.1 ρ ∧ p.2 = decide (a < b) := by
  by_cases h : a < b
  · exact ⟨_, mem2 (Or.inl rfl), sat_one (by rw [sat_leAn]; omega), by simp [h]⟩
  · exact ⟨_, mem2 (Or.inr rfl), sat_one (by rw [sat_leA]; omega), by simp [h]⟩

theorem ule_cover {ρ : Nat → Int} {x y : Aff} {a b : Nat}
    (hx : x.eval ρ = (a : Int)) (hy : y.eval ρ = (b : Int)) :
    ∃ p ∈ ([([leA x y], true), ([leAn y 1 x], false)] : List (List Cons × Bool)),
      Sat p.1 ρ ∧ p.2 = decide (a ≤ b) := by
  by_cases h : a ≤ b
  · exact ⟨_, mem2 (Or.inl rfl), sat_one (by rw [sat_leA]; omega), by simp [h]⟩
  · exact ⟨_, mem2 (Or.inr rfl), sat_one (by rw [sat_leAn]; omega), by simp [h]⟩

theorem sgn_cover {w : Nat} {ρ : Nat → Int} {ea eb : Aff} {a b : Nat} (hw : 1 ≤ w)
    (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
    (ha' : a < modulus w) (hb' : b < modulus w)
    (f : Aff → Aff → List (List Cons × Bool)) (g : Nat → Nat → Bool)
    (hf : ∀ x y (u v : Nat), x.eval ρ = (u : Int) → y.eval ρ = (v : Int) →
      ∃ p ∈ f x y, Sat p.1 ρ ∧ p.2 = g u v) :
    ∃ p ∈ ((biasSplit w ea).flatMap fun (c1, x) =>
      (biasSplit w eb).flatMap fun (c2, y) =>
        (f x y).map fun (c3, r) => (c1 ++ c2 ++ c3, r)),
      Sat p.1 ρ ∧ p.2 = g (biased w a) (biased w b) := by
  obtain ⟨⟨c1, x⟩, h1, s1, e1⟩ := biasSplit_cover hw ha ha'
  obtain ⟨⟨c2, y⟩, h2, s2, e2⟩ := biasSplit_cover hw hb hb'
  obtain ⟨⟨c3, r⟩, h3, s3, e3⟩ := hf x y _ _ e1 e2
  refine ⟨(c1 ++ c2 ++ c3, r), ?_, Sat.append (Sat.append s1 s2) s3, e3⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨(c1, x), h1, (c2, y), h2, (c3, r), h3, rfl⟩

theorem cmpCases_cover (op : ICmpOp) {w : Nat} {ρ : Nat → Int} {ea eb : Aff} {a b : Nat}
    (hw : 1 ≤ w) (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
    (ha' : a < modulus w) (hb' : b < modulus w) :
    ∃ p ∈ cmpCases op w ea eb, Sat p.1 ρ ∧ p.2 = icmpR op w a b := by
  cases op
  case eq =>
    by_cases h : a = b
    · refine ⟨_, List.Mem.head _, ?_, by simp [icmpR, h]⟩
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> rw [sat_leA] <;> omega
    · by_cases h' : a < b
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), sat_one (by rw [sat_leAn]; omega),
          by simp [icmpR, h]⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          sat_one (by rw [sat_leAn]; omega), by simp [icmpR, h]⟩
  case ne =>
    by_cases h : a = b
    · refine ⟨_, List.Mem.head _, ?_, by simp [icmpR, h]⟩
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> rw [sat_leA] <;> omega
    · by_cases h' : a < b
      · exact ⟨_, List.Mem.tail _ (List.Mem.head _), sat_one (by rw [sat_leAn]; omega),
          by simp [icmpR, h]⟩
      · exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          sat_one (by rw [sat_leAn]; omega), by simp [icmpR, h]⟩
  case ult => simpa [cmpCases, icmpR] using ult_cover ha hb
  case ule => simpa [cmpCases, icmpR] using ule_cover ha hb
  case ugt => simpa [cmpCases, icmpR] using ult_cover hb ha
  case uge => simpa [cmpCases, icmpR] using ule_cover hb ha
  case slt =>
    simpa [cmpCases, icmpR] using
      sgn_cover hw ha hb ha' hb' _ (fun u v => decide (u < v)) (fun x y u v hx hy => ult_cover hx hy)
  case sle =>
    simpa [cmpCases, icmpR] using
      sgn_cover hw ha hb ha' hb' _ (fun u v => decide (u ≤ v)) (fun x y u v hx hy => ule_cover hx hy)
  case sgt =>
    simpa [cmpCases, icmpR] using
      sgn_cover hw ha hb ha' hb' (fun x y => [([leAn y 1 x], true), ([leA x y], false)])
        (fun u v => decide (v < u)) (fun x y u v hx hy => ult_cover hy hx)
  case sge =>
    simpa [cmpCases, icmpR] using
      sgn_cover hw ha hb ha' hb' (fun x y => [([leA y x], true), ([leAn x 1 y], false)])
        (fun u v => decide (v ≤ u)) (fun x y u v hx hy => ule_cover hy hx)

end VF5
