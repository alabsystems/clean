import VF5Cmp

namespace VF5
open SemR

variable {m : Module}

theorem brcov2_same {ρ : Nat → Int} {nv : Nat} {cs : List Cons} {t : IntTy} {e : Aff} {c : Nat}
    {f : Bool} (h : Sat cs ρ) (hcs : CsScoped nv cs) (he : e.eval ρ = (c : Int))
    (hc : c < modulus t.bits) (hs : e.Scoped nv) :
    BrCovers m ρ nv ⟨cs, [.int t e, .bool f], nv⟩ [.int t c, .bool f] := by
  refine ⟨ρ, Agree.refl ρ nv, h, Nat.le_refl _, hcs, rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨c, rfl, hc, he⟩
    · rfl
  · intro s hs'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
    rcases hs' with rfl | rfl
    · exact hs
    · trivial

theorem brcov2_fresh {ρ : Nat → Int} {nv : Nat} {pre : List Cons} {t : IntTy} {c : Nat} {f : Bool}
    (h : Sat pre ρ) (hcs : CsScoped nv pre) (hc : c < modulus t.bits) :
    BrCovers m ρ nv ⟨pre ++ rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv), .bool f], nv + 1⟩
      [.int t c, .bool f] := by
  obtain ⟨ρ', hag, hsat, hsc, hrel, hss⟩ := fresh_covers (m := m) ρ nv t c hc
  refine ⟨ρ', hag, Sat.append (Sat.congr hcs hag h) hsat, Nat.le_succ _,
    CsScoped.append (hcs.mono (Nat.le_succ _)) hsc, rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact hrel
    · rfl
  · intro s hs'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
    rcases hs' with rfl | rfl
    · exact hss
    · trivial

theorem signSplit_cover {w : Nat} {e : Aff} {ρ : Nat → Int} {a : Nat}
    (he : e.eval ρ = (a : Int)) :
    ∃ p ∈ signSplit w e, Sat p.1 ρ ∧ p.2 = isNeg w a := by
  by_cases h : half w ≤ a
  · exact ⟨_, mem2 (Or.inr rfl), sat_one (by rw [sat_le0]; simp [Hw, he]; omega), by simp [isNeg, h]⟩
  · exact ⟨_, mem2 (Or.inl rfl), sat_one (by rw [sat_le0]; simp [Hw, he]; omega), by simp [isNeg, h]⟩

theorem signSplit_scoped {w n : Nat} {e : Aff} (hs : e.Scoped n) :
    ∀ p ∈ signSplit w e, CsScoped n p.1 := by
  intro p hp
  simp only [signSplit, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact scoped_one (scoped_le0 (scoped_addC _ hs))
  · exact scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) hs))

section
variable {t : IntTy} {ea eb : Aff} {nv : Nat} {ρ : Nat → Int} {a b : Nat}
  (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
  (ha' : a < modulus t.bits) (hb' : b < modulus t.bits)
  (hsa : ea.Scoped nv) (hsb : eb.Scoped nv)
include ha hb ha' hb' hsa hsb

/-- The wrapped sum: which case, its constraint, and the residue. -/
theorem addW_cover :
    ∃ p ∈ ([([le0 ((ea.add eb).addC (-(Mw t.bits - 1)))], ea.add eb),
            ([le0 ((Aff.c (Mw t.bits)).sub (ea.add eb))], (ea.add eb).addC (-(Mw t.bits)))] :
            List (List Cons × Aff)),
      Sat p.1 ρ ∧ CsScoped nv p.1 ∧ p.2.Scoped nv ∧ p.2.eval ρ = (((a + b) % modulus t.bits : Nat) : Int) := by
  by_cases hlt : a + b < modulus t.bits
  · refine ⟨_, mem2 (Or.inl rfl), sat_one ?_, scoped_one (scoped_le0 (scoped_addC _ (scoped_add hsa hsb))),
      scoped_add hsa hsb, ?_⟩
    · rw [sat_le0]; simp [Mw, ha, hb]; omega
    · rw [mod_of_lt hlt]; simp [ha, hb]
  · refine ⟨_, mem2 (Or.inr rfl), sat_one ?_,
      scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) (scoped_add hsa hsb))),
      scoped_addC _ (scoped_add hsa hsb), ?_⟩
    · rw [sat_le0]; simp [Mw, ha, hb]; omega
    · rw [mod_of_lt2 (by omega) (by omega)]; simp [Mw, ha, hb]; omega

theorem subW_cover :
    ∃ p ∈ ([([leA eb ea], ea.sub eb), ([leAn ea 1 eb], (ea.sub eb).addC (Mw t.bits))] :
            List (List Cons × Aff)),
      Sat p.1 ρ ∧ CsScoped nv p.1 ∧ p.2.Scoped nv ∧
        p.2.eval ρ = (((a + (modulus t.bits - b % modulus t.bits)) % modulus t.bits : Nat) : Int) := by
  rw [mod_of_lt hb']
  by_cases hle : b ≤ a
  · refine ⟨_, mem2 (Or.inl rfl), sat_one ?_, scoped_one (scoped_leA hsb hsa), scoped_sub hsa hsb, ?_⟩
    · rw [sat_leA]; simp [ha, hb]; omega
    · rw [mod_of_lt2 (by omega) (by omega)]; simp [ha, hb]; omega
  · refine ⟨_, mem2 (Or.inr rfl), sat_one ?_, scoped_one (scoped_leAn _ hsa hsb),
      scoped_addC _ (scoped_sub hsa hsb), ?_⟩
    · rw [sat_leAn]; simp [ha, hb]; omega
    · rw [mod_of_lt (by omega)]; simp [Mw, ha, hb]; omega

theorem signed_cover (ws : List (List Cons × Aff)) (r : Nat) (flag : Bool → Bool → Bool → Bool)
    (hw : ∃ p ∈ ws, Sat p.1 ρ ∧ CsScoped nv p.1 ∧ p.2.Scoped nv ∧ p.2.eval ρ = (r : Int))
    (hr : r < modulus t.bits) :
    ∃ br ∈ (ws.flatMap fun (cw, re) =>
      (signSplit t.bits ea).flatMap fun (c1, sa) =>
        (signSplit t.bits eb).flatMap fun (c2, sb) =>
          (signSplit t.bits re).map fun (c3, sr) =>
            (⟨cw ++ c1 ++ c2 ++ c3, [.int t re, .bool (flag sa sb sr)], nv⟩ : Br)),
      BrCovers m ρ nv br [.int t r, .bool (flag (isNeg t.bits a) (isNeg t.bits b) (isNeg t.bits r))] := by
  obtain ⟨⟨cw, re⟩, hm, hs, hsc, hres, hre⟩ := hw
  obtain ⟨⟨c1, sa⟩, h1, s1, e1⟩ := signSplit_cover (w := t.bits) ha
  obtain ⟨⟨c2, sb⟩, h2, s2, e2⟩ := signSplit_cover (w := t.bits) hb
  obtain ⟨⟨c3, sr⟩, h3, s3, e3⟩ := signSplit_cover (w := t.bits) hre
  simp only at e1 e2 e3
  subst e1 e2 e3
  refine ⟨_, ?_, brcov2_same (m := m) (Sat.append (Sat.append (Sat.append hs s1) s2) s3)
    (CsScoped.append (CsScoped.append (CsScoped.append hsc (signSplit_scoped hsa _ h1))
      (signSplit_scoped hsb _ h2)) (signSplit_scoped hres _ h3)) hre hr hres⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨(cw, re), hm, (c1, _), h1, (c2, _), h2, (c3, _), h3, rfl⟩

theorem ovfCases_cover (op : OvfOp) :
    ∃ br ∈ ovfCases op t ea eb nv,
      BrCovers m ρ nv br [.int t (ovf op t.signed t.bits a b).1, .bool (ovf op t.signed t.bits a b).2] := by
  have hm := modulus_pos t.bits
  cases op <;> cases hs : t.signed
  case add.false =>
    obtain ⟨p, hp, hsat, hsc, hps, hpe⟩ := addW_cover ha hb ha' hb' hsa hsb
    simp only [ovfCases, ovf, hs]
    by_cases hlt : a + b < modulus t.bits
    · refine ⟨_, mem2 (Or.inl rfl), ?_⟩
      have := brcov2_same (m := m) (t := t) (f := false) (sat_one (c := le0 ((ea.add eb).addC (-(Mw t.bits - 1))))
        (by rw [sat_le0]; simp [Mw, ha, hb]; omega))
        (scoped_one (scoped_le0 (scoped_addC _ (scoped_add hsa hsb))))
        (show (ea.add eb).eval ρ = (((a + b) % modulus t.bits : Nat) : Int) by rw [mod_of_lt hlt]; simp [ha, hb])
        (Nat.mod_lt _ hm) (scoped_add hsa hsb)
      simpa [show decide (modulus t.bits ≤ a + b) = false by simp; omega] using this
    · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
      have := brcov2_same (m := m) (t := t) (f := true) (sat_one (c := le0 ((Aff.c (Mw t.bits)).sub (ea.add eb)))
        (by rw [sat_le0]; simp [Mw, ha, hb]; omega))
        (scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) (scoped_add hsa hsb))))
        (show ((ea.add eb).addC (-(Mw t.bits))).eval ρ = (((a + b) % modulus t.bits : Nat) : Int) by
          rw [mod_of_lt2 (by omega) (by omega)]; simp [Mw, ha, hb]; omega)
        (Nat.mod_lt _ hm) (scoped_addC _ (scoped_add hsa hsb))
      simpa [show decide (modulus t.bits ≤ a + b) = true by simp; omega] using this
  case sub.false =>
    simp only [ovfCases, ovf, hs]
    rw [mod_of_lt hb']
    by_cases hle : b ≤ a
    · refine ⟨_, mem2 (Or.inl rfl), ?_⟩
      have := brcov2_same (m := m) (t := t) (f := false) (sat_one (c := leA eb ea) (by rw [sat_leA]; simp [ha, hb]; omega))
        (scoped_one (scoped_leA hsb hsa))
        (show (ea.sub eb).eval ρ = (((a + (modulus t.bits - b)) % modulus t.bits : Nat) : Int) by
          rw [mod_of_lt2 (by omega) (by omega)]; simp [ha, hb]; omega)
        (Nat.mod_lt _ hm) (scoped_sub hsa hsb)
      simpa [show decide (a < b) = false by simp; omega] using this
    · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
      have := brcov2_same (m := m) (t := t) (f := true) (sat_one (c := leAn ea 1 eb) (by rw [sat_leAn]; simp [ha, hb]; omega))
        (scoped_one (scoped_leAn _ hsa hsb))
        (show ((ea.sub eb).addC (Mw t.bits)).eval ρ = (((a + (modulus t.bits - b)) % modulus t.bits : Nat) : Int) by
          rw [mod_of_lt (by omega)]; simp [Mw, ha, hb]; omega)
        (Nat.mod_lt _ hm) (scoped_addC _ (scoped_sub hsa hsb))
      simpa [show decide (a < b) = true by simp; omega] using this
  case add.true =>
    simpa [ovfCases, ovf, hs] using signed_cover ha hb ha' hb' hsa hsb _ _ (fun sa sb sr => sa == sb && sr != sa) (addW_cover ha hb ha' hb' hsa hsb) (Nat.mod_lt _ hm)
  case sub.true =>
    simpa [ovfCases, ovf, hs] using signed_cover ha hb ha' hb' hsa hsb _ _ (fun sa sb sr => sa != sb && sr != sa) (subW_cover ha hb ha' hb' hsa hsb) (Nat.mod_lt _ hm)
  case mul.false =>
    simp only [ovfCases, ovf, hs, freshInt]
    split
    · next hk =>
      have hbk : eb.k = (b : Int) := by rw [← eval_isConst eb ρ hk]; exact hb
      have hp : (ea.smul eb.k).eval ρ = ((a * b : Nat) : Int) := by
        simp only [eval_smul, ha, hbk, Int.natCast_mul, Int.mul_comm]
      by_cases hlt : a * b < modulus t.bits
      · refine ⟨_, mem2 (Or.inl rfl), ?_⟩
        have := brcov2_same (m := m) (t := t) (f := false)
          (sat_one (c := le0 ((ea.smul eb.k).addC (-(Mw t.bits - 1)))) (by rw [sat_le0, eval_addC, hp]; simp [Mw]; omega))
          (scoped_one (scoped_le0 (scoped_addC _ (scoped_smul _ hsa))))
          (show (ea.smul eb.k).eval ρ = (((a * b) % modulus t.bits : Nat) : Int) by rw [hp, mod_of_lt hlt])
          (Nat.mod_lt _ hm) (scoped_smul _ hsa)
        simpa [show decide (modulus t.bits ≤ a * b) = false by simp; omega] using this
      · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
        have := brcov2_fresh (m := m) (ρ := ρ) (nv := nv) (t := t) (f := true)
          (sat_one (c := le0 ((Aff.c (Mw t.bits)).sub (ea.smul eb.k))) (by rw [sat_le0, eval_sub, hp]; simp [Mw]; omega))
          (scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) (scoped_smul _ hsa))))
          (Nat.mod_lt (a * b) hm)
        simpa [show decide (modulus t.bits ≤ a * b) = true by simp; omega] using this
    · cases hd : decide (modulus t.bits ≤ a * b)
      · refine ⟨_, mem2 (Or.inl rfl), ?_⟩
        simpa using brcov2_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t) (f := false) (sat_nil ρ)
          (fun _ h => nomatch h) (Nat.mod_lt (a * b) hm)
      · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
        simpa using brcov2_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t) (f := true) (sat_nil ρ)
          (fun _ h => nomatch h) (Nat.mod_lt (a * b) hm)
  case mul.true =>
    simp only [ovfCases, ovf, hs, freshInt]
    generalize (if isNeg t.bits a != isNeg t.bits b then decide (half t.bits < mag t.bits a * mag t.bits b)
          else decide (half t.bits ≤ mag t.bits a * mag t.bits b)) = fl
    cases fl
    · refine ⟨_, mem2 (Or.inl rfl), ?_⟩
      simpa using brcov2_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t) (f := false) (sat_nil ρ)
        (fun _ h => nomatch h) (Nat.mod_lt (a * b) hm)
    · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
      simpa using brcov2_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t) (f := true) (sat_nil ρ)
        (fun _ h => nomatch h) (Nat.mod_lt (a * b) hm)

theorem unCases_cover {op : UnOp} {bs : List Br} (hc : unCases op t ea = some bs) :
    ∃ br ∈ bs.map (fun b => { b with nv := nv }), BrCovers m ρ nv br [.int t (intUn op t.bits a)] := by
  have hm := modulus_pos t.bits
  cases op <;> simp only [unCases, Option.some.injEq, reduceCtorEq] at hc
  case neg =>
    subst hc
    simp only [intUn, negR, mod_of_lt ha', List.map_cons, List.map_nil]
    by_cases h0 : a = 0
    · subst h0
      refine ⟨_, mem2 (Or.inl rfl), brcov_same (m := m) (sat_one (by rw [sat_le0, ha]; decide))
        (scoped_one (scoped_le0 hsa)) (by simp) (by simp; exact hm) (scoped_c _ _)⟩
    · refine ⟨_, mem2 (Or.inr rfl), brcov_same (m := m) (sat_one (by rw [sat_le0]; simp [ha]; omega))
        (scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) hsa))) ?_ (Nat.mod_lt _ hm)
        (scoped_sub (scoped_c _ _) hsa)⟩
      rw [mod_of_lt (by omega)]; simp [Mw, ha]; omega
  case not =>
    subst hc
    simp only [intUn, mod_of_lt ha', List.map_cons, List.map_nil]
    refine ⟨_, List.Mem.head _, brcov_same (m := m) (sat_nil ρ) (fun _ h => nomatch h) ?_ (by omega)
      (scoped_sub (scoped_c _ _) hsa)⟩
    simp [Mw, ha]; omega

end

end VF5
