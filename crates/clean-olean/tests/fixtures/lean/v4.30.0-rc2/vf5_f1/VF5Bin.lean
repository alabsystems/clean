import VF7Bits

namespace VF5
open SemR

variable {m : Module}

theorem intBin_lt_add {w a b : Nat} : (a + b) % modulus w < modulus w := Nat.mod_lt _ (modulus_pos w)

/-- The covering statement for an integer binary operator. -/
def BinCover (m : Module) (op : BinOp) (t : IntTy) (ea eb : Aff) (nv : Nat) (ubs : List (List Cons))
    (bs : List Br) (ρ : Nat → Int) (a b : Nat) : Prop :=
  (∀ c, intBin op t.bits a b = .ok c → ∃ br ∈ bs, BrCovers m ρ nv br [.int t c]) ∧
  (∀ msg, intBin op t.bits a b = .ub msg → ∃ u ∈ ubs, Sat u ρ) ∧
  (∀ msg, intBin op t.bits a b ≠ .tyErr msg) ∧ (∀ f, intBin op t.bits a b ≠ .unsup f)

theorem negR_lt (w x : Nat) : negR w x < modulus w := Nat.mod_lt _ (modulus_pos w)

section
variable {t : IntTy} {ea eb : Aff} {nv : Nat} {ρ : Nat → Int} {a b : Nat}
  (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
  (ha' : a < modulus t.bits) (hb' : b < modulus t.bits)
  (hsa : ea.Scoped nv) (hsb : eb.Scoped nv)
include ha hb ha' hb' hsa hsb

theorem cover_add :
    BinCover m .add t ea eb nv []
      [⟨[le0 ((ea.add eb).addC (-(Mw t.bits - 1)))], [.int t (ea.add eb)], nv⟩,
       ⟨[le0 ((Aff.c (Mw t.bits)).sub (ea.add eb))], [.int t ((ea.add eb).addC (-(Mw t.bits)))], nv⟩]
      ρ a b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c h
    simp only [intBin, OpRes.ok.injEq] at h
    subst h
    by_cases hlt : a + b < modulus t.bits
    · refine ⟨_, mem2 (Or.inl rfl), brcov_same (m := m) (sat_one ?_) (scoped_one (scoped_le0
        (scoped_addC _ (scoped_add hsa hsb)))) ?_ (Nat.mod_lt _ (modulus_pos _)) (scoped_add hsa hsb)⟩
      · rw [sat_le0]; simp [Mw, ha, hb]; omega
      · rw [mod_of_lt hlt]; simp [ha, hb]
    · refine ⟨_, mem2 (Or.inr rfl), brcov_same (m := m) (sat_one ?_) (scoped_one (scoped_le0
        (scoped_sub (scoped_c _ _) (scoped_add hsa hsb)))) ?_ (Nat.mod_lt _ (modulus_pos _))
        (scoped_addC _ (scoped_add hsa hsb))⟩
      · rw [sat_le0]; simp [Mw, ha, hb]; omega
      · rw [mod_of_lt2 (by omega) (by omega)]; simp [Mw, ha, hb]; omega
  · intro msg h; simp [intBin] at h
  · intro msg h; simp [intBin] at h
  · intro f h; simp [intBin] at h

theorem cover_sub :
    BinCover m .sub t ea eb nv []
      [⟨[leA eb ea], [.int t (ea.sub eb)], nv⟩,
       ⟨[leAn ea 1 eb], [.int t ((ea.sub eb).addC (Mw t.bits))], nv⟩]
      ρ a b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c h
    simp only [intBin, OpRes.ok.injEq] at h
    subst h
    rw [mod_of_lt hb']
    by_cases hle : b ≤ a
    · refine ⟨_, mem2 (Or.inl rfl), brcov_same (m := m) (sat_one ?_) (scoped_one (scoped_leA hsb hsa)) ?_
        (Nat.mod_lt _ (modulus_pos _)) (scoped_sub hsa hsb)⟩
      · rw [sat_leA]; simp [ha, hb]; omega
      · rw [mod_of_lt2 (by omega) (by omega)]; simp [ha, hb]; omega
    · refine ⟨_, mem2 (Or.inr rfl), brcov_same (m := m) (sat_one ?_) (scoped_one (scoped_leAn _ hsa hsb)) ?_
        (Nat.mod_lt _ (modulus_pos _)) (scoped_addC _ (scoped_sub hsa hsb))⟩
      · rw [sat_leAn]; simp [ha, hb]; omega
      · rw [mod_of_lt (by omega)]; simp [Mw, ha, hb]; omega
  · intro msg h; simp [intBin] at h
  · intro msg h; simp [intBin] at h
  · intro f h; simp [intBin] at h

theorem cover_fresh_ok {op : BinOp} {ubs : List (List Cons)}
    (hok : ∀ c, intBin op t.bits a b = .ok c → c < modulus t.bits)
    (hub : ∀ msg, intBin op t.bits a b = .ub msg → ∃ u ∈ ubs, Sat u ρ)
    (hty : ∀ msg, intBin op t.bits a b ≠ .tyErr msg) (hun : ∀ f, intBin op t.bits a b ≠ .unsup f) :
    BinCover m op t ea eb nv ubs
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  refine ⟨?_, hub, hty, hun⟩
  intro c h
  have := brcov_fresh (m := m) (ρ := ρ) (nv := nv) (pre := []) (t := t) (sat_nil ρ)
    (fun _ h => nomatch h) (hok c h)
  exact ⟨_, List.Mem.head _, by simpa using this⟩

theorem cover_mul_const (hk : eb.isConst = true) :
    BinCover m .mul t ea eb nv []
      [⟨[le0 ((ea.smul eb.k).addC (-(Mw t.bits - 1)))], [.int t (ea.smul eb.k)], nv⟩,
       ⟨le0 ((Aff.c (Mw t.bits)).sub (ea.smul eb.k)) :: rangeCs t.bits (Aff.v nv),
        [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  have hbk : eb.k = (b : Int) := by rw [← eval_isConst eb ρ hk]; exact hb
  have hp : (ea.smul eb.k).eval ρ = ((a * b : Nat) : Int) := by
    simp only [eval_smul, ha, hbk, Int.natCast_mul, Int.mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c h
    simp only [intBin, OpRes.ok.injEq] at h
    subst h
    by_cases hlt : a * b < modulus t.bits
    · refine ⟨_, mem2 (Or.inl rfl), brcov_same (m := m) (sat_one ?_) (scoped_one (scoped_le0
        (scoped_addC _ (scoped_smul _ hsa)))) ?_ (Nat.mod_lt _ (modulus_pos _)) (scoped_smul _ hsa)⟩
      · rw [sat_le0, eval_addC, hp]; simp [Mw]; omega
      · rw [hp, mod_of_lt hlt]
    · refine ⟨_, mem2 (Or.inr rfl), ?_⟩
      have := brcov_fresh (m := m) (ρ := ρ) (nv := nv) (t := t)
        (sat_one (c := le0 ((Aff.c (Mw t.bits)).sub (ea.smul eb.k))) (by
          rw [sat_le0, eval_sub, hp]; simp [Mw]; omega))
        (scoped_one (scoped_le0 (scoped_sub (scoped_c _ _) (scoped_smul _ hsa))))
        (Nat.mod_lt (a * b) (modulus_pos t.bits))
      simpa using this
  · intro msg h; simp [intBin] at h
  · intro msg h; simp [intBin] at h
  · intro f h; simp [intBin] at h

theorem ub_zero_cover {ubs : List (List Cons)} (hmem : [le0 eb] ∈ ubs) (h0 : b = 0) :
    ∃ u ∈ ubs, Sat u ρ :=
  ⟨_, hmem, sat_one (by rw [sat_le0, hb, h0]; decide)⟩

theorem cover_udiv : BinCover m .udiv t ea eb nv [[le0 eb]]
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_
  · intro c h; simp only [intBin] at h; split at h
    · exact nomatch h
    · simp only [OpRes.ok.injEq] at h; subst h; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha'
  · intro msg h; simp only [intBin] at h; split at h
    · next h0 => exact ub_zero_cover ha hb ha' hb' hsa hsb (List.Mem.head _) (by simpa using h0)
    · exact nomatch h
  · intro msg h; simp only [intBin] at h; split at h <;> exact nomatch h
  · intro f h; simp only [intBin] at h; split at h <;> exact nomatch h

theorem cover_urem : BinCover m .urem t ea eb nv [[le0 eb]]
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_
  · intro c h; simp only [intBin] at h; split at h
    · exact nomatch h
    · simp only [OpRes.ok.injEq] at h; subst h; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
  · intro msg h; simp only [intBin] at h; split at h
    · next h0 => exact ub_zero_cover ha hb ha' hb' hsa hsb (List.Mem.head _) (by simpa using h0)
    · exact nomatch h
  · intro msg h; simp only [intBin] at h; split at h <;> exact nomatch h
  · intro f h; simp only [intBin] at h; split at h <;> exact nomatch h

theorem sdivUb_cover {ubs : List (List Cons)}
    (hmem : [leA ea (Aff.c (Hw t.bits)), leA (Aff.c (Hw t.bits)) ea,
             leA eb (Aff.c (Mw t.bits - 1)), leA (Aff.c (Mw t.bits - 1)) eb] ∈ ubs)
    (h1 : a = half t.bits) (h2 : b = modulus t.bits - 1) : ∃ u ∈ ubs, Sat u ρ := by
  refine ⟨_, hmem, ?_⟩
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  have hm := modulus_pos t.bits
  rcases hc with rfl | rfl | rfl | rfl <;> rw [sat_leA] <;> simp [Hw, Mw, ha, hb, h1, h2] <;> omega

theorem cover_sdiv : BinCover m .sdiv t ea eb nv
      [[le0 eb], [leA ea (Aff.c (Hw t.bits)), leA (Aff.c (Hw t.bits)) ea,
                  leA eb (Aff.c (Mw t.bits - 1)), leA (Aff.c (Mw t.bits - 1)) eb]]
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_
  · intro c h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · simp only [OpRes.ok.injEq] at h; subst h; split
        · exact negR_lt _ _
        · exact Nat.mod_lt _ (modulus_pos _)
  · intro msg h; simp only [intBin] at h; split at h
    · next h0 => exact ub_zero_cover ha hb ha' hb' hsa hsb (List.Mem.head _) (by simpa using h0)
    · split at h
      · next h0 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h0
        exact sdivUb_cover ha hb ha' hb' hsa hsb (List.Mem.tail _ (List.Mem.head _)) h0.1 h0.2
      · exact nomatch h
  · intro msg h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h <;> exact nomatch h
  · intro f h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h <;> exact nomatch h

theorem cover_srem : BinCover m .srem t ea eb nv
      [[le0 eb], [leA ea (Aff.c (Hw t.bits)), leA (Aff.c (Hw t.bits)) ea,
                  leA eb (Aff.c (Mw t.bits - 1)), leA (Aff.c (Mw t.bits - 1)) eb]]
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_
  · intro c h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h
      · exact nomatch h
      · simp only [OpRes.ok.injEq] at h; subst h; split
        · exact negR_lt _ _
        · exact Nat.mod_lt _ (modulus_pos _)
  · intro msg h; simp only [intBin] at h; split at h
    · next h0 => exact ub_zero_cover ha hb ha' hb' hsa hsb (List.Mem.head _) (by simpa using h0)
    · split at h
      · next h0 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h0
        exact sdivUb_cover ha hb ha' hb' hsa hsb (List.Mem.tail _ (List.Mem.head _)) h0.1 h0.2
      · exact nomatch h
  · intro msg h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h <;> exact nomatch h
  · intro f h; simp only [intBin] at h; split at h
    · exact nomatch h
    · split at h <;> exact nomatch h

theorem shiftUb_cover (h : t.bits ≤ b) : ∃ u ∈ [[leA (Aff.c (t.bits : Int)) eb]], Sat u ρ :=
  ⟨_, List.Mem.head _, sat_one (by rw [sat_leA]; simp [hb]; omega)⟩

/-- The `Bool`-on-integer operations `bAnd`, `bOr`, `bXor`: opaque results. -/
theorem cover_bitwise {op : BinOp} (hop : op = .bAnd ∨ op = .bOr ∨ op = .bXor) :
    BinCover m op t ea eb nv []
      [⟨rangeCs t.bits (Aff.v nv), [.int t (Aff.v nv)], nv + 1⟩] ρ a b := by
  have h2 := two_le_modulus (bits_pos t)
  refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_ <;>
    rcases hop with rfl | rfl | rfl <;> simp only [intBin] <;> intro x h
  all_goals first
    | (simp only [OpRes.ok.injEq] at h; subst h; first
        | exact Nat.mod_lt _ (modulus_pos _)
        | (split <;> omega))
    | exact nomatch h

end

/-! ## VF7: the bit-level encodings cover SemR's operators -/

/-- A one-value branch covers `c` at an assignment `ρ'` agreeing below `nv`. -/
theorem brcov_one {ρ ρ' : Nat → Int} {nv n' : Nat} {cs : List Cons} {t : IntTy} {e : Aff} {c : Nat}
    (hag : Agree ρ ρ' nv) (hsat : Sat cs ρ') (hle : nv ≤ n') (hsc : CsScoped n' cs)
    (he : e.eval ρ' = c) (hc : c < modulus t.bits) (hs : e.Scoped n') :
    BrCovers m ρ nv ⟨cs, [.int t e], n'⟩ [.int t c] := by
  refine ⟨ρ', hag, hsat, hle, hsc, rfl, ?_, ?_⟩
  · intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; exact ⟨c, rfl, hc, he⟩
  · intro s hs'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
    subst hs'; exact hs

theorem log2Of_sound {w : Nat} {c : Int} {j : Nat} (h : log2Of w c = some j) :
    j < w ∧ (((2 ^ j : Nat) : Int)) = c := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.mp h2, intEqb_eq h1⟩

theorem fixedAt_sound {w : Nat} {cs : List Cons} {eb : Aff} : ∀ {ds : List Cons} {j : Nat},
    fixedAt w cs eb ds = some j →
      ∃ j' : Int, j = j'.toNat ∧ 0 ≤ j' ∧ memC (leA eb (Aff.c j')) cs = true ∧
        memC (leA (Aff.c j') eb) cs = true
  | [], _, h => nomatch h
  | d :: ds, j, h => by
    simp only [fixedAt] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      refine ⟨_, rfl, ?_, hc.1.2, hc.2⟩
      have := hc.1.1.1.2
      cases hj : d.bound + eb.k with
      | ofNat n => exact Int.natCast_nonneg n
      | negSucc n => rw [hj] at this; exact nomatch this
    · exact fixedAt_sound h

/-- The concrete in-range amount is among the forked ones. -/
theorem amounts_mem {w : Nat} {cs : List Cons} {eb : Aff} {ρ : Nat → Int} {b : Nat}
    (hsat : Sat cs ρ) (hb : eb.eval ρ = (b : Int)) (hbw : b < w) : b ∈ amounts w cs eb := by
  unfold amounts
  split
  · next hk =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
    have := eval_isConst eb ρ hk.1.1
    rw [hb] at this
    simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  · split
    · next j hj =>
      obtain ⟨j', rfl, hj0, h1, h2⟩ := fixedAt_sound hj
      have c1 := sat_mem hsat h1
      have c2 := sat_mem hsat h2
      rw [sat_leA] at c1 c2
      simp only [eval_c, hb] at c1 c2
      simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
    · exact List.mem_range.mpr hbw

section
variable {t : IntTy} {ea eb : Aff} {nv : Nat} {ρ : Nat → Int} {a b : Nat} {cs : List Cons}
  (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
  (ha' : a < modulus t.bits) (hb' : b < modulus t.bits)
  (hsa : ea.Scoped nv) (hsb : eb.Scoped nv) (hsat : Sat cs ρ) (hcs : CsScoped nv cs)
include ha hb ha' hb' hsa hsb hsat hcs

/-- The branch of a bit-by-bit operation covers `OP a b`. -/
theorem bitwise_covers {f : BT → BT → Nat → List Cons × BT × Nat} {g : Nat → Nat → Nat}
    {OP : Nat → Nat → Nat} (hf : BitOpOK f g) (h0 : OP 0 0 = 0)
    (hop : ∀ r s a b, r < 2 → s < 2 → OP (r + 2 * a) (s + 2 * b) = g r s + 2 * OP a b) :
    BrCovers m ρ nv (bitwiseBr t f ea eb nv cs) [.int t (OP a b % modulus t.bits)] := by
  obtain ⟨ρ1, ag1, sat1, le1, sc1, hl1, hb1, hs1⟩ :=
    getBits_sound (w := t.bits) hsat hcs ha ha' hsa
  have hsat1 : Sat cs ρ1 := Sat.congr hcs ag1 hsat
  have hb1' : eb.eval ρ1 = b := (eval_congr hsb ag1).symm.trans hb
  obtain ⟨ρ2, ag2, sat2, le2, sc2, hl2, hb2, hs2⟩ :=
    getBits_sound (w := t.bits) hsat1 (hcs.mono le1) hb1' hb' (hsb.mono le1)
  obtain ⟨ρ3, ag3, sat3, bits3, le3, sc3, scs3, len3⟩ := zipBits_sound hf h0 hop _ _ _ ρ2 a b
    (hl1.trans hl2.symm) (bitsOf_congr hs1 ag2 hb1) hb2 (hs1.mono le2) hs2
  have hlt : OP a b < modulus t.bits := by
    have := bitsOf_lt bits3; rw [len3, hl1] at this; exact this
  rw [Nat.mod_eq_of_lt hlt]
  simp only [bitwiseBr]
  refine brcov_one (ag1.trans ((ag2.mono le1).trans (ag3.mono (Nat.le_trans le1 le2))))
    ?_ (Nat.le_trans le1 (Nat.le_trans le2 le3)) ?_ bits3.2 hlt (scoped_bitSum scs3)
  · refine Sat.append (Sat.append ?_ ?_) sat3
    · exact Sat.congr sc1 (ag2.trans (ag3.mono le2)) sat1
    · exact Sat.congr sc2 ag3 sat2
  · refine CsScoped.append (CsScoped.append ?_ ?_) sc3
    · exact sc1.mono (Nat.le_trans le2 le3)
    · exact sc2.mono le3

/-- The branch of an amount `b < w` covers the move `V w a b`. -/
theorem shift_covers {f : Nat → List BT → List BT} {V : Nat → Nat → Nat → Nat} (hmv : MoveOK f V)
    (hbw : b < t.bits) :
    ∃ br ∈ shiftBrs t f eb cs (getBits t.bits cs ea nv), BrCovers m ρ nv br [.int t (V t.bits a b)] := by
  refine ⟨_, List.mem_map.mpr ⟨b, amounts_mem hsat hb hbw, rfl⟩, ?_⟩
  obtain ⟨ρ1, ag1, sat1, le1, sc1, hr⟩ := getBits_sound (w := t.bits) hsat hcs ha ha' hsa
  obtain ⟨hv, hsv, hlt⟩ := hmv _ _ _ _ _ _ hr hbw
  have hb1 : eb.eval ρ1 = b := (eval_congr hsb ag1).symm.trans hb
  refine brcov_one ag1 ?_ le1 ?_ hv.2 hlt (scoped_bitSum hsv)
  · refine Sat.append sat1 ?_
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl <;> rw [sat_leA] <;> simp [hb1]
  · refine CsScoped.append sc1 ?_
    intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · exact scoped_leA (hsb.mono le1) (scoped_c _ _)
    · exact scoped_leA (scoped_c _ _) (hsb.mono le1)

end

/-- The branch of a move of `e`'s `w` bits covers `v`. -/
theorem bitsBr_covers {w : Nat} {t' : IntTy} {fl : List BT → List BT} {e : Aff} {nv : Nat}
    {ρ : Nat → Int} {cs : List Cons} {a v : Nat} (hsat : Sat cs ρ) (hcs : CsScoped nv cs)
    (he : e.eval ρ = a) (ha : a < 2 ^ w) (hs : e.Scoped nv)
    (hf : ∀ (ρ : Nat → Int) (n : Nat) (xs : List BT), BitsRead w ρ n xs a →
      BitsOf ρ (fl xs) v ∧ BTsScoped n (fl xs)) (hv : v < modulus t'.bits) :
    BrCovers m ρ nv (bitsBr w t' fl e nv cs) [.int t' v] := by
  obtain ⟨ρ1, ag1, sat1, le1, sc1, hr⟩ := getBits_sound (w := w) hsat hcs he ha hs
  obtain ⟨h1, h2⟩ := hf _ _ _ hr
  exact brcov_one ag1 sat1 le1 sc1 h1.2 hv (scoped_bitSum h2)

theorem intBin_shift_ok {op : BinOp} {w a b c : Nat} {V : Nat}
    (hdef : intBin op w a b = if w ≤ b then .ub "shift amount out of range" else .ok V)
    (h : intBin op w a b = .ok c) : b < w ∧ c = V := by
  rw [hdef] at h; split at h
  · exact nomatch h
  · next hb => simp only [OpRes.ok.injEq] at h; exact ⟨by omega, h.symm⟩

theorem binCases_sound {op : BinOp} {t : IntTy} {ea eb : Aff} {nv : Nat} {cs : List Cons}
    {ubs : List (List Cons)} {bs : List Br} {ρ : Nat → Int} {a b : Nat}
    (hc : binCases op t ea eb nv cs = some (ubs, bs))
    (ha : ea.eval ρ = (a : Int)) (hb : eb.eval ρ = (b : Int))
    (ha' : a < modulus t.bits) (hb' : b < modulus t.bits)
    (hsa : ea.Scoped nv) (hsb : eb.Scoped nv) (hsat : Sat cs ρ) (hcs : CsScoped nv cs) :
    BinCover m op t ea eb nv ubs bs ρ a b := by
  have H := fun {op : BinOp} (hop : op = .bAnd ∨ op = .bOr ∨ op = .bXor) =>
    cover_bitwise (m := m) (op := op) ha hb ha' hb' hsa hsb hop
  have hnoerr : ∀ (op : BinOp), (op = .shl ∨ op = .lshr ∨ op = .ashr) →
      (∀ msg, intBin op t.bits a b ≠ .tyErr msg) ∧ (∀ f, intBin op t.bits a b ≠ .unsup f) := by
    intro op hop
    rcases hop with rfl | rfl | rfl <;>
      exact ⟨fun msg h => by (simp only [intBin] at h; split at h <;> exact (nomatch h)),
             fun f h => by (simp only [intBin] at h; split at h <;> exact (nomatch h))⟩
  have hub : ∀ (op : BinOp), (op = .shl ∨ op = .lshr ∨ op = .ashr) →
      ∀ msg, intBin op t.bits a b = .ub msg → ∃ u ∈ [[leA (Aff.c (t.bits : Int)) eb]], Sat u ρ := by
    intro op hop msg h
    rcases hop with rfl | rfl | rfl <;> (simp only [intBin] at h; split at h) <;>
      (rename_i h0; first | exact shiftUb_cover ha hb ha' hb' hsa hsb h0 | cases h)
  have hbitw : ∀ (op : BinOp) (OP : Nat → Nat → Nat), (intBin op t.bits a b = .ok (OP a b % modulus t.bits)) →
      ∀ br, BrCovers m ρ nv br [.int t (OP a b % modulus t.bits)] →
      BinCover m op t ea eb nv [] [br] ρ a b := by
    intro op OP hi br hbr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c h; rw [hi] at h; simp only [OpRes.ok.injEq] at h; subst h; exact ⟨br, List.Mem.head _, hbr⟩
    · intro msg h; rw [hi] at h; exact nomatch h
    · intro msg h; rw [hi] at h; exact nomatch h
    · intro f h; rw [hi] at h; exact nomatch h
  cases op <;> simp only [binCases, Option.some.injEq, Prod.mk.injEq] at hc
  case rotl => exact nomatch hc
  case rotr => exact nomatch hc
  case mul =>
    split at hc
    · next hk =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact cover_mul_const ha hb ha' hb' hsa hsb hk
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      refine cover_fresh_ok ha hb ha' hb' hsa hsb ?_ ?_ ?_ ?_ <;> simp only [intBin] <;> intro x h
      · simp only [OpRes.ok.injEq] at h; subst h; exact Nat.mod_lt _ (modulus_pos _)
      all_goals exact nomatch h
  case udiv =>
    split at hc
    · next j hj =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      split at hj
      · next hk =>
        obtain ⟨hjw, h2⟩ := log2Of_sound hj
        have hbk : (b : Int) = eb.k := by rw [← hb]; exact eval_isConst eb ρ hk
        have hb2 : b = 2 ^ j := by omega
        have hok : intBin .udiv t.bits a b = .ok (a / 2 ^ j) := by
          simp only [intBin, hb2]; simp [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos j)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c h; rw [hok] at h; simp only [OpRes.ok.injEq] at h; subst h
          refine ⟨_, List.Mem.head _, bitsBr_covers hsat hcs ha ha' hsa ?_ ?_⟩
          · intro ρ' n xs hr; obtain ⟨h1, h2, _⟩ := lshr_ok _ _ _ _ _ _ hr hjw; exact ⟨h1, h2⟩
          · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha'
        · intro msg h; rw [hok] at h; exact nomatch h
        · intro msg h; rw [hok] at h; exact nomatch h
        · intro f h; rw [hok] at h; exact nomatch h
      · exact nomatch hj
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact cover_udiv ha hb ha' hb' hsa hsb
  case urem =>
    split at hc
    · next j hj =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      split at hj
      · next hk =>
        obtain ⟨hjw, h2⟩ := log2Of_sound hj
        have hbk : (b : Int) = eb.k := by rw [← hb]; exact eval_isConst eb ρ hk
        have hb2 : b = 2 ^ j := by omega
        have hok : intBin .urem t.bits a b = .ok (a % 2 ^ j) := by
          simp only [intBin, hb2]; simp [Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos j)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c h; rw [hok] at h; simp only [OpRes.ok.injEq] at h; subst h
          refine ⟨_, List.Mem.head _, bitsBr_covers hsat hcs ha ha' hsa ?_ ?_⟩
          · intro ρ' n xs hr; obtain ⟨h1, h2, _⟩ := mask_ok _ _ _ _ _ _ hr hjw; exact ⟨h1, h2⟩
          · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha'
        · intro msg h; rw [hok] at h; exact nomatch h
        · intro msg h; rw [hok] at h; exact nomatch h
        · intro f h; rw [hok] at h; exact nomatch h
      · exact nomatch hj
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact cover_urem ha hb ha' hb' hsa hsb
  all_goals (obtain ⟨rfl, rfl⟩ := hc)
  case add => exact cover_add ha hb ha' hb' hsa hsb
  case sub => exact cover_sub ha hb ha' hb' hsa hsb
  case sdiv => exact cover_sdiv ha hb ha' hb' hsa hsb
  case srem => exact cover_srem ha hb ha' hb' hsa hsb
  case shl =>
    refine ⟨?_, hub .shl (by simp), (hnoerr .shl (by simp)).1, (hnoerr .shl (by simp)).2⟩
    intro c h
    obtain ⟨hbw, rfl⟩ := intBin_shift_ok (V := (a * 2 ^ b) % modulus t.bits) (by simp [intBin]) h
    exact shift_covers ha hb ha' hb' hsa hsb hsat hcs shl_ok hbw
  case lshr =>
    refine ⟨?_, hub .lshr (by simp), (hnoerr .lshr (by simp)).1, (hnoerr .lshr (by simp)).2⟩
    intro c h
    obtain ⟨hbw, rfl⟩ := intBin_shift_ok (V := a / 2 ^ b) (by simp [intBin]) h
    exact shift_covers ha hb ha' hb' hsa hsb hsat hcs lshr_ok hbw
  case ashr =>
    refine ⟨?_, hub .ashr (by simp), (hnoerr .ashr (by simp)).1, (hnoerr .ashr (by simp)).2⟩
    intro c h
    obtain ⟨hbw, rfl⟩ := intBin_shift_ok
      (V := a / 2 ^ b + (if isNeg t.bits a = true then modulus t.bits - 2 ^ (t.bits - b) else 0))
      (by simp [intBin]) h
    exact shift_covers ha hb ha' hb' hsa hsb hsat hcs ashr_ok hbw
  case and =>
    exact hbitw .and Nat.land (by simp [intBin]) _
      (bitwise_covers ha hb ha' hb' hsa hsb hsat hcs andBit_ok rfl land_step)
  case or =>
    exact hbitw .or Nat.lor (by simp [intBin]) _
      (bitwise_covers ha hb ha' hb' hsa hsb hsat hcs orBit_ok rfl lor_step)
  case xor =>
    exact hbitw .xor Nat.xor (by simp [intBin]) _
      (bitwise_covers ha hb ha' hb' hsa hsb hsat hcs xorBit_ok rfl xor_step)
  case bAnd => exact H (by simp)
  case bOr => exact H (by simp)
  case bXor => exact H (by simp)

end VF5
