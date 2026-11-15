/-
  VF7Bits — the bit-level reading of integers is sound: every bit term
  `getBits` returns is `0` or `1` at the assignment the cover builds and the
  bits sum to the value; the bit operations (`andBit`, `orBit`, `xorBit`,
  `zipBits`) compute SemR's `&&&`, `|||`, `^^^` on such sums; moving the bits
  (`shlBits`, `lshrBits`, `ashrBits`, `maskBits`, `List.take`) computes SemR's
  shifts, masks and narrowing casts (VF7's first slice; Clean `docs/DECISIONS.md`
  R206).

  Copyright 2026 Andrew Yates. Licensed under the Apache License, Version 2.0.
  Author: Andrew Yates <andrewyates.name@gmail.com>
-/
import VF5Ops

set_option linter.unusedVariables false

namespace VF5

open SemR

/-! ## Bits, their sums, their scope -/

/-- A bit term's value is `0` or `1`. -/
def B01 (ρ : Nat → Int) (b : BT) : Prop := b.aff.eval ρ = 0 ∨ b.aff.eval ρ = 1

/-- `bs` are bits (each `0` or `1`) summing to `a`. -/
def BitsOf (ρ : Nat → Int) (bs : List BT) (a : Nat) : Prop :=
  (∀ b ∈ bs, B01 ρ b) ∧ (bitSum bs).eval ρ = (a : Int)

def BTsScoped (n : Nat) (bs : List BT) : Prop := ∀ b ∈ bs, b.aff.Scoped n

@[simp] theorem eval_bitSum_nil (ρ : Nat → Int) : (bitSum []).eval ρ = 0 := by simp [bitSum]

@[simp] theorem eval_bitSum_cons (b : BT) (bs : List BT) (ρ : Nat → Int) :
    (bitSum (b :: bs)).eval ρ = b.aff.eval ρ + 2 * (bitSum bs).eval ρ := by
  simp [bitSum]

theorem two_pow_succ_int (n : Nat) : (2 : Int) ^ (n + 1) = 2 * 2 ^ n := by
  rw [Int.pow_succ, Int.mul_comm]

theorem eval_bitSum_append (xs ys : List BT) (ρ : Nat → Int) :
    (bitSum (xs ++ ys)).eval ρ = (bitSum xs).eval ρ + 2 ^ xs.length * (bitSum ys).eval ρ := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, eval_bitSum_cons, ih, List.length_cons, two_pow_succ_int]
    rw [Int.mul_add, Int.mul_assoc]
    omega

theorem B01.nat {ρ : Nat → Int} {b : BT} (h : B01 ρ b) : ∃ r : Nat, b.aff.eval ρ = (r : Int) ∧ r < 2 := by
  rcases h with h | h
  · exact ⟨0, by simp [h], by decide⟩
  · exact ⟨1, by simp [h], by decide⟩

theorem bitSum_range : ∀ (bs : List BT) (ρ : Nat → Int), (∀ b ∈ bs, B01 ρ b) →
    0 ≤ (bitSum bs).eval ρ ∧ (bitSum bs).eval ρ < 2 ^ bs.length
  | [], ρ, _ => by simp
  | b :: bs, ρ, h => by
    have hb := h b (List.Mem.head _)
    have ih := bitSum_range bs ρ (fun x hx => h x (List.Mem.tail _ hx))
    simp only [eval_bitSum_cons, List.length_cons, two_pow_succ_int]
    rcases hb with h0 | h0 <;> rw [h0] <;> omega

theorem bitsOf_lt {ρ : Nat → Int} {bs : List BT} {a : Nat} (h : BitsOf ρ bs a) : a < 2 ^ bs.length := by
  have := (bitSum_range bs ρ h.1).2
  rw [h.2] at this
  have h2 : ((2 ^ bs.length : Nat) : Int) = (2 : Int) ^ bs.length := Int.natCast_pow 2 _
  omega

theorem toNat_eq {x : Int} (h : 0 ≤ x) : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg h

/-- A sum of bits is a natural number. -/
theorem bits_nat {ρ : Nat → Int} {bs : List BT} (h : ∀ b ∈ bs, B01 ρ b) :
    ∃ a : Nat, BitsOf ρ bs a :=
  ⟨((bitSum bs).eval ρ).toNat, h, (toNat_eq (bitSum_range bs ρ h).1).symm⟩

theorem bitsOf_append {ρ : Nat → Int} {xs ys : List BT} {a : Nat} (h : BitsOf ρ (xs ++ ys) a) :
    BitsOf ρ xs (a % 2 ^ xs.length) ∧ BitsOf ρ ys (a / 2 ^ xs.length) := by
  have hx : ∀ b ∈ xs, B01 ρ b := fun b hb => h.1 b (List.mem_append_left _ hb)
  have hy : ∀ b ∈ ys, B01 ρ b := fun b hb => h.1 b (List.mem_append_right _ hb)
  obtain ⟨T, hT⟩ := bits_nat hx
  obtain ⟨D, hD⟩ := bits_nat hy
  have hTl := bitsOf_lt hT
  have he := h.2
  have hp2 : ((2 ^ xs.length : Nat) : Int) = (2 : Int) ^ xs.length := Int.natCast_pow 2 _
  rw [eval_bitSum_append, hT.2, hD.2, ← hp2] at he
  have ha : a = T + 2 ^ xs.length * D := by exact_mod_cast he.symm
  have hp : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  refine ⟨⟨hx, ?_⟩, ⟨hy, ?_⟩⟩
  · rw [ha, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hTl]; exact hT.2
  · rw [ha, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hTl, Nat.zero_add]; exact hD.2

theorem bitsOf_take_drop {ρ : Nat → Int} {xs : List BT} {a j : Nat} (h : BitsOf ρ xs a)
    (hj : j ≤ xs.length) :
    BitsOf ρ (xs.take j) (a % 2 ^ j) ∧ BitsOf ρ (xs.drop j) (a / 2 ^ j) := by
  have h' : BitsOf ρ (xs.take j ++ xs.drop j) a := by rw [List.take_append_drop]; exact h
  have hl : (xs.take j).length = j := by rw [List.length_take]; omega
  have := bitsOf_append h'
  rw [hl] at this
  exact this

@[simp] theorem eval_k (b : Bool) (ρ : Nat → Int) : (BT.k b).aff.eval ρ = if b then 1 else 0 := by
  cases b <;> simp [BT.aff]

theorem bitsOf_zeros (ρ : Nat → Int) : ∀ j : Nat, BitsOf ρ (List.replicate j (.k false)) 0
  | 0 => by constructor <;> simp
  | j + 1 => by
    obtain ⟨h1, h2⟩ := bitsOf_zeros ρ j
    constructor
    · intro b hb
      rw [List.mem_replicate] at hb
      rw [hb.2]; left; simp
    · rw [List.replicate_succ, eval_bitSum_cons, h2]; simp

theorem eval_bitSum_replicate {ρ : Nat → Int} {b : BT} (hb : B01 ρ b) :
    ∀ j : Nat, (bitSum (List.replicate j b)).eval ρ = b.aff.eval ρ * (2 ^ j - 1)
  | 0 => by simp
  | j + 1 => by
    rw [List.replicate_succ, eval_bitSum_cons, eval_bitSum_replicate hb j, two_pow_succ_int]
    rcases hb with h | h <;> rw [h] <;> omega

theorem b01_replicate {ρ : Nat → Int} {b : BT} (hb : B01 ρ b) (j : Nat) :
    ∀ x ∈ List.replicate j b, B01 ρ x := by
  intro x hx; rw [List.mem_replicate] at hx; rw [hx.2]; exact hb

/-! ## Scope -/

theorem scoped_bitSum : ∀ {n : Nat} {bs : List BT}, BTsScoped n bs → (bitSum bs).Scoped n
  | n, [], _ => scoped_c n 0
  | n, b :: bs, h => by
    simp only [bitSum]
    exact scoped_add (h b (List.Mem.head _))
      (scoped_smul _ (scoped_bitSum (fun x hx => h x (List.Mem.tail _ hx))))

theorem BTsScoped.mono {n n' : Nat} {bs : List BT} (h : BTsScoped n bs) (hn : n ≤ n') :
    BTsScoped n' bs := fun b hb => (h b hb).mono hn

theorem bitsOf_congr {ρ ρ' : Nat → Int} {n : Nat} {bs : List BT} {a : Nat} (hs : BTsScoped n bs)
    (hag : Agree ρ ρ' n) (h : BitsOf ρ bs a) : BitsOf ρ' bs a := by
  refine ⟨?_, ?_⟩
  · intro b hb
    have := eval_congr (hs b hb) hag
    rcases h.1 b hb with h0 | h0
    · left; rw [← this]; exact h0
    · right; rw [← this]; exact h0
  · rw [← eval_congr (scoped_bitSum hs) hag]; exact h.2

theorem scoped_k (n : Nat) (b : Bool) : (BT.k b).aff.Scoped n := by
  cases b <;> exact scoped_c n _

/-! ## One bit operation -/

theorem kv_some {x : BT} {b : Bool} (h : x.kv = some b) : x = .k b := by
  cases x <;> simp [BT.kv] at h; subst h; rfl

theorem eval_flip (x : BT) (ρ : Nat → Int) : x.flip.aff.eval ρ = 1 - x.aff.eval ρ := by
  cases x with
  | k b => cases b <;> simp [BT.flip, BT.aff]
  | v j => simp [BT.flip, BT.aff]
  | n j => simp [BT.flip, BT.aff]; omega

theorem scoped_flip {n : Nat} {x : BT} (h : x.aff.Scoped n) : x.flip.aff.Scoped n := by
  cases x with
  | k b => exact scoped_k n _
  | v j => exact scoped_sub (scoped_c _ _) h
  | n j =>
    simp only [BT.flip, BT.aff]
    simp only [BT.aff, Aff.Scoped, Aff.sub, Aff.add, Aff.smul, Aff.c, length_addVec,
      length_scale] at h ⊢
    omega

/-- What one bit operation guarantees: for bits `x`, `y` of values `r`, `s`,
    the result bit has value `g r s` at an assignment that agrees below `nv`
    and meets the operation's constraints. -/
def BitOpOK (f : BT → BT → Nat → List Cons × BT × Nat) (g : Nat → Nat → Nat) : Prop :=
  ∀ (x y : BT) (nv : Nat) (ρ : Nat → Int) (r s : Nat), x.aff.eval ρ = r → y.aff.eval ρ = s →
    r < 2 → s < 2 → x.aff.Scoped nv → y.aff.Scoped nv →
    ∃ ρ', Agree ρ ρ' nv ∧ Sat (f x y nv).1 ρ' ∧ (f x y nv).2.1.aff.eval ρ' = (g r s : Int) ∧
      g r s < 2 ∧ nv ≤ (f x y nv).2.2 ∧ CsScoped (f x y nv).2.2 (f x y nv).1 ∧
      (f x y nv).2.1.aff.Scoped (f x y nv).2.2

theorem zBit_ok {c : Aff → List Cons} {nv : Nat} {ρ : Nat → Int} {z : Nat} (hz : z < 2)
    (hc : Sat (c (Aff.v nv)) (upd ρ nv z)) (hsc : CsScoped (nv + 1) (c (Aff.v nv))) :
    ∃ ρ', Agree ρ ρ' nv ∧ Sat (zBit c nv).1 ρ' ∧ (zBit c nv).2.1.aff.eval ρ' = (z : Int) ∧
      nv ≤ (zBit c nv).2.2 ∧ CsScoped (zBit c nv).2.2 (zBit c nv).1 ∧
      (zBit c nv).2.1.aff.Scoped (zBit c nv).2.2 := by
  simp only [zBit]
  refine ⟨upd ρ nv z, agree_upd ρ nv z, ?_, by simp [zBit, BT.aff], Nat.le_succ _, ?_,
    scoped_v (by omega)⟩
  · refine Sat.append hc ?_
    intro d hd
    simp only [bitCs, rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl <;> rw [sat_le0] <;> simp [Mw, modulus] <;> omega
  · refine CsScoped.append hsc ?_
    intro d hd
    simp only [bitCs, rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · exact scoped_le0 (scoped_smul _ (scoped_v (by omega)))
    · exact scoped_le0 (scoped_addC _ (scoped_v (by omega)))

theorem same_ok {x : BT} {nv : Nat} {ρ : Nat → Int} {v : Nat} (he : x.aff.eval ρ = (v : Int))
    (hs : x.aff.Scoped nv) :
    ∃ ρ', Agree ρ ρ' nv ∧ Sat ([] : List Cons) ρ' ∧ x.aff.eval ρ' = (v : Int) ∧
      nv ≤ nv ∧ CsScoped nv ([] : List Cons) ∧ x.aff.Scoped nv :=
  ⟨ρ, Agree.refl ρ nv, sat_nil ρ, he, Nat.le_refl _, (fun _ h => nomatch h), hs⟩

theorem sat_of_list {cs : List Cons} {ρ : Nat → Int} (h : ∀ c ∈ cs, c.sat ρ) : Sat cs ρ := h

theorem scoped_of_list {n : Nat} {cs : List Cons} (h : ∀ c ∈ cs, Cons.Scoped n c) : CsScoped n cs := h

theorem andBit_ok : BitOpOK andBit (fun r s => r * s) := by
  intro x y nv ρ r s hx hy hr hs hsx hsy
  have hrs : r * s < 2 := by rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  cases hkx : x.kv with
  | some bx =>
    have := kv_some hkx; subst this
    cases bx
    · simp only [andBit, hkx]
      have hr0 : r = 0 := by simp at hx; omega
      subst hr0
      refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp, hrs, Nat.le_refl _, (fun _ h => nomatch h),
        scoped_k _ _⟩
    · simp only [andBit, hkx]
      have hr1 : r = 1 := by simp at hx; omega
      subst hr1
      exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp [hy], hrs, Nat.le_refl _, (fun _ h => nomatch h), hsy⟩
  | none =>
    cases hky : y.kv with
    | some byy =>
      have := kv_some hky; subst this
      cases byy
      · simp only [andBit, hkx, hky]
        have hs0 : s = 0 := by simp at hy; omega
        subst hs0
        refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp, hrs, Nat.le_refl _, (fun _ h => nomatch h),
          scoped_k _ _⟩
      · simp only [andBit, hkx, hky]
        have hs1 : s = 1 := by simp at hy; omega
        subst hs1
        exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp [hx], hrs, Nat.le_refl _, (fun _ h => nomatch h), hsx⟩
    | none =>
      simp only [andBit, hkx, hky]
      have hx' : x.aff.eval (upd ρ nv (r * s : Nat)) = r := (eval_congr hsx (agree_upd ρ nv _)).symm.trans hx
      have hy' : y.aff.eval (upd ρ nv (r * s : Nat)) = s := (eval_congr hsy (agree_upd ρ nv _)).symm.trans hy
      obtain ⟨ρ', h1, h2, h3, h4, h5, h6⟩ := zBit_ok (c := fun z => [leA z x.aff, leA z y.aff,
          leAn (x.aff.add y.aff) (-1) z]) (nv := nv) (ρ := ρ) hrs
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
          rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
          rcases hd with rfl | rfl | rfl <;>
          simp only [sat_leA, sat_leAn, eval_add, eval_v, upd_self, hx', hy'] <;> decide)
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          have hv : (Aff.v nv).Scoped (nv + 1) := scoped_v (by omega)
          have hx1 := hsx.mono (Nat.le_succ nv)
          have hy1 := hsy.mono (Nat.le_succ nv)
          rcases hd with rfl | rfl | rfl
          · exact scoped_leA hv hx1
          · exact scoped_leA hv hy1
          · exact scoped_leAn _ (scoped_add hx1 hy1) hv)
      exact ⟨ρ', h1, h2, h3, hrs, h4, h5, h6⟩

theorem orBit_ok : BitOpOK orBit (fun r s => r + s - r * s) := by
  intro x y nv ρ r s hx hy hr hs hsx hsy
  have hrs : r + s - r * s < 2 := by rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  cases hkx : x.kv with
  | some bx =>
    have := kv_some hkx; subst this
    cases bx
    · simp only [orBit, hkx]
      have hr0 : r = 0 := by simp at hx; omega
      subst hr0
      exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp [hy], hrs, Nat.le_refl _, (fun _ h => nomatch h), hsy⟩
    · simp only [orBit, hkx]
      have hr1 : r = 1 := by simp at hx; omega
      subst hr1
      refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h), scoped_k _ _⟩
      simp
  | none =>
    cases hky : y.kv with
    | some byy =>
      have := kv_some hky; subst this
      cases byy
      · simp only [orBit, hkx, hky]
        have hs0 : s = 0 := by simp at hy; omega
        subst hs0
        exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, by simp [hx], hrs, Nat.le_refl _, (fun _ h => nomatch h), hsx⟩
      · simp only [orBit, hkx, hky]
        have hs1 : s = 1 := by simp at hy; omega
        subst hs1
        refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h), scoped_k _ _⟩
        simp
    | none =>
      simp only [orBit, hkx, hky]
      have hx' : x.aff.eval (upd ρ nv ((r + s - r * s : Nat) : Int)) = r :=
        (eval_congr hsx (agree_upd ρ nv _)).symm.trans hx
      have hy' : y.aff.eval (upd ρ nv ((r + s - r * s : Nat) : Int)) = s :=
        (eval_congr hsy (agree_upd ρ nv _)).symm.trans hy
      obtain ⟨ρ', h1, h2, h3, h4, h5, h6⟩ := zBit_ok (c := fun z => [leA x.aff z, leA y.aff z,
          leA z (x.aff.add y.aff)]) (nv := nv) (ρ := ρ) hrs
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
          rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
          rcases hd with rfl | rfl | rfl <;>
          simp only [sat_leA, eval_add, eval_v, upd_self, hx', hy'] <;> decide)
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          have hv : (Aff.v nv).Scoped (nv + 1) := scoped_v (by omega)
          have hx1 := hsx.mono (Nat.le_succ nv)
          have hy1 := hsy.mono (Nat.le_succ nv)
          rcases hd with rfl | rfl | rfl
          · exact scoped_leA hx1 hv
          · exact scoped_leA hy1 hv
          · exact scoped_leA hv (scoped_add hx1 hy1))
      exact ⟨ρ', h1, h2, h3, hrs, h4, h5, h6⟩

theorem xorBit_ok : BitOpOK xorBit (fun r s => r + s - 2 * (r * s)) := by
  intro x y nv ρ r s hx hy hr hs hsx hsy
  have hrs : r + s - 2 * (r * s) < 2 := by rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  cases hkx : x.kv with
  | some bx =>
    have := kv_some hkx; subst this
    cases bx
    · simp only [xorBit, hkx]
      have hr0 : r = 0 := by simp at hx; omega
      subst hr0
      refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h), hsy⟩
      simp [hy]
    · simp only [xorBit, hkx]
      have hr1 : r = 1 := by simp at hx; omega
      subst hr1
      refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h),
        scoped_flip hsy⟩
      simp only [if_true, eval_flip, hy]; omega
  | none =>
    cases hky : y.kv with
    | some byy =>
      have := kv_some hky; subst this
      cases byy
      · simp only [xorBit, hkx, hky]
        have hs0 : s = 0 := by simp at hy; omega
        subst hs0
        refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h), hsx⟩
        simp [hx]
      · simp only [xorBit, hkx, hky]
        have hs1 : s = 1 := by simp at hy; omega
        subst hs1
        refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, hrs, Nat.le_refl _, (fun _ h => nomatch h),
          scoped_flip hsx⟩
        simp only [if_true, eval_flip, hx]; omega
    | none =>
      simp only [xorBit, hkx, hky]
      have hx' : x.aff.eval (upd ρ nv ((r + s - 2 * (r * s) : Nat) : Int)) = r :=
        (eval_congr hsx (agree_upd ρ nv _)).symm.trans hx
      have hy' : y.aff.eval (upd ρ nv ((r + s - 2 * (r * s) : Nat) : Int)) = s :=
        (eval_congr hsy (agree_upd ρ nv _)).symm.trans hy
      obtain ⟨ρ', h1, h2, h3, h4, h5, h6⟩ := zBit_ok (c := fun z => [leA z (x.aff.add y.aff),
          leA (x.aff.sub y.aff) z, leA (y.aff.sub x.aff) z, leA (z.add (x.aff.add y.aff)) (Aff.c 2)])
          (nv := nv) (ρ := ρ) hrs
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
          rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
          rcases hd with rfl | rfl | rfl | rfl <;>
          simp only [sat_leA, eval_add, eval_sub, eval_c, eval_v, upd_self, hx', hy'] <;> decide)
        (by
          intro d hd
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
          have hv : (Aff.v nv).Scoped (nv + 1) := scoped_v (by omega)
          have hx1 := hsx.mono (Nat.le_succ nv)
          have hy1 := hsy.mono (Nat.le_succ nv)
          rcases hd with rfl | rfl | rfl | rfl
          · exact scoped_leA hv (scoped_add hx1 hy1)
          · exact scoped_leA (scoped_sub hx1 hy1) hv
          · exact scoped_leA (scoped_sub hy1 hx1) hv
          · exact scoped_leA (scoped_add hv (scoped_add hx1 hy1)) (scoped_c _ _))
      exact ⟨ρ', h1, h2, h3, hrs, h4, h5, h6⟩

/-! ## A bit operation on whole values -/

theorem half_add (r a : Nat) (hr : r < 2) : (r + 2 * a) / 2 = a := by omega

theorem bit0_add (r a : Nat) (hr : r < 2) : (r + 2 * a).testBit 0 = decide (r = 1) := by
  simp only [Nat.testBit_zero]; congr 1; apply propext; omega

theorem land_step (r s a b : Nat) (hr : r < 2) (hs : s < 2) :
    (r + 2 * a) &&& (s + 2 * b) = r * s + 2 * (a &&& b) := by
  have hrs : r * s < 2 := by rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero =>
    rw [Nat.testBit_and, bit0_add r a hr, bit0_add s b hs, bit0_add _ _ hrs]
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> decide
  | succ i =>
    rw [Nat.testBit_and, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one,
      half_add r a hr, half_add s b hs, half_add _ _ hrs, Nat.testBit_and]

theorem lor_step (r s a b : Nat) (hr : r < 2) (hs : s < 2) :
    (r + 2 * a) ||| (s + 2 * b) = (r + s - r * s) + 2 * (a ||| b) := by
  have hrs : r + s - r * s < 2 := by
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero =>
    rw [Nat.testBit_or, bit0_add r a hr, bit0_add s b hs, bit0_add _ _ hrs]
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> decide
  | succ i =>
    rw [Nat.testBit_or, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one,
      half_add r a hr, half_add s b hs, half_add _ _ hrs, Nat.testBit_or]

theorem xor_step (r s a b : Nat) (hr : r < 2) (hs : s < 2) :
    (r + 2 * a) ^^^ (s + 2 * b) = (r + s - 2 * (r * s)) + 2 * (a ^^^ b) := by
  have hrs : r + s - 2 * (r * s) < 2 := by
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;> omega
  apply Nat.eq_of_testBit_eq; intro i
  cases i with
  | zero =>
    rw [Nat.testBit_xor, bit0_add r a hr, bit0_add s b hs, bit0_add _ _ hrs]
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> decide
  | succ i =>
    rw [Nat.testBit_xor, Nat.testBit_add_one, Nat.testBit_add_one, Nat.testBit_add_one,
      half_add r a hr, half_add s b hs, half_add _ _ hrs, Nat.testBit_xor]

theorem b01_of {ρ : Nat → Int} {b : BT} {v : Nat} (h : b.aff.eval ρ = (v : Int)) (hv : v < 2) : B01 ρ b := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · left; simpa using h
  · right; simpa using h

/-- A bit operation on two values' bits computes `OP` of the values. -/
theorem zipBits_sound {f : BT → BT → Nat → List Cons × BT × Nat} {g : Nat → Nat → Nat}
    {OP : Nat → Nat → Nat} (hf : BitOpOK f g) (h0 : OP 0 0 = 0)
    (hop : ∀ r s a b, r < 2 → s < 2 → OP (r + 2 * a) (s + 2 * b) = g r s + 2 * OP a b) :
    ∀ (xs ys : List BT) (nv : Nat) (ρ : Nat → Int) (a b : Nat), xs.length = ys.length →
      BitsOf ρ xs a → BitsOf ρ ys b → BTsScoped nv xs → BTsScoped nv ys →
      ∃ ρ', Agree ρ ρ' nv ∧ Sat (zipBits f xs ys nv).1 ρ' ∧
        BitsOf ρ' (zipBits f xs ys nv).2.1 (OP a b) ∧ nv ≤ (zipBits f xs ys nv).2.2 ∧
        CsScoped (zipBits f xs ys nv).2.2 (zipBits f xs ys nv).1 ∧
        BTsScoped (zipBits f xs ys nv).2.2 (zipBits f xs ys nv).2.1 ∧
        (zipBits f xs ys nv).2.1.length = xs.length
  | [], [], nv, ρ, a, b, _, ha, hb, _, _ => by
    have ha0 : a = 0 := by have := ha.2; simp at this; omega
    have hb0 : b = 0 := by have := hb.2; simp at this; omega
    subst ha0 hb0
    refine ⟨ρ, Agree.refl ρ nv, sat_nil ρ, ?_, Nat.le_refl _, (fun _ h => nomatch h),
      (fun _ h => nomatch h), rfl⟩
    rw [h0]; constructor <;> simp [zipBits]
  | [], _ :: _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => by simp at hl
  | x :: xs, y :: ys, nv, ρ, a, b, hl, ha, hb, hsx, hsy => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨r, hr, hr2⟩ := (ha.1 x (List.Mem.head _)).nat
    obtain ⟨s, hs, hs2⟩ := (hb.1 y (List.Mem.head _)).nat
    obtain ⟨a', ha'⟩ := bits_nat (fun z hz => ha.1 z (List.Mem.tail _ hz))
    obtain ⟨b', hb'⟩ := bits_nat (fun z hz => hb.1 z (List.Mem.tail _ hz))
    have hae : a = r + 2 * a' := by have := ha.2; rw [eval_bitSum_cons, hr, ha'.2] at this; omega
    have hbe : b = s + 2 * b' := by have := hb.2; rw [eval_bitSum_cons, hs, hb'.2] at this; omega
    have hx0 := hsx x (List.Mem.head _)
    have hy0 := hsy y (List.Mem.head _)
    obtain ⟨ρ1, ag1, sat1, ev1, g2, le1, sc1, scz⟩ := hf x y nv ρ r s hr hs hr2 hs2 hx0 hy0
    have hsxs : BTsScoped nv xs := fun z hz => hsx z (List.Mem.tail _ hz)
    have hsys : BTsScoped nv ys := fun z hz => hsy z (List.Mem.tail _ hz)
    obtain ⟨ρ2, ag2, sat2, bits2, le2, sc2, scs2, len2⟩ := zipBits_sound hf h0 hop xs ys
      (f x y nv).2.2 ρ1 a' b' hl (bitsOf_congr hsxs ag1 ha') (bitsOf_congr hsys ag1 hb')
      (hsxs.mono le1) (hsys.mono le1)
    have ev2 : (f x y nv).2.1.aff.eval ρ2 = (g r s : Int) := (eval_congr scz ag2).symm.trans ev1
    refine ⟨ρ2, ag1.trans (ag2.mono le1), ?_, ?_, Nat.le_trans le1 le2, ?_, ?_, ?_⟩
    · simp only [zipBits]; exact Sat.append (Sat.congr sc1 ag2 sat1) sat2
    · simp only [zipBits]
      refine ⟨?_, ?_⟩
      · intro z hz
        cases hz with
        | head => exact b01_of ev2 g2
        | tail _ hz => exact bits2.1 z hz
      · rw [eval_bitSum_cons, ev2, bits2.2, hae, hbe, hop r s a' b' hr2 hs2]; omega
    · simp only [zipBits]; exact CsScoped.append (sc1.mono le2) sc2
    · simp only [zipBits]
      intro z hz
      cases hz with
      | head => exact scz.mono le2
      | tail _ hz => exact scs2 z hz
    · simp only [zipBits, List.length_cons, len2]

/-! ## Reading a term's bits -/

theorem intEqb_eq : ∀ {a b : Int}, intEqb a b = true → a = b
  | .ofNat a, .ofNat b, h => by
    have : a = b := Nat.eq_of_beq_eq_true h
    rw [this]
  | .negSucc a, .negSucc b, h => by
    have : a = b := Nat.eq_of_beq_eq_true h
    rw [this]
  | .ofNat _, .negSucc _, h => nomatch h
  | .negSucc _, .ofNat _, h => nomatch h

theorem listEqb_eq : ∀ {a b : List Int}, listEqb a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listEqb, Bool.and_eq_true] at h
    rw [intEqb_eq h.1, listEqb_eq h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem memC_sound : ∀ {c : Cons} {cs : List Cons}, memC c cs = true → c ∈ cs
  | c, [], h => nomatch h
  | c, d :: ds, h => by
    simp only [memC, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · have : c = d := by
        have e1 := listEqb_eq h1; have e2 := intEqb_eq h2
        cases c; cases d; simp_all
      rw [this]; exact List.Mem.head _
    · exact List.Mem.tail _ (memC_sound h)

theorem trivFalse_sound {c : Cons} {ρ : Nat → Int} (h : trivFalse c = true) : ¬ c.sat ρ := by
  simp only [trivFalse, Bool.and_eq_true] at h
  intro hc
  have h0 := ChkLIA.dot_allZero ρ h.1
  have h1 := ChkLIA.isNeg_lt h.2
  simp only [ChkLIA.Cons.sat, h0] at hc
  omega

theorem sat_mem {c : Cons} {cs : List Cons} {ρ : Nat → Int} (hsat : Sat cs ρ) (h : memC c cs = true) :
    c.sat ρ := hsat c (memC_sound h)

theorem bitCs_sound {cs : List Cons} {ρ : Nat → Int} {nv j : Nat} (hsat : Sat cs ρ)
    (hsc : CsScoped nv cs) (h : ((bitCs j).all fun c => memC c cs) = true) :
    (ρ j = 0 ∨ ρ j = 1) ∧ j < nv := by
  simp only [bitCs, rangeCs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have h1 := sat_mem hsat h.1
  have h2 := sat_mem hsat h.2
  rw [sat_le0] at h1 h2
  simp [Mw, modulus] at h1 h2
  have hs := hsc _ (memC_sound h.1)
  simp only [Cons.Scoped, le0, Aff.smul, Aff.v, length_scale, length_unitVec] at hs
  exact ⟨by omega, by omega⟩

theorem zerosThen_dot {x : Int} : ∀ {l : List Int} {j : Nat} (ρ : Nat → Int),
    zerosThen x l j = true → ChkLIA.dot l ρ = x * ρ j ∧ l.length = j + 1
  | [y], 0, ρ, h => by
    simp only [zerosThen] at h
    simp [ChkLIA.dot, intEqb_eq h]
  | y :: l, j + 1, ρ, h => by
    simp only [zerosThen, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨d, hl⟩ := zerosThen_dot (fun i => ρ (i + 1)) h2
    refine ⟨?_, by simp [hl]⟩
    simp only [ChkLIA.dot, intEqb_eq h1, d]; omega
  | [], _, _, h => nomatch h
  | _ :: _ :: _, 0, _, h => nomatch h

theorem bitVarsOf_sound {cs : List Cons} {ρ : Nat → Int} {nv : Nat} (hsat : Sat cs ρ)
    (hsc : CsScoped nv cs) : ∀ {ds : List Cons}, (∀ c ∈ ds, c ∈ cs) →
      ∀ j, memN j (bitVarsOf ds) = true → (ρ j = 0 ∨ ρ j = 1) ∧ j < nv
  | [], _, j, h => nomatch h
  | c1 :: tl, hds, j, h => by
    simp only [bitVarsOf] at h
    split at h
    · exact nomatch h
    · next c2 rest =>
      have htl : ∀ c ∈ c2 :: rest, c ∈ cs := fun c hc => hds c (List.Mem.tail _ hc)
      split at h
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
        simp only [memN, Bool.or_eq_true] at h
        rcases h with h | h
        · have hj : j = c1.coeffs.length - 1 := Nat.eq_of_beq_eq_true h
          obtain ⟨d1, l1⟩ := zerosThen_dot ρ h1
          obtain ⟨d2, _⟩ := zerosThen_dot ρ h3
          have s1 := hsat c1 (hds c1 (List.Mem.head _))
          have s2 := hsat c2 (htl c2 (List.Mem.head _))
          have sc := hsc c1 (hds c1 (List.Mem.head _))
          simp only [ChkLIA.Cons.sat, d1, intEqb_eq h2] at s1
          simp only [ChkLIA.Cons.sat, d2, intEqb_eq h4] at s2
          simp only [Cons.Scoped] at sc
          rw [hj]
          exact ⟨by omega, by omega⟩
        · exact bitVarsOf_sound hsat hsc htl j h
      · exact bitVarsOf_sound hsat hsc htl j h

theorem bitOK_sound {cs : List Cons} {ρ : Nat → Int} {nv : Nat} {b : BT} (hsat : Sat cs ρ)
    (hsc : CsScoped nv cs) (h : bitOK (bitVarsOf cs) b = true) : B01 ρ b ∧ b.aff.Scoped nv := by
  cases b with
  | k b => exact ⟨by cases b <;> simp [B01], scoped_k _ _⟩
  | v j =>
    obtain ⟨h1, h2⟩ := bitVarsOf_sound hsat hsc (fun c hc => hc) j h
    refine ⟨?_, scoped_v h2⟩
    simp only [B01, BT.aff, eval_v]; exact h1
  | n j =>
    obtain ⟨h1, h2⟩ := bitVarsOf_sound hsat hsc (fun c hc => hc) j h
    refine ⟨?_, scoped_sub (scoped_c _ _) (scoped_v h2)⟩
    simp only [B01, BT.aff, eval_sub, eval_c, eval_v]; omega

theorem allOK_sound {cs : List Cons} {ρ : Nat → Int} {nv : Nat} (hsat : Sat cs ρ)
    (hsc : CsScoped nv cs) : ∀ {bs : List BT}, allOK (bitVarsOf cs) bs = true →
      (∀ b ∈ bs, B01 ρ b) ∧ BTsScoped nv bs
  | [], _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | b :: bs, h => by
    simp only [allOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := bitOK_sound hsat hsc h.1
    obtain ⟨r1, r2⟩ := allOK_sound hsat hsc h.2
    refine ⟨?_, ?_⟩
    · intro x hx; cases hx with
      | head => exact h1
      | tail _ hx => exact r1 x hx
    · intro x hx; cases hx with
      | head => exact h2
      | tail _ hx => exact r2 x hx

theorem affZero_eval {e : Aff} (h : affZero e = true) (ρ : Nat → Int) : e.eval ρ = 0 := by
  simp only [affZero, Bool.and_eq_true] at h
  simp only [Aff.eval, dot_allZero' e.co ρ h.1, ChkLIA.isZero_eq h.2]; rfl

/-- What a reading of `w` bits guarantees. -/
def BitsRead (w : Nat) (ρ : Nat → Int) (n : Nat) (bs : List BT) (a : Nat) : Prop :=
  bs.length = w ∧ BitsOf ρ bs a ∧ BTsScoped n bs

theorem ownChk_sound {w : Nat} {cs : List Cons} {e : Aff} {bs : List BT} {ρ : Nat → Int} {nv a : Nat}
    (h : ownChk w cs e bs = true) (hsat : Sat cs ρ) (hsc : CsScoped nv cs) (he : e.eval ρ = a) :
    BitsRead w ρ nv bs a := by
  simp only [ownChk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hz⟩, hb⟩ := h
  obtain ⟨h01, hs⟩ := allOK_sound hsat hsc hb
  have := affZero_eval hz ρ
  rw [eval_sub] at this
  exact ⟨hl, ⟨h01, by omega⟩, hs⟩

/-! ## A fresh decomposition -/

/-- Variables `n, …, n+w-1` set to the low `w` bits of `a`. -/
def setBits (ρ : Nat → Int) : Nat → Nat → Nat → (Nat → Int)
  | _, 0, _ => ρ
  | n, w + 1, a => upd (setBits ρ (n + 1) w (a / 2)) n ((a % 2 : Nat) : Int)

theorem agree_setBits (ρ : Nat → Int) : ∀ (n w a : Nat), Agree ρ (setBits ρ n w a) n
  | n, 0, a => Agree.refl ρ n
  | n, w + 1, a => by
    simp only [setBits]
    exact ((agree_setBits ρ (n + 1) w (a / 2)).mono (Nat.le_succ n)).trans (agree_upd _ n _)

theorem mem_bitVars : ∀ {n w : Nat} {b : BT}, b ∈ bitVars n w → ∃ j, b = .v j ∧ n ≤ j ∧ j < n + w
  | n, 0, b, h => nomatch h
  | n, w + 1, b, h => by
    simp only [bitVars] at h
    cases h with
    | head => exact ⟨n, rfl, Nat.le_refl _, by omega⟩
    | tail _ h =>
      obtain ⟨j, rfl, h1, h2⟩ := mem_bitVars h
      exact ⟨j, rfl, by omega, by omega⟩

theorem eval_bitVars_upd {σ : Nat → Int} {n m : Nat} {x : Int} (hn : n < m) :
    ∀ w, (bitSum (bitVars m w)).eval (upd σ n x) = (bitSum (bitVars m w)).eval σ := by
  intro w
  induction w generalizing m with
  | zero => simp [bitVars]
  | succ w ih =>
    simp only [bitVars, eval_bitSum_cons, BT.aff, eval_v, ih (Nat.lt_succ_of_lt hn)]
    simp [upd]; omega

theorem setBits_bits (ρ : Nat → Int) : ∀ (n w a : Nat),
    BitsOf (setBits ρ n w a) (bitVars n w) (a % 2 ^ w)
  | n, 0, a => by constructor <;> simp [bitVars, Nat.mod_one]
  | n, w + 1, a => by
    obtain ⟨h1, h2⟩ := setBits_bits ρ (n + 1) w (a / 2)
    simp only [setBits]
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [bitVars] at hb
      cases hb with
      | head =>
        simp only [B01, BT.aff, eval_v, upd_self]
        rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;> simp
      | tail _ hb =>
        obtain ⟨j, rfl, hj1, _⟩ := mem_bitVars hb
        have := h1 _ hb
        simp only [B01, BT.aff, eval_v] at this ⊢
        have hne : j ≠ n := by omega
        simp only [upd, hne, if_false]; exact this
    · simp only [bitVars, eval_bitSum_cons, BT.aff, eval_v, upd_self,
        eval_bitVars_upd (Nat.lt_succ_self n), h2]
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mod_mul]
      omega

theorem length_bitVars : ∀ (n w : Nat), (bitVars n w).length = w
  | _, 0 => rfl
  | n, w + 1 => by simp only [bitVars, List.length_cons, length_bitVars (n + 1) w]

theorem scoped_bitVars {n w m : Nat} (h : n + w ≤ m) : BTsScoped m (bitVars n w) := by
  intro b hb
  obtain ⟨j, rfl, _, h2⟩ := mem_bitVars hb
  exact scoped_v (by omega)

theorem varsCs_sat {σ : Nat → Int} : ∀ {n w : Nat}, (∀ b ∈ bitVars n w, B01 σ b) → Sat (varsCs n w) σ
  | n, 0, _ => sat_nil σ
  | n, w + 1, h => by
    simp only [varsCs]
    refine Sat.append ?_ (varsCs_sat (fun b hb => h b (by simp only [bitVars]; exact List.Mem.tail _ hb)))
    have := h (.v n) (by simp only [bitVars]; exact List.Mem.head _)
    simp only [B01, BT.aff, eval_v] at this
    intro d hd
    simp only [bitCs, rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl <;> rw [sat_le0] <;> simp [Mw, modulus] <;> omega

theorem varsCs_scoped : ∀ {n w m : Nat}, n + w ≤ m → CsScoped m (varsCs n w)
  | n, 0, m, _ => fun _ h => nomatch h
  | n, w + 1, m, h => by
    simp only [varsCs]
    refine CsScoped.append ?_ (varsCs_scoped (by omega))
    intro d hd
    simp only [bitCs, rangeCs, List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · exact scoped_le0 (scoped_smul _ (scoped_v (by omega)))
    · exact scoped_le0 (scoped_addC _ (scoped_v (by omega)))

/-- What `getBits` guarantees: an assignment agreeing below `nv`, meeting the
    constraints the reading adds, at which the bits are `a`'s. -/
def GetOK (w : Nat) (ρ : Nat → Int) (nv : Nat) (r : List Cons × List BT × Nat) (a : Nat) : Prop :=
  ∃ ρ', Agree ρ ρ' nv ∧ Sat r.1 ρ' ∧ nv ≤ r.2.2 ∧ CsScoped r.2.2 r.1 ∧ BitsRead w ρ' r.2.2 r.2.1 a

theorem freshBits_sound {w : Nat} {e : Aff} {nv : Nat} {ρ : Nat → Int} {a : Nat}
    (he : e.eval ρ = a) (ha : a < 2 ^ w) (hs : e.Scoped nv) : GetOK w ρ nv (freshBits w e nv) a := by
  have hb := setBits_bits ρ nv w a
  rw [Nat.mod_eq_of_lt ha] at hb
  have hag := agree_setBits ρ nv w a
  have he' : e.eval (setBits ρ nv w a) = a := (eval_congr hs hag).symm.trans he
  have hS : (bitSum (bitVars nv w)).Scoped (nv + w) := scoped_bitSum (scoped_bitVars (Nat.le_refl _))
  have hs' : e.Scoped (nv + w) := hs.mono (by omega)
  refine ⟨setBits ρ nv w a, hag, ?_, by simp [freshBits], ?_, ?_⟩
  · simp only [freshBits]
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · rw [sat_le0, eval_sub, he', hb.2]; omega
    · rw [sat_le0, eval_sub, he', hb.2]; omega
    · exact varsCs_sat hb.1 d hd
  · simp only [freshBits]
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact scoped_le0 (scoped_sub hs' hS)
    · exact scoped_le0 (scoped_sub hS hs')
    · exact varsCs_scoped (Nat.le_refl _) d hd
  · refine ⟨?_, hb, scoped_bitVars (Nat.le_refl _)⟩
    simp only [freshBits]; exact length_bitVars nv w

theorem prefixC_mem : ∀ {p l : List Cons}, prefixC p l = true → ∀ c ∈ p, c ∈ l
  | [], _, _, _, h => nomatch h
  | c :: cs, d :: ds, h, x, hx => by
    simp only [prefixC, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases hx with
    | head =>
      have : c = d := by
        have e1 := listEqb_eq h1; have e2 := intEqb_eq h2
        cases c; cases d; simp_all
      rw [this]; exact List.Mem.head _
    | tail _ hx => exact List.Mem.tail _ (prefixC_mem h3 x hx)
  | _ :: _, [], h, _, _ => nomatch h

theorem decompOf_sound {w : Nat} {e : Aff} : ∀ {ds : List Cons} {bs : List BT},
    decompOf w e ds = some bs → ∃ n, bs = bitVars n w ∧ ∀ c ∈ (freshBits w e n).1, c ∈ ds
  | [], _, h => nomatch h
  | d :: ds, bs, h => by
    simp only [decompOf] at h
    split at h
    · next n hn =>
      split at h
      · next hc =>
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true] at hc
        exact ⟨n, rfl, prefixC_mem hc.2⟩
      · obtain ⟨n', h1, h2⟩ := decompOf_sound h
        exact ⟨n', h1, fun c hc => List.Mem.tail _ (h2 c hc)⟩
    · obtain ⟨n', h1, h2⟩ := decompOf_sound h
      exact ⟨n', h1, fun c hc => List.Mem.tail _ (h2 c hc)⟩

theorem varsCs_read {cs : List Cons} {ρ : Nat → Int} {nv : Nat} (hsat : Sat cs ρ)
    (hsc : CsScoped nv cs) : ∀ {n w : Nat}, (∀ c ∈ varsCs n w, c ∈ cs) →
      (∀ b ∈ bitVars n w, B01 ρ b) ∧ BTsScoped nv (bitVars n w)
  | n, 0, _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | n, w + 1, h => by
    simp only [varsCs] at h
    have hn : ((bitCs n).all fun c => memC c cs) = true := by
      rw [List.all_eq_true]; intro c hc
      have hm := h c (List.mem_append_left _ hc)
      clear h hc
      induction cs with
      | nil => exact nomatch hm
      | cons d ds ih =>
        simp only [memC, Bool.or_eq_true, Bool.and_eq_true]
        cases hm with
        | head =>
          left; exact ⟨by
            have : ∀ l : List Int, listEqb l l = true := by
              intro l; induction l with
              | nil => rfl
              | cons x xs ihl =>
                simp only [listEqb, Bool.and_eq_true, ihl, and_true]
                cases x <;> simp [intEqb]
            exact this _, by cases c.bound <;> simp [intEqb]⟩
        | tail _ hm' =>
          right
          exact ih (fun c hc => hsat c (List.Mem.tail _ hc)) (fun c hc => hsc c (List.Mem.tail _ hc)) hm'
    obtain ⟨h1, h2⟩ := bitCs_sound hsat hsc hn
    obtain ⟨r1, r2⟩ := varsCs_read hsat hsc (n := n + 1) (w := w)
      (fun c hc => h c (List.mem_append_right _ hc))
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [bitVars] at hb
      cases hb with
      | head => simp only [B01, BT.aff, eval_v]; exact h1
      | tail _ hb => exact r1 b hb
    · intro b hb
      simp only [bitVars] at hb
      cases hb with
      | head => exact scoped_v h2
      | tail _ hb => exact r2 b hb

/-- A decomposition found among the path's constraints reads `e`'s bits. -/
theorem fresh_read {w n : Nat} {cs : List Cons} {e : Aff} {ρ : Nat → Int} {nv a : Nat}
    (hmem : ∀ c ∈ (freshBits w e n).1, c ∈ cs) (hsat : Sat cs ρ) (hsc : CsScoped nv cs)
    (he : e.eval ρ = a) : BitsRead w ρ nv (bitVars n w) a := by
  simp only [freshBits] at hmem
  have c1 := hsat _ (hmem _ (List.Mem.head _))
  have c2 := hsat _ (hmem _ (List.Mem.tail _ (List.Mem.head _)))
  rw [sat_le0, eval_sub] at c1 c2
  obtain ⟨r1, r2⟩ := varsCs_read hsat hsc (n := n) (w := w)
    (fun c hc => hmem c (List.Mem.tail _ (List.Mem.tail _ hc)))
  exact ⟨length_bitVars n w, ⟨r1, by omega⟩, r2⟩

theorem getBits_sound {w : Nat} {cs : List Cons} {e : Aff} {nv : Nat} {ρ : Nat → Int} {a : Nat}
    (hsat : Sat cs ρ) (hsc : CsScoped nv cs) (he : e.eval ρ = a) (ha : a < 2 ^ w) (hs : e.Scoped nv) :
    GetOK w ρ nv (getBits w cs e nv) a := by
  unfold getBits
  split
  · next h =>
    exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, Nat.le_refl _, (fun _ h => nomatch h),
      ownChk_sound h hsat hsc he⟩
  · split
    · next bs hd =>
      obtain ⟨n, rfl, hmem⟩ := decompOf_sound hd
      exact ⟨ρ, Agree.refl ρ nv, sat_nil ρ, Nat.le_refl _, (fun _ h => nomatch h),
        fresh_read hmem hsat hsc he⟩
    · exact freshBits_sound he ha hs

/-! ## Moving bits -/

theorem bitsOf_append_mk {ρ : Nat → Int} {xs ys : List BT} {x y : Nat} (hx : BitsOf ρ xs x)
    (hy : BitsOf ρ ys y) : BitsOf ρ (xs ++ ys) (x + 2 ^ xs.length * y) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hx.1 b h
    · exact hy.1 b h
  · rw [eval_bitSum_append, hx.2, hy.2]
    have : ((2 ^ xs.length : Nat) : Int) = (2 : Int) ^ xs.length := Int.natCast_pow 2 _
    rw [← this]; push_cast; rfl

theorem bts_sub {n : Nat} {xs ys : List BT} (h : ∀ b ∈ ys, b ∈ xs ∨ b = .k false)
    (hs : BTsScoped n xs) : BTsScoped n ys := by
  intro b hb
  rcases h b hb with h | h
  · exact hs b h
  · rw [h]; exact scoped_k n _

theorem mem_zeros {b : BT} {j : Nat} (h : b ∈ List.replicate j (BT.k false)) : b = .k false :=
  (List.mem_replicate.mp h).2

theorem drop_last : ∀ (xs : List BT), xs ≠ [] → xs.drop (xs.length - 1) = [lastBit xs]
  | [], h => absurd rfl h
  | [x], _ => by simp [lastBit]
  | x :: y :: ys, _ => by
    have := drop_last (y :: ys) (by simp)
    simp only [List.length_cons, Nat.add_sub_cancel] at this ⊢
    simp only [lastBit, List.drop_succ_cons]
    exact this

theorem lastBit_mem : ∀ (xs : List BT), xs ≠ [] → lastBit xs ∈ xs
  | [], h => absurd rfl h
  | [x], _ => List.Mem.head _
  | x :: y :: ys, _ => List.Mem.tail _ (lastBit_mem (y :: ys) (by simp))

theorem pow_split {w j : Nat} (hj : j ≤ w) : 2 ^ w = 2 ^ j * 2 ^ (w - j) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- What moving `w` bits by `f j` computes, for every `j < w`. -/
def MoveOK (f : Nat → List BT → List BT) (V : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (w : Nat) (ρ : Nat → Int) (n : Nat) (xs : List BT) (a j : Nat), BitsRead w ρ n xs a → j < w →
    BitsOf ρ (f j xs) (V w a j) ∧ BTsScoped n (f j xs) ∧ V w a j < 2 ^ w

theorem shl_ok : MoveOK shlBits (fun w a j => (a * 2 ^ j) % 2 ^ w) := by
  intro w ρ n xs a j ⟨hl, hb, hs⟩ hj
  have ht := (bitsOf_take_drop (j := w - j) hb (by omega)).1
  have h := bitsOf_append_mk (bitsOf_zeros ρ j) ht
  simp only [List.length_replicate, Nat.zero_add] at h
  refine ⟨?_, ?_, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  · simp only [shlBits, hl]
    rw [pow_split (Nat.le_of_lt hj), Nat.mul_comm a, Nat.mul_mod_mul_left]; exact h
  · refine bts_sub ?_ hs
    intro b hb'
    simp only [shlBits] at hb'
    rcases List.mem_append.mp hb' with h | h
    · exact Or.inr (mem_zeros h)
    · exact Or.inl (List.mem_of_mem_take h)

theorem lshr_ok : MoveOK lshrBits (fun w a j => a / 2 ^ j) := by
  intro w ρ n xs a j ⟨hl, hb, hs⟩ hj
  have hd := (bitsOf_take_drop (j := j) hb (by omega)).2
  have h := bitsOf_append_mk hd (bitsOf_zeros ρ j)
  simp only [Nat.mul_zero, Nat.add_zero] at h
  refine ⟨h, ?_, ?_⟩
  · refine bts_sub ?_ hs
    intro b hb'
    simp only [lshrBits] at hb'
    rcases List.mem_append.mp hb' with h | h
    · exact Or.inl (List.mem_of_mem_drop h)
    · exact Or.inr (mem_zeros h)
  · have := bitsOf_lt hb; rw [hl] at this
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this

theorem mask_ok : MoveOK maskBits (fun w a j => a % 2 ^ j) := by
  intro w ρ n xs a j ⟨hl, hb, hs⟩ hj
  have ht := (bitsOf_take_drop (j := j) hb (by omega)).1
  have h := bitsOf_append_mk ht (bitsOf_zeros ρ (xs.length - j))
  simp only [Nat.mul_zero, Nat.add_zero] at h
  refine ⟨h, ?_, ?_⟩
  · refine bts_sub ?_ hs
    intro b hb'
    simp only [maskBits] at hb'
    rcases List.mem_append.mp hb' with h | h
    · exact Or.inl (List.mem_of_mem_take h)
    · exact Or.inr (mem_zeros h)
  · have := bitsOf_lt hb; rw [hl] at this
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this

/-- The sign bit of `w ≥ 1` bits of `a` is `1` exactly when `a` is negative read signed. -/
theorem sign_bit {ρ : Nat → Int} {n w : Nat} {xs : List BT} {a : Nat} (h : BitsRead w ρ n xs a)
    (hw : 1 ≤ w) : B01 ρ (lastBit xs) ∧
      (lastBit xs).aff.eval ρ = (if isNeg w a then 1 else 0) := by
  obtain ⟨hl, hb, hs⟩ := h
  have hne : xs ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
  have hd := (bitsOf_take_drop (j := w - 1) hb (by omega)).2
  rw [← hl, drop_last xs hne, hl] at hd
  have hlt := bitsOf_lt hb
  rw [hl] at hlt
  have hval := hd.2
  simp only [eval_bitSum_cons, eval_bitSum_nil, Int.mul_zero, Int.add_zero] at hval
  have hh : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hq : a / 2 ^ (w - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  refine ⟨hd.1 _ (List.Mem.head _), ?_⟩
  rw [hval]
  by_cases hn : isNeg w a = true
  · have : half w ≤ a := by simpa [isNeg] using hn
    have h1 : 1 ≤ a / 2 ^ (w - 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by
      simp only [half] at this; omega)
    simp only [hn, if_true]; omega
  · have : ¬ half w ≤ a := by simpa [isNeg] using hn
    have h1 : a / 2 ^ (w - 1) = 0 := by
      rw [Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]; simp only [half] at this; omega
    simp only [Bool.not_eq_true] at hn
    simp only [hn]; simp [h1]

theorem ashr_lt {w a b : Nat} (ha : a < modulus w) (hb : b < w) :
    a / 2 ^ b + (if isNeg w a = true then modulus w - 2 ^ (w - b) else 0) < modulus w := by
  have hsplit : modulus w = 2 ^ b * 2 ^ (w - b) := by
    simp only [modulus, ← Nat.pow_add]; congr 1; omega
  have hq : a / 2 ^ b < 2 ^ (w - b) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)]
    rw [hsplit] at ha; rw [Nat.mul_comm]; exact ha
  have hle : 2 ^ (w - b) ≤ modulus w := by
    rw [hsplit]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b)
  split <;> omega

theorem ashr_ok : MoveOK ashrBits
    (fun w a j => a / 2 ^ j + (if isNeg w a = true then modulus w - 2 ^ (w - j) else 0)) := by
  intro w ρ n xs a j hr hj
  obtain ⟨hs01, hsv⟩ := sign_bit hr (by omega)
  obtain ⟨hl, hb, hs⟩ := hr
  have hd := (bitsOf_take_drop (j := j) hb (by omega)).2
  have hrep : BitsOf ρ (List.replicate j (lastBit xs))
      (if isNeg w a then 2 ^ j - 1 else 0) := by
    refine ⟨b01_replicate hs01 j, ?_⟩
    rw [eval_bitSum_replicate hs01 j, hsv]
    have hp : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := Int.natCast_pow 2 _
    have h1 : 1 ≤ 2 ^ j := Nat.two_pow_pos j
    split <;> simp only [Int.one_mul, Int.zero_mul] <;> omega
  have h := bitsOf_append_mk hd hrep
  have hlen : (xs.drop j).length = w - j := by rw [List.length_drop, hl]
  rw [hlen] at h
  have hsplit := pow_split (Nat.le_of_lt hj)
  have hlt := bitsOf_lt hb; rw [hl] at hlt
  refine ⟨?_, ?_, ?_⟩
  · simp only [ashrBits]
    have : 2 ^ (w - j) * (if isNeg w a = true then 2 ^ j - 1 else 0) =
        (if isNeg w a = true then modulus w - 2 ^ (w - j) else 0) := by
      split
      · simp only [modulus, Nat.mul_sub, Nat.mul_one]; rw [hsplit, Nat.mul_comm]
      · simp
    rw [← this]; exact h
  · refine bts_sub ?_ hs
    intro b hb'
    simp only [ashrBits] at hb'
    rcases List.mem_append.mp hb' with h | h
    · exact Or.inl (List.mem_of_mem_drop h)
    · rw [(List.mem_replicate.mp h).2]
      exact Or.inl (lastBit_mem xs (by intro h; rw [h] at hl; simp at hl; omega))
  · exact ashr_lt hlt hj

theorem take_ok {w w' : Nat} {ρ : Nat → Int} {n : Nat} {xs : List BT} {a : Nat}
    (hr : BitsRead w ρ n xs a) (hw : w' ≤ w) :
    BitsOf ρ (xs.take w') (a % 2 ^ w') ∧ BTsScoped n (xs.take w') := by
  obtain ⟨hl, hb, hs⟩ := hr
  exact ⟨(bitsOf_take_drop (j := w') hb (by omega)).1,
    bts_sub (fun b hb => Or.inl (List.mem_of_mem_take hb)) hs⟩

/-! ## Pruning a comparison's cases -/

theorem contraWith_sound {nc : List Int} {b : Int} : ∀ {cs : List Cons},
    contraWith nc b cs = true → ∃ d ∈ cs, d.coeffs = nc ∧ b + d.bound < 0
  | [], h => nomatch h
  | d :: ds, h => by
    simp only [contraWith, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨d, List.Mem.head _, listEqb_eq h1, ChkLIA.isNeg_lt h2⟩
    · obtain ⟨d', hd', h1, h2⟩ := contraWith_sound h
      exact ⟨d', List.Mem.tail _ hd', h1, h2⟩

theorem contra_sound {cs : List Cons} {c : Cons} {ρ : Nat → Int} (h : contra cs c = true)
    (hsat : Sat cs ρ) (hc : c.sat ρ) : False := by
  simp only [contra, Bool.or_eq_true] at h
  rcases h with h | h
  · exact trivFalse_sound h hc
  · obtain ⟨d, hd, hco, hb⟩ := contraWith_sound h
    have h1 := hsat d hd
    simp only [ChkLIA.Cons.sat, hco, ChkLIA.dot_scale] at h1 hc
    omega

/-- A case the concrete values meet survives the pruning. -/
theorem pruneCases_mem {cs : List Cons} {l : List (List Cons × Bool)} {p : List Cons × Bool}
    {ρ : Nat → Int} (hp : p ∈ l) (hsat : Sat cs ρ) (hc : Sat p.1 ρ) : p ∈ pruneCases cs l := by
  simp only [pruneCases, List.mem_filter, Bool.not_eq_true']
  refine ⟨hp, ?_⟩
  cases h : p.1.any (contra cs) with
  | false => rfl
  | true =>
    rw [List.any_eq_true] at h
    obtain ⟨c, hcm, hcc⟩ := h
    exact absurd (contra_sound hcc hsat (hc c hcm)) id

end VF5
