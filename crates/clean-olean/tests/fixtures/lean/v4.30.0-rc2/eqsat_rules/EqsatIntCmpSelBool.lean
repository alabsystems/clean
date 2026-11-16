/- EqsatIntCmpSelBool: the comparison, select and bool rules of the integer rule
   set (PKG-U2, lemma group b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `EqsatInt.<rule> : ∀ t, Sound Defs.<rule> (.int t)` for `icmp_eq_self`,
   `icmp_ne_self`, `icmp_ult_self`, `icmp_ule_self`, `icmp_slt_self`,
   `icmp_sle_self`, `select_true` and `select_false`;
   `EqsatInt.<rule>_bool : Sound Defs.<rule> .bool` for `icmp_eq_self`,
   `icmp_ne_self`, `select_true`, `select_false`, `and_self` and `or_self`;
   `EqsatInt.<rule> : Sound Defs.<rule> .bool` for the bool-only `bor_false`,
   `bxor_false`, `bxor_self` and `bxor_true_true`. `select_same`,
   `select_same_bool`, `band_true` and `band_false` are in
   `EqsatIntSample.lean`. A rule with no lemma here is not proved.

   Every integer lemma is one proof at all widths: a comparison of a residue
   with itself is decided by SemR's `icmpR` on the residue alone (the signed
   orders compare one biased residue with itself), and a select on a literal
   condition is SemR's `selectVal` on admitted arms. No lemma here needs the
   pointer-width hypothesis.
-/
import EqsatBasics
import EqsatIntRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-! ## A comparison of a value with itself -/

/-- `(icmp.eq ?x ?x)` is `true`, at every integer type. -/
theorem icmp_eq_self (t : IntTy) : Sound Defs.icmp_eq_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_eq_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool true, ?_, rfl⟩
  simp only [Defs.icmp_eq_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-- `(icmp.eq ?x ?x)` is `true`, at `bool`. -/
theorem icmp_eq_self_bool : Sound Defs.icmp_eq_self .bool := by
  intro pb env _ hadm _
  simp only [Defs.icmp_eq_self, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨x, _, rfl, rfl⟩ := hadm
  refine ⟨.bool true, ?_, rfl⟩
  simp only [Defs.icmp_eq_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_bool]
  simp [icmpR]

/-- `(icmp.ne ?x ?x)` is `false`, at every integer type. -/
theorem icmp_ne_self (t : IntTy) : Sound Defs.icmp_ne_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_ne_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool false, ?_, rfl⟩
  simp only [Defs.icmp_ne_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-- `(icmp.ne ?x ?x)` is `false`, at `bool`. -/
theorem icmp_ne_self_bool : Sound Defs.icmp_ne_self .bool := by
  intro pb env _ hadm _
  simp only [Defs.icmp_ne_self, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨x, _, rfl, rfl⟩ := hadm
  refine ⟨.bool false, ?_, rfl⟩
  simp only [Defs.icmp_ne_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_bool]
  simp [icmpR]

/-- `(icmp.ult ?x ?x)` is `false`, at every integer type. -/
theorem icmp_ult_self (t : IntTy) : Sound Defs.icmp_ult_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_ult_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool false, ?_, rfl⟩
  simp only [Defs.icmp_ult_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-- `(icmp.ule ?x ?x)` is `true`, at every integer type. -/
theorem icmp_ule_self (t : IntTy) : Sound Defs.icmp_ule_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_ule_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool true, ?_, rfl⟩
  simp only [Defs.icmp_ule_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-- `(icmp.slt ?x ?x)` is `false`, at every integer type. -/
theorem icmp_slt_self (t : IntTy) : Sound Defs.icmp_slt_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_slt_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool false, ?_, rfl⟩
  simp only [Defs.icmp_slt_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-- `(icmp.sle ?x ?x)` is `true`, at every integer type. -/
theorem icmp_sle_self (t : IntTy) : Sound Defs.icmp_sle_self (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.icmp_sle_self, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.bool true, ?_, rfl⟩
  simp only [Defs.icmp_sle_self, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalIcmp_int hx hx]
  simp [icmpR]

/-! ## A select on a literal condition -/

/-- `(select true ?x ?y)` is `?x`, at every integer type. -/
theorem select_true (t : IntTy) : Sound Defs.select_true (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.select_true, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.select_true, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_int true hx hy]

/-- `(select true ?x ?y)` is `?x`, at `bool`. -/
theorem select_true_bool : Sound Defs.select_true .bool := by
  intro pb env _ hadm _
  simp only [Defs.select_true, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨x, _, rfl, y, _, rfl, rfl⟩ := hadm
  refine ⟨.bool x, ?_, rfl⟩
  simp only [Defs.select_true, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_bool]

/-- `(select false ?x ?y)` is `?y`, at every integer type. -/
theorem select_false (t : IntTy) : Sound Defs.select_false (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.select_false, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩ := hadm
  refine ⟨.int t y, ?_, rfl⟩
  simp only [Defs.select_false, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_int false hx hy]

/-- `(select false ?x ?y)` is `?y`, at `bool`. -/
theorem select_false_bool : Sound Defs.select_false .bool := by
  intro pb env _ hadm _
  simp only [Defs.select_false, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨x, _, rfl, y, _, rfl, rfl⟩ := hadm
  refine ⟨.bool y, ?_, rfl⟩
  simp only [Defs.select_false, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_bool]

/-! ## The bool-only rules -/

/-- `(bor ?b false)` is `?b`. -/
theorem bor_false : Sound Defs.bor_false .bool := by
  intro pb env _ hadm _
  simp only [Defs.bor_false, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.bor_false, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(bxor ?b false)` is `?b`. -/
theorem bxor_false : Sound Defs.bxor_false .bool := by
  intro pb env _ hadm _
  simp only [Defs.bxor_false, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.bxor_false, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(bxor ?b ?b)` is `false`. -/
theorem bxor_self : Sound Defs.bxor_self .bool := by
  intro pb env _ hadm _
  simp only [Defs.bxor_self, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool false, ?_, rfl⟩
  simp only [Defs.bxor_self, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(bxor (bxor ?b true) true)` is `?b`: the inner result is a bool, so the
    outer operator is SemR's `boolBin` on it. -/
theorem bxor_true_true : Sound Defs.bxor_true_true .bool := by
  intro pb env _ hadm _
  simp only [Defs.bxor_true_true, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.bxor_true_true, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b
  · show evalBinop pb BinOp.bXor Ty.bool (Val.bool true) (Val.bool true) = _
    rw [evalBinop_bool]; rfl
  · show evalBinop pb BinOp.bXor Ty.bool (Val.bool false) (Val.bool true) = _
    rw [evalBinop_bool]; rfl

/-! ## The bool instances of the bitwise self rules

`(and ?x ?x)` and `(or ?x ?x)` have `bool` in their domain: at `bool` the
integer operator is SemR's `boolBin` (`and` is `bAnd`, `or` is `bOr` there).
Their integer instances are in `EqsatIntBitwise.lean`. -/

/-- `(and ?x ?x)` is `?x`, at `bool`. -/
theorem and_self_bool : Sound Defs.and_self .bool := by
  intro pb env _ hadm _
  simp only [Defs.and_self, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.and_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(or ?x ?x)` is `?x`, at `bool`. -/
theorem or_self_bool : Sound Defs.or_self .bool := by
  intro pb env _ hadm _
  simp only [Defs.or_self, admits_cons_t_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.or_self, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [evalBinop_bool]
  cases b <;> rfl

end EqsatInt
