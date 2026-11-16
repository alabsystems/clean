/- EqsatIntSample: sample lemmas of the integer rule set (PKG-U2).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   Six lemmas that show the vocabulary is workable and fix the shape and the
   names the rest of the set uses (namespace `EqsatInt`):
   * `EqsatInt.<rule> : ∀ t, Sound Defs.<rule> (.int t)` where the rule holds at
     every integer type (`add_zero`, `select_same`, `rotl_full`);
   * `EqsatInt.<rule>_bool : Sound Defs.<rule> .bool` for a rule whose domain
     has both integer types and `bool` (`select_same_bool`);
   * `EqsatInt.<rule> : Sound Defs.<rule> .bool` for a bool-only rule
     (`band_true`, and `band_false`, a `refines` rule).
   A discharge record's term is the lemma applied to the type
   (`EqsatInt.add_zero SemR.IntTy.u64`) or the lemma constant itself.

   A rule with a `where` clause has a second lemma beside its `Sound` lemma,
   `EqsatInt.<rule>_sat : ∀ t, Satisfiable Defs.<rule> (.int t)`: its side
   conditions can be met at every integer type and admitted pointer width, so
   the rule is not `Sound` for want of an assignment (`rotl_full_sat`).

   The proof shape: introduce the pointer width and the assignment, rewrite
   `Admits` into the assignment's values, unfold `Pat.eval` down to SemR's
   value evaluators, reduce those on admitted operands to the residue operators
   (`EqsatBasics`), and do the arithmetic there.
-/
import EqsatBasics
import EqsatIntRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-- `(add ?x (const 0))` is `?x`, at every integer type. -/
theorem add_zero (t : IntTy) : Sound Defs.add_zero (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.add_zero, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.add_zero, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  simp [intBin, liftOp, R.bind, litR, Nat.mod_eq_of_lt hx]

/-- `(select ?c ?x ?x)` is `?x`, at every integer type. -/
theorem select_same (t : IntTy) : Sound Defs.select_same (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.select_same, admits_cons_t_int, admits_cons_bool, admits_nil] at hadm
  obtain ⟨c, _, rfl, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.select_same, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_int c hx hx]
  cases c <;> rfl

/-- `(select ?c ?x ?x)` is `?x`, at `bool`. -/
theorem select_same_bool : Sound Defs.select_same .bool := by
  intro pb env _ hadm _
  simp only [Defs.select_same, admits_cons_t_bool, admits_cons_bool, admits_nil] at hadm
  obtain ⟨c, _, rfl, x, _, rfl, rfl⟩ := hadm
  refine ⟨.bool x, ?_, rfl⟩
  simp only [Defs.select_same, Pat.eval, getVar, R.bind, STy.ty]
  rw [selectVal_bool]
  cases c <;> rfl

/-- `(band ?b true)` is `?b`. -/
theorem band_true : Sound Defs.band_true .bool := by
  intro pb env _ hadm _
  simp only [Defs.band_true, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine ⟨.bool b, ?_, rfl⟩
  simp only [Defs.band_true, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(band ?b false)` refines to `false` (a one-way rule: the right disjunct
    of the refines statement, since the left side is never undefined). -/
theorem band_false : Sound Defs.band_false .bool := by
  intro pb env _ hadm _
  simp only [Defs.band_false, admits_cons_bool, admits_nil] at hadm
  obtain ⟨b, _, rfl, rfl⟩ := hadm
  refine Or.inr ⟨.bool false, ?_, rfl⟩
  simp only [Defs.band_false, Pat.eval, getVar, R.bind, binTy]
  rw [evalBinop_bool]
  cases b <;> rfl

/-- `(rotl ?x (const ?c))` is `?x` when `?c` is a multiple of the width, at
    every integer type: the side condition is the hypothesis `hc`. -/
theorem rotl_full (t : IntTy) : Sound Defs.rotl_full (.int t) := by
  intro pb env _ hadm hc
  simp only [Defs.rotl_full, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hcl, x, _, rfl, hx, rfl⟩ := hadm
  have hc0 : c % t.bits pb = 0 := hc.1
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.rotl_full, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx hcl]
  have hdiv : x / 2 ^ t.bits pb = 0 := Nat.div_eq_of_lt hx
  simp [intBin, liftOp, R.bind, hc0, Nat.mod_eq_of_lt hx, hdiv]

/-- The side condition of `rotl_full` can be met at every integer type and
    admitted pointer width, by a constant that is not zero: the width itself. -/
theorem rotl_full_sat (t : IntTy) : Satisfiable Defs.rotl_full (.int t) := fun pb _ =>
  ⟨[.int t (t.bits pb), .int t 0],
    ⟨⟨t.bits pb, rfl, Nat.lt_two_pow_self⟩, ⟨0, rfl, modulus_pos _⟩, trivial⟩,
    ⟨Nat.mod_self _, trivial⟩⟩

end EqsatInt
