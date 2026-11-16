/- EqsatIntNegRot: the negation and rotation rules of the integer rule set, and
   the rule proved one type at a time (PKG-U2, lemma group d).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `EqsatInt.<rule> : ∀ t, Sound Defs.<rule> (.int t)` for `mul_neg_one`,
   `neg_neg`, `zero_sub`, `add_neg`, `sub_const_to_add` and `rotr_full`
   (`rotl_full` is in `EqsatIntSample.lean`), each one proof at every integer
   type from `Nat` arithmetic modulo SemR's modulus, and
   `EqsatInt.mul_255_neg_i8_i8 : Sound Defs.mul_255_neg_i8 (.int .i8)` and
   `EqsatInt.mul_255_neg_i8_u8 : Sound Defs.mul_255_neg_i8 (.int .u8)` for the
   rule that holds at eight bits only (its literal 255 is the all-ones residue
   there and nowhere else; `EqsatIntControls.wrong_width_u16` is the
   sixteen-bit counterexample of the same sides). A rule with no lemma here
   is not proved. The rule set has no shift rule: the rule grammar refuses
   `shl`, `lshr` and `ashr`.

   The rules of this group with a `where` clause also have
   `EqsatInt.<rule>_sat : ∀ t, Satisfiable Defs.<rule> (.int t)`
   (`sub_const_to_add_sat`, `rotr_full_sat`; `rotl_full_sat` is in
   `EqsatIntSample.lean`). A `_sat` lemma says the side conditions can be met;
   it does not say the rule is `Sound`.

   The helpers of this group are named `EqsatInt.negrot_*`, so no other module
   of the family declares their names: `negrot_mul_pred_mod` (multiplying by
   `m - 1` is negation modulo `m`), `negrot_neg_mod_neg_mod` (negation modulo
   `m` is an involution on residues) and `negrot_negR_negR` (the same for
   SemR's `negR`).
-/
import EqsatBasics
import EqsatIntRuleDefs

namespace EqsatInt
open SemR EqsatRule

/-- Multiplying a residue by `m - 1` negates it modulo `m`. -/
theorem negrot_mul_pred_mod (m x : Nat) (hx : x < m) :
    (x * (m - 1)) % m = (m - x) % m := by
  cases x with
  | zero => simp
  | succ k =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hkn : k < n := by omega
    have e : (k + 1) * (n + 1 - 1) = (n + 1 - (k + 1)) + (n + 1) * k := by
      rw [Nat.add_sub_cancel, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul,
        Nat.mul_comm k n]
      omega
    rw [e, Nat.add_mul_mod_self_left]

/-- Negation modulo `m` is an involution on the residues below `m`. -/
theorem negrot_neg_mod_neg_mod (m x : Nat) (hx : x < m) :
    (m - (m - x % m) % m % m) % m = x := by
  rw [Nat.mod_eq_of_lt hx, Nat.mod_mod]
  cases x with
  | zero => simp
  | succ k =>
    have h1 : m - (k + 1) < m := by omega
    rw [Nat.mod_eq_of_lt h1]
    have h2 : m - (m - (k + 1)) = k + 1 := by omega
    rw [h2, Nat.mod_eq_of_lt hx]

/-- SemR's negation of a residue is an involution. -/
theorem negrot_negR_negR (w x : Nat) (hx : x < modulus w) : negR w (negR w x) = x :=
  negrot_neg_mod_neg_mod (modulus w) x hx

/-- `(mul ?x (const -1))` is `(neg ?x)`, at every integer type: `(const -1)`
    is the all-ones residue `2^w - 1`. -/
theorem mul_neg_one (t : IntTy) : Sound Defs.mul_neg_one (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.mul_neg_one, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (negR (t.bits pb) x), ?_, ?_⟩
  · simp only [Defs.mul_neg_one, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    have h : (x * litR (t.bits pb) true 1) % modulus (t.bits pb) = negR (t.bits pb) x := by
      rw [litR_neg_one]
      show (x * (modulus (t.bits pb) - 1)) % modulus (t.bits pb) =
        (modulus (t.bits pb) - x % modulus (t.bits pb)) % modulus (t.bits pb)
      rw [Nat.mod_eq_of_lt hx]
      exact negrot_mul_pred_mod _ _ hx
    simp [intBin, liftOp, R.bind, h]
  · simp only [Defs.mul_neg_one, Pat.eval, getVar, R.bind, STy.ty]
    rw [evalUnop_int hx]
    simp [intUn]

/-- `(mul ?x (const 255))` is `(neg ?x)` at `u8`: 255 is the all-ones residue
    of eight bits. (The same sides as `EqsatIntControls.wrong_width_holds_u8`.) -/
theorem mul_255_neg_i8_u8 : Sound Defs.mul_255_neg_i8 (.int .u8) := by
  intro pb env _ hadm _
  simp only [Defs.mul_255_neg_i8, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  have hx' : x < 256 := hx
  refine ⟨.int .u8 ((256 - x) % 256), ?_, ?_⟩
  · simp only [Defs.mul_255_neg_i8, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    have : (x * 255) % 256 = (256 - x) % 256 := by omega
    simp [intBin, liftOp, R.bind, litR, modulus, IntTy.bits, this]
  · simp only [Defs.mul_255_neg_i8, Pat.eval, getVar, R.bind, STy.ty]
    rw [evalUnop_int hx]
    have : x % 256 = x := Nat.mod_eq_of_lt hx'
    simp [intUn, negR, modulus, IntTy.bits, this]

/-- `(mul ?x (const 255))` is `(neg ?x)` at `i8`: 255 is the residue of `-1`
    at eight bits. -/
theorem mul_255_neg_i8_i8 : Sound Defs.mul_255_neg_i8 (.int .i8) := by
  intro pb env _ hadm _
  simp only [Defs.mul_255_neg_i8, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  have hx' : x < 256 := hx
  refine ⟨.int .i8 ((256 - x) % 256), ?_, ?_⟩
  · simp only [Defs.mul_255_neg_i8, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    have : (x * 255) % 256 = (256 - x) % 256 := by omega
    simp [intBin, liftOp, R.bind, litR, modulus, IntTy.bits, this]
  · simp only [Defs.mul_255_neg_i8, Pat.eval, getVar, R.bind, STy.ty]
    rw [evalUnop_int hx]
    have : x % 256 = x := Nat.mod_eq_of_lt hx'
    simp [intUn, negR, modulus, IntTy.bits, this]

/-- `(neg (neg ?x))` is `?x`, at every integer type. -/
theorem neg_neg (t : IntTy) : Sound Defs.neg_neg (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.neg_neg, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.neg_neg, Pat.eval, getVar, R.bind, STy.ty]
  rw [evalUnop_int hx]
  simp only [intUn]
  rw [evalUnop_int (negR_lt _ _)]
  simp only [intUn]
  rw [negrot_negR_negR _ _ hx]

/-- `(sub (const 0) ?x)` is `(neg ?x)`, at every integer type. -/
theorem zero_sub (t : IntTy) : Sound Defs.zero_sub (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.zero_sub, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t (negR (t.bits pb) x), ?_, ?_⟩
  · simp only [Defs.zero_sub, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int (litR_lt _ _ _) hx]
    simp [intBin, liftOp, R.bind, litR, negR]
  · simp only [Defs.zero_sub, Pat.eval, getVar, R.bind, STy.ty]
    rw [evalUnop_int hx]
    simp [intUn]

/-- `(add ?x (neg ?y))` is `(sub ?x ?y)`, at every integer type. -/
theorem add_neg (t : IntTy) : Sound Defs.add_neg (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.add_neg, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, y, _, rfl, hy, rfl⟩ := hadm
  refine ⟨.int t ((x + (modulus (t.bits pb) - y % modulus (t.bits pb))) % modulus (t.bits pb)),
    ?_, ?_⟩
  · simp only [Defs.add_neg, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalUnop_int hy]
    simp only [intUn]
    rw [evalBinop_int hx (negR_lt _ _)]
    simp [intBin, liftOp, R.bind, negR]
  · simp only [Defs.add_neg, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hy]
    simp [intBin, liftOp, R.bind]

/-- `(sub ?x (const ?c))` is `(add ?x (eval neg ?c))`, at every integer type,
    with `(eval neg ?c)` read as SemR's `neg` on the constant (premise
    `checker-ground-eval`). The side condition `(ne ?c 0)` is not needed. -/
theorem sub_const_to_add (t : IntTy) : Sound Defs.sub_const_to_add (.int t) := by
  intro pb env _ hadm _
  simp only [Defs.sub_const_to_add, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hc, x, _, rfl, hx, rfl⟩ := hadm
  refine ⟨.int t ((x + (modulus (t.bits pb) - c % modulus (t.bits pb))) % modulus (t.bits pb)),
    ?_, ?_⟩
  · simp only [Defs.sub_const_to_add, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hc]
    simp [intBin, liftOp, R.bind]
  · simp only [Defs.sub_const_to_add, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalUnop_int hc]
    simp only [intUn]
    rw [evalBinop_int hx (negR_lt _ _)]
    simp [intBin, liftOp, R.bind, negR]

/-- The side condition `(ne ?c 0)` of `sub_const_to_add` can be met at every
    integer type and admitted pointer width: `c = 1`. -/
theorem sub_const_to_add_sat (t : IntTy) : Satisfiable Defs.sub_const_to_add (.int t) :=
  fun pb hpb => by
    have h1 : 1 < modulus (t.bits pb) := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp (bits_pos hpb))
    refine ⟨[.int t 1, .int t 0], ⟨⟨1, rfl, h1⟩, ⟨0, rfl, modulus_pos _⟩, trivial⟩, ?_, trivial⟩
    show (1 : Nat) ≠ litR (t.bits pb) false 0
    simp [litR]

/-- `(rotr ?x (const ?c))` is `?x` when `?c` is a multiple of the width, at
    every integer type: the side condition is the hypothesis `hc`. -/
theorem rotr_full (t : IntTy) : Sound Defs.rotr_full (.int t) := by
  intro pb env _ hadm hc
  simp only [Defs.rotr_full, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, hcl, x, _, rfl, hx, rfl⟩ := hadm
  have hc0 : c % t.bits pb = 0 := hc.1
  refine ⟨.int t x, ?_, rfl⟩
  simp only [Defs.rotr_full, Pat.eval, getVar, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx hcl]
  simp [intBin, liftOp, R.bind, hc0, modulus]

/-- The side condition of `rotr_full` can be met at every integer type and
    admitted pointer width, by a constant that is not zero: the width itself. -/
theorem rotr_full_sat (t : IntTy) : Satisfiable Defs.rotr_full (.int t) := fun pb _ =>
  ⟨[.int t (t.bits pb), .int t 0],
    ⟨⟨t.bits pb, rfl, Nat.lt_two_pow_self⟩, ⟨0, rfl, modulus_pos _⟩, trivial⟩,
    ⟨Nat.mod_self _, trivial⟩⟩

end EqsatInt
