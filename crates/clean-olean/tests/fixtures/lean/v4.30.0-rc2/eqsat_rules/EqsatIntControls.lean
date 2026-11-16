/- EqsatIntControls: wrong rules refuted through the vocabulary (PKG-U2).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   The non-vacuity evidence for `EqsatRule.Sound`. If `Admits` could not be
   satisfied, or `Pat.eval` did not reach SemR's operators, every rule would
   be `Sound`; so each wrong rule of trust-cg's committed wrong-rule set
   (`crates/trust-cg-eqsat/tests/wrong_rules/`, quoted in
   `EqsatIntWrongRuleDefs.lean`) that is false as a statement is refuted here
   by one assignment, at a named small type (`<rule>_<type>`) and at every
   integer type (`<rule>_all`, through the pointer width 64):

   | Wrong rule | Named type | Every integer type | Assignment |
   |---|---|---|---|
   | `wrong_constant` `(mul ?x 2) = ?x` | `u8` | `wrong_constant_all` | x = 1 |
   | `wrong_operand_order` `(add ?x (neg ?y)) = (sub ?y ?x)` | `u8` | `wrong_operand_order_all` | x = 1, y = 0 |
   | `wrong_select_arm` `(select true ?x ?y) = ?y` | `u8`, `bool` | `wrong_select_arm_all` | x = 0, y = 1 |
   | `wrong_boolean_constant` `(icmp.ult ?x ?x) = true` | `u8` | `wrong_boolean_constant_all` | x = 0 |
   | `missing_side_condition` `(rotl ?x ?c) = ?x`, no condition | `u8` | `missing_side_condition_all` | c = 1, x = 1 |
   | `wrong_width` `(mul ?x 255) = (neg ?x)` | `u16`, `i16` | `wrong_width_wide` (every type not eight bits wide) | x = 1 |
   | `wrong_fold` `(sub ?a ?b) = (eval add ?a ?b)` | `u8` | `wrong_fold_all` | a = 0, b = 1 |
   | `panic_only_udiv_self` `(udiv ?x ?x) = 1` | `u8` | `panic_only_udiv_self_all` | x = 0 (undefined behaviour) |
   | `panic_only_sdiv_neg_one` `(sdiv ?x -1) = (neg ?x)` | `i8` | `panic_only_sdiv_neg_one_all` | x = `2^(w-1)` (undefined behaviour) |

   The last two name operators the rule grammar refuses; the vocabulary can
   state them, and the equiv statement fails because a side is not a value.
   `wrong_width` is also proved at `u8`, where it is true: the refutation is
   of the width, not of the literal.

   `one_way_reversed` is not refuted: `(mul ?x 2)` refines to `(add ?x ?x)` is
   a true statement (`one_way_reversed_is_true`). What is wrong with it is that
   it is not the registered rule; the statement digest refuses it, not the
   kernel.

   The pointer-width hypothesis: `ptr64_only_not_usize` needs the width 32
   and `ptr32_only_not_usize` the width 64, so both disjuncts of `PbOk` are
   exercised; `not_sixteen_holds_usize` is a rule false at sixteen bits that
   is `Sound` at `usize`, so the hypothesis is used and admits nothing else.

   Direction. `(udiv ?x ?x)` refines to `1` at `u8` (`udiv_self_refines_u8`)
   and the equiv statement of the same sides is false
   (`panic_only_udiv_self_u8`), so a refines fact does not give the equiv
   statement (`refines_does_not_give_equiv`); the gate offers the refines
   proof for the equiv statement and requires the kernel to refuse. That
   witness needs `udiv`, an operator that is not total. For a rule the
   grammar can state the two directions are one statement
   (`EqsatRule.refines_gives_equiv_of_total`): `band_false_as_equiv_is_true`
   proves the registered one-way rule `band_false` with its direction
   flipped. So the kernel refuses a refines lemma offered for an equiv
   statement, and does not refuse the statement; the direction of a rule of
   the grammar is held by the rule digest and by the checker's
   `SymOfRefines` refusal.

   What `refines` leaves open: `refines_ub_left_any_rhs` is a refines
   statement whose left side is always undefined behaviour and whose right
   side is not a term, and it holds.

   Side conditions: `contradictory` has conditions no assignment satisfies,
   is `Sound` at every integer type although its sides differ
   (`contradictory_is_sound`, `contradictory_sides_false`), and is told apart
   by `Satisfiable` (`contradictory_not_satisfiable`); `contradictoryAt8` is
   the same at eight bits only.

   Literals: `same_residue_one_statement` and `eval_free_twin_holds` are two
   pairs of different literals with one proposition; the gate requires the
   entry to accept each lemma for the other literal.
-/
import EqsatAnchors
import EqsatIntWrongRuleDefs
import EqsatIntSample
import EqsatIntArith

namespace EqsatIntControls
open SemR EqsatRule

/-- Two sides with different values do not stand in `equiv`. -/
theorem not_equiv_of_values {l r : R Val} {a b : Val} (hl : l = .ok a) (hr : r = .ok b)
    (hne : a ≠ b) : ¬ Holds .equiv l r := by
  rintro ⟨v, hl', hr'⟩
  rw [hl] at hl'; rw [hr] at hr'
  cases hl'; cases hr'
  exact hne rfl

/-- A left side that is undefined behaviour does not stand in `equiv`. -/
theorem not_equiv_of_ub {l r : R Val} {m : String} (hl : l = .stop (.ub m)) :
    ¬ Holds .equiv l r := by
  rintro ⟨v, hl', _⟩
  rw [hl] at hl'
  cases hl'

theorem wrong_constant_u8 : ¬ Sound WrongDefs.wrong_constant (.int .u8) := fun h =>
  not_equiv_of_values (a := .int .u8 2) (b := .int .u8 1) rfl rfl (by simp)
    (h 64 [.int .u8 1] trivial ⟨⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_operand_order_u8 : ¬ Sound WrongDefs.wrong_operand_order (.int .u8) := fun h =>
  not_equiv_of_values (a := .int .u8 1) (b := .int .u8 255) rfl rfl (by simp)
    (h 64 [.int .u8 1, .int .u8 0] trivial
      ⟨⟨1, rfl, by decide⟩, ⟨0, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_select_arm_u8 : ¬ Sound WrongDefs.wrong_select_arm (.int .u8) := fun h =>
  not_equiv_of_values (a := .int .u8 0) (b := .int .u8 1) rfl rfl (by simp)
    (h 64 [.int .u8 0, .int .u8 1] trivial
      ⟨⟨0, rfl, by decide⟩, ⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_select_arm_bool : ¬ Sound WrongDefs.wrong_select_arm .bool := fun h =>
  not_equiv_of_values (a := .bool false) (b := .bool true) rfl rfl (by simp)
    (h 64 [.bool false, .bool true] trivial ⟨⟨false, rfl⟩, ⟨true, rfl⟩, trivial⟩ trivial)

theorem wrong_boolean_constant_u8 : ¬ Sound WrongDefs.wrong_boolean_constant (.int .u8) := fun h =>
  not_equiv_of_values (a := .bool false) (b := .bool true) rfl rfl (by simp)
    (h 64 [.int .u8 0] trivial ⟨⟨0, rfl, by decide⟩, trivial⟩ trivial)

theorem missing_side_condition_u8 : ¬ Sound WrongDefs.missing_side_condition (.int .u8) := fun h =>
  not_equiv_of_values (a := .int .u8 2) (b := .int .u8 1) rfl rfl (by simp)
    (h 64 [.int .u8 1, .int .u8 1] trivial
      ⟨⟨1, rfl, by decide⟩, ⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_width_u16 : ¬ Sound WrongDefs.wrong_width (.int .u16) := fun h =>
  not_equiv_of_values (a := .int .u16 255) (b := .int .u16 65535) rfl rfl (by simp)
    (h 64 [.int .u16 1] trivial ⟨⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_width_i16 : ¬ Sound WrongDefs.wrong_width (.int .i16) := fun h =>
  not_equiv_of_values (a := .int .i16 255) (b := .int .i16 65535) rfl rfl (by simp)
    (h 64 [.int .i16 1] trivial ⟨⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem wrong_fold_u8 : ¬ Sound WrongDefs.wrong_fold (.int .u8) := fun h =>
  not_equiv_of_values (a := .int .u8 255) (b := .int .u8 1) rfl rfl (by simp)
    (h 64 [.int .u8 0, .int .u8 1] trivial
      ⟨⟨0, rfl, by decide⟩, ⟨1, rfl, by decide⟩, trivial⟩ trivial)

theorem panic_only_udiv_self_u8 : ¬ Sound WrongDefs.panic_only_udiv_self (.int .u8) := fun h =>
  not_equiv_of_ub rfl (h 64 [.int .u8 0] trivial ⟨⟨0, rfl, by decide⟩, trivial⟩ trivial)

theorem panic_only_sdiv_neg_one_i8 : ¬ Sound WrongDefs.panic_only_sdiv_neg_one (.int .i8) := fun h =>
  not_equiv_of_ub rfl (h 64 [.int .i8 128] trivial ⟨⟨128, rfl, by decide⟩, trivial⟩ trivial)

/-- The literal of `wrong_width` is true at eight bits: what is refuted above
    is the width. -/
theorem wrong_width_holds_u8 : Sound WrongDefs.wrong_width (.int .u8) := by
  intro pb env _ hadm _
  simp only [WrongDefs.wrong_width, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  have hx' : x < 256 := hx
  refine ⟨.int .u8 ((256 - x) % 256), ?_, ?_⟩
  · simp only [WrongDefs.wrong_width, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    have : (x * 255) % 256 = (256 - x) % 256 := by omega
    simp [intBin, liftOp, R.bind, litR, modulus, IntTy.bits, this]
  · simp only [WrongDefs.wrong_width, Pat.eval, getVar, R.bind, STy.ty]
    rw [evalUnop_int hx]
    have : x % 256 = x := Nat.mod_eq_of_lt hx'
    simp [intUn, negR, modulus, IntTy.bits, this]

/-- `one_way_reversed` is a true statement at every integer type; it is the
    statement digest, not the kernel, that refuses it. -/
theorem one_way_reversed_is_true (t : IntTy) : Sound WrongDefs.one_way_reversed (.int t) := by
  intro pb env _ hadm _
  simp only [WrongDefs.one_way_reversed, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inr ⟨.int t ((x + x) % modulus (t.bits pb)), ?_, ?_⟩
  · simp only [WrongDefs.one_way_reversed, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx (litR_lt _ _ _)]
    have : (x * (2 % modulus (t.bits pb))) % modulus (t.bits pb) = (x + x) % modulus (t.bits pb) := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_two]
    simp [intBin, liftOp, R.bind, litR, this]
  · simp only [WrongDefs.one_way_reversed, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hx]
    simp [intBin, liftOp, R.bind]

/-! ## A refines fact does not give the equiv statement -/

/-- The sides of `panic_only_udiv_self`, stated one way. -/
def udivSelfRefines : Rule :=
  Rule.mk Dir.refines
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.udiv (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.lit false (nat_lit 1))
    Conds.nil

/-- The refines rule has the equiv rule's sides, variables and conditions. -/
theorem udivSelfRefines_sides :
    udivSelfRefines.vars = WrongDefs.panic_only_udiv_self.vars ∧
    udivSelfRefines.lhs = WrongDefs.panic_only_udiv_self.lhs ∧
    udivSelfRefines.rhs = WrongDefs.panic_only_udiv_self.rhs ∧
    udivSelfRefines.conds = WrongDefs.panic_only_udiv_self.conds :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `(udiv ?x ?x)` refines to `1` at `u8`: undefined behaviour at zero, one
    elsewhere. -/
theorem udiv_self_refines_u8 : Sound udivSelfRefines (.int .u8) := by
  intro pb env _ hadm _
  simp only [udivSelfRefines, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  by_cases h0 : x = 0
  · subst h0
    exact Or.inl ⟨_, rfl⟩
  · refine Or.inr ⟨.int .u8 1, ?_, rfl⟩
    simp only [udivSelfRefines, Pat.eval, getVar, R.bind, binTy, STy.ty]
    rw [evalBinop_int hx hx]
    simp [intBin, liftOp, R.bind, h0, Nat.div_self (Nat.pos_of_ne_zero h0)]

theorem refines_does_not_give_equiv :
    ¬ ∀ (vars : Sorts) (lhs rhs : Pat) (conds : Conds) (T : STy),
        Sound ⟨.refines, vars, lhs, rhs, conds⟩ T → Sound ⟨.equiv, vars, lhs, rhs, conds⟩ T :=
  fun h => panic_only_udiv_self_u8 (h _ _ _ _ _ udiv_self_refines_u8)

/-! ## The refutations at every integer type

The same wrong rules, refuted at each of the twelve integer types (through
the pointer width 64, which every type admits), so a registry canary can be
run at the widest type and at `isize` and `usize`, not only at eight bits. -/

theorem one_lt_modulus (t : IntTy) : 1 < modulus (t.bits 64) := by cases t <;> decide

theorem int_ne {t : IntTy} {a b : Nat} (h : a ≠ b) : Val.int t a ≠ Val.int t b :=
  fun e => h (by injection e)

theorem wrong_constant_all (t : IntTy) : ¬ Sound WrongDefs.wrong_constant (.int t) := fun h => by
  have := h 64 [.int t 1] (pbOk_inhabited _) ⟨⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial
  cases t <;>
    exact not_equiv_of_values (a := .int _ 2) (b := .int _ 1) rfl rfl (int_ne (by decide)) this

theorem wrong_operand_order_all (t : IntTy) :
    ¬ Sound WrongDefs.wrong_operand_order (.int t) := fun h => by
  have vals : WrongDefs.wrong_operand_order.lhs.eval 64 (.int t) [.int t 1, .int t 0] =
        .ok (.int t 1) ∧
      WrongDefs.wrong_operand_order.rhs.eval 64 (.int t) [.int t 1, .int t 0] =
        .ok (.int t (modulus (t.bits 64) - 1)) ∧
      1 ≠ modulus (t.bits 64) - 1 := by
    cases t <;> exact ⟨rfl, rfl, by decide⟩
  exact not_equiv_of_values vals.1 vals.2.1 (int_ne vals.2.2)
    (h 64 [.int t 1, .int t 0] (pbOk_inhabited _)
      ⟨⟨1, rfl, one_lt_modulus t⟩, ⟨0, rfl, modulus_pos _⟩, trivial⟩ trivial)

theorem wrong_select_arm_all (t : IntTy) : ¬ Sound WrongDefs.wrong_select_arm (.int t) := fun h => by
  have := h 64 [.int t 0, .int t 1] (pbOk_inhabited _)
    ⟨⟨0, rfl, modulus_pos _⟩, ⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial
  cases t <;>
    exact not_equiv_of_values (a := .int _ 0) (b := .int _ 1) rfl rfl (int_ne (by decide)) this

theorem wrong_boolean_constant_all (t : IntTy) :
    ¬ Sound WrongDefs.wrong_boolean_constant (.int t) := fun h => by
  have := h 64 [.int t 0] (pbOk_inhabited _) ⟨⟨0, rfl, modulus_pos _⟩, trivial⟩ trivial
  cases t <;>
    exact not_equiv_of_values (a := .bool false) (b := .bool true) rfl rfl (by simp) this

theorem missing_side_condition_all (t : IntTy) :
    ¬ Sound WrongDefs.missing_side_condition (.int t) := fun h => by
  have := h 64 [.int t 1, .int t 1] (pbOk_inhabited _)
    ⟨⟨1, rfl, one_lt_modulus t⟩, ⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial
  cases t <;>
    exact not_equiv_of_values (a := .int _ 2) (b := .int _ 1) rfl rfl (int_ne (by decide)) this

/-- `wrong_width` is false at every integer type that is not eight bits wide. -/
theorem wrong_width_wide (t : IntTy) (hw : t.bits 64 ≠ 8) :
    ¬ Sound WrongDefs.wrong_width (.int t) := fun h => by
  have vals : WrongDefs.wrong_width.lhs.eval 64 (.int t) [.int t 1] = .ok (.int t 255) ∧
      WrongDefs.wrong_width.rhs.eval 64 (.int t) [.int t 1] =
        .ok (.int t (modulus (t.bits 64) - 1)) ∧
      255 ≠ modulus (t.bits 64) - 1 := by
    cases t <;> first | exact absurd rfl hw | exact ⟨rfl, rfl, by decide⟩
  exact not_equiv_of_values vals.1 vals.2.1 (int_ne vals.2.2)
    (h 64 [.int t 1] (pbOk_inhabited _) ⟨⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial)

theorem wrong_width_i32 : ¬ Sound WrongDefs.wrong_width (.int .i32) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_u32 : ¬ Sound WrongDefs.wrong_width (.int .u32) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_i64 : ¬ Sound WrongDefs.wrong_width (.int .i64) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_u64 : ¬ Sound WrongDefs.wrong_width (.int .u64) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_i128 : ¬ Sound WrongDefs.wrong_width (.int .i128) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_u128 : ¬ Sound WrongDefs.wrong_width (.int .u128) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_isize : ¬ Sound WrongDefs.wrong_width (.int .isize) :=
  wrong_width_wide _ (by decide)
theorem wrong_width_usize : ¬ Sound WrongDefs.wrong_width (.int .usize) :=
  wrong_width_wide _ (by decide)

theorem wrong_fold_all (t : IntTy) : ¬ Sound WrongDefs.wrong_fold (.int t) := fun h => by
  have vals : WrongDefs.wrong_fold.lhs.eval 64 (.int t) [.int t 0, .int t 1] =
        .ok (.int t (modulus (t.bits 64) - 1)) ∧
      WrongDefs.wrong_fold.rhs.eval 64 (.int t) [.int t 0, .int t 1] = .ok (.int t 1) ∧
      modulus (t.bits 64) - 1 ≠ 1 := by
    cases t <;> exact ⟨rfl, rfl, by decide⟩
  exact not_equiv_of_values vals.1 vals.2.1 (int_ne vals.2.2)
    (h 64 [.int t 0, .int t 1] (pbOk_inhabited _)
      ⟨⟨0, rfl, modulus_pos _⟩, ⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial)

theorem panic_only_udiv_self_all (t : IntTy) :
    ¬ Sound WrongDefs.panic_only_udiv_self (.int t) := fun h => by
  have := h 64 [.int t 0] (pbOk_inhabited _) ⟨⟨0, rfl, modulus_pos _⟩, trivial⟩ trivial
  cases t <;> exact not_equiv_of_ub rfl this

theorem panic_only_sdiv_neg_one_all (t : IntTy) :
    ¬ Sound WrongDefs.panic_only_sdiv_neg_one (.int t) := fun h => by
  have hlt : half (t.bits 64) < modulus (t.bits 64) := by cases t <;> decide
  have := h 64 [.int t (half (t.bits 64))] (pbOk_inhabited _) ⟨⟨_, rfl, hlt⟩, trivial⟩ trivial
  cases t <;> exact not_equiv_of_ub rfl this

/-! ## The pointer-width hypothesis

At `isize` and `usize` a statement quantifies over the pointer widths 32 and
64 and no other. Each disjunct of `PbOk` is needed by one refutation below,
and a rule that is false at sixteen bits is `Sound` at `usize`. -/

/-- `(icmp.ne (const 4294967296) (const 0)) = true`: true where `2^32` is not
    zero, so at 64 bits and not at 32. -/
def ptr64Only : Rule :=
  Rule.mk Dir.equiv
    Sorts.nil
    (Pat.cmp ICmpOp.ne (Pat.lit false (nat_lit 4294967296)) (Pat.lit false (nat_lit 0)))
    Pat.tt
    Conds.nil

/-- `(add ?x (const 4294967296)) = ?x`: true where `2^32` is zero, so at 32
    bits and not at 64. -/
def ptr32Only : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 4294967296)))
    (Pat.var (nat_lit 0))
    Conds.nil

/-- `(icmp.ne (const 65536) (const 0)) = true`: false at sixteen bits, true at
    32 and at 64. -/
def notSixteen : Rule :=
  Rule.mk Dir.equiv
    Sorts.nil
    (Pat.cmp ICmpOp.ne (Pat.lit false (nat_lit 65536)) (Pat.lit false (nat_lit 0)))
    Pat.tt
    Conds.nil

theorem ptr64_only_holds_u64 : Sound ptr64Only (.int .u64) := by
  intro pb env _ hadm _
  simp only [ptr64Only, admits_nil] at hadm
  subst hadm
  exact ⟨.bool true, rfl, rfl⟩

/-- Refuted at `usize` through the pointer width 32: the left disjunct of
    `PbOk`. -/
theorem ptr64_only_not_usize : ¬ Sound ptr64Only (.int .usize) := fun h =>
  not_equiv_of_values (a := .bool false) (b := .bool true) rfl rfl (by simp)
    (h 32 [] (Or.inl rfl) trivial trivial)

theorem ptr32_only_holds_u32 : Sound ptr32Only (.int .u32) := by
  intro pb env _ hadm _
  simp only [ptr32Only, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  have hx' : x < 4294967296 := hx
  refine ⟨.int .u32 x, ?_, rfl⟩
  simp only [ptr32Only, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  simp [intBin, liftOp, R.bind, litR, modulus, IntTy.bits]
  exact hx'

/-- Refuted at `usize` through the pointer width 64: the right disjunct of
    `PbOk`. -/
theorem ptr32_only_not_usize : ¬ Sound ptr32Only (.int .usize) := fun h =>
  not_equiv_of_values (a := .int .usize 4294967296) (b := .int .usize 0) rfl rfl (int_ne (by decide))
    (h 64 [.int .usize 0] (Or.inr rfl) ⟨⟨0, rfl, by decide⟩, trivial⟩ trivial)

/-- `wrong_width` refuted at `usize` through the pointer width 32 as well. -/
theorem wrong_width_usize_at_32 : ¬ Sound WrongDefs.wrong_width (.int .usize) := fun h =>
  not_equiv_of_values (a := .int .usize 255) (b := .int .usize 4294967295) rfl rfl
    (int_ne (by decide)) (h 32 [.int .usize 1] (Or.inl rfl) ⟨⟨1, rfl, by decide⟩, trivial⟩ trivial)

/-- A statement at `usize` is about the pointer widths 32 and 64 only: this
    rule is false at sixteen bits and `Sound` at `usize`. -/
theorem not_sixteen_holds_usize : Sound notSixteen (.int .usize) := by
  intro pb env hpb hadm _
  simp only [notSixteen, admits_nil] at hadm
  subst hadm
  rcases hpb with rfl | rfl <;> exact ⟨.bool true, rfl, rfl⟩

theorem not_sixteen_fails_u16 : ¬ Sound notSixteen (.int .u16) := fun h =>
  not_equiv_of_values (a := .bool false) (b := .bool true) rfl rfl (by simp)
    (h 64 [] trivial trivial trivial)

/-! ## What `refines` does not constrain -/

/-- `(udiv ?x (const 0))` refines to the unbound rank 7. -/
def udivZeroGarbage : Rule :=
  Rule.mk Dir.refines
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.udiv (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    (Pat.var (nat_lit 7))
    Conds.nil

/-- A `refines` statement whose left side is undefined behaviour on every
    assignment holds with any right side, here one that is not a term. The
    left side needs an operator that is not total, which the rule grammar
    refuses; `EqsatRule.refines_gives_equiv_of_total` is why a rule of the
    grammar cannot be proved this way. -/
theorem refines_ub_left_any_rhs (t : IntTy) : Sound udivZeroGarbage (.int t) := by
  intro pb env _ hadm _
  simp only [udivZeroGarbage, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, hx, rfl⟩ := hadm
  refine Or.inl ⟨"unsigned division by zero", ?_⟩
  simp only [udivZeroGarbage, Pat.eval, getVar, litVal, R.bind, binTy, STy.ty]
  rw [evalBinop_int hx (litR_lt _ _ _)]
  simp [intBin, liftOp, R.bind, litR, Nat.zero_mod]

/-- Its right side is not a term on any assignment. -/
theorem udiv_zero_garbage_rhs (pb : Nat) (t : IntTy) (x : Nat) :
    udivZeroGarbage.rhs.eval pb (.int t) [.int t x] = .stop .outOfFuel := rfl

/-! ## Direction, for a rule the grammar can state

`band_false` is registered one way. Its left side names a total operator, so
the equiv statement of the same sides is true and is proved from the refines
lemma. The kernel refuses the refines lemma itself for the equiv statement
(a different proposition), but not the statement: the direction of a rule of
the grammar is held by the rule digest and by the checker's refusal to use a
`refines` step backwards, not by the kernel. -/

/-- `band_false` with its direction flipped. -/
def bandFalseEquiv : Rule :=
  Rule.mk Dir.equiv Defs.band_false.vars Defs.band_false.lhs Defs.band_false.rhs
    Defs.band_false.conds

theorem band_false_as_equiv_is_true : Sound bandFalseEquiv .bool :=
  refines_gives_equiv_of_total _ _ _ _ _ rfl EqsatInt.band_false

/-! ## Side conditions that contradict each other -/

/-- `(add ?x (const ?c)) = (mul ?x (const ?c)) where (eq ?c 0) (ne ?c 0)`:
    the checker's parser accepts it, and it never fires. -/
def contradictory : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 0)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 0)))
    (Conds.cons (Cond.eq (nat_lit 0) false (nat_lit 0))
      (Conds.cons (Cond.ne (nat_lit 0) false (nat_lit 0)) Conds.nil))

/-- The same sides with no side condition. -/
def contradictorySides : Rule :=
  Rule.mk Dir.equiv contradictory.vars contradictory.lhs contradictory.rhs Conds.nil

/-- The sides are not equal: `1 + 1` is not `1 * 1`. -/
theorem contradictory_sides_false (t : IntTy) : ¬ Sound contradictorySides (.int t) := fun h => by
  have := h 64 [.int t 1, .int t 1] (pbOk_inhabited _)
    ⟨⟨1, rfl, one_lt_modulus t⟩, ⟨1, rfl, one_lt_modulus t⟩, trivial⟩ trivial
  cases t <;>
    exact not_equiv_of_values (a := .int _ 2) (b := .int _ 1) rfl rfl (int_ne (by decide)) this

/-- Yet the rule is `Sound` at every integer type, for want of an assignment:
    `Sound` alone would print this row as proved. -/
theorem contradictory_is_sound (t : IntTy) : Sound contradictory (.int t) := by
  intro pb env _ hadm hc
  simp only [contradictory, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, _, x, _, rfl, _, rfl⟩ := hadm
  exact absurd hc.1 hc.2.1

/-- `Satisfiable` is the statement that tells it apart: it is false of this
    rule at every integer type. -/
theorem contradictory_not_satisfiable (t : IntTy) : ¬ Satisfiable contradictory (.int t) := by
  intro h
  obtain ⟨env, hadm, hc⟩ := h 64 (pbOk_inhabited _)
  simp only [contradictory, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, _, x, _, rfl, _, rfl⟩ := hadm
  exact absurd hc.1 hc.2.1

/-- `... where (eq ?c 256) (ne ?c 0)`: contradictory at eight bits only, where
    256 is 0. -/
def contradictoryAt8 : Rule :=
  Rule.mk Dir.equiv contradictory.vars contradictory.lhs contradictory.rhs
    (Conds.cons (Cond.eq (nat_lit 0) false (nat_lit 256))
      (Conds.cons (Cond.ne (nat_lit 0) false (nat_lit 0)) Conds.nil))

theorem contradictory_at8_sound_u8 : Sound contradictoryAt8 (.int .u8) := by
  intro pb env _ hadm hc
  simp only [contradictoryAt8, contradictory, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, _, x, _, rfl, _, rfl⟩ := hadm
  have e : litR (IntTy.u8.bits pb) false 256 = litR (IntTy.u8.bits pb) false 0 :=
    (by decide : litR 8 false 256 = litR 8 false 0)
  exact absurd (hc.1.trans e) hc.2.1

theorem contradictory_at8_not_satisfiable_u8 : ¬ Satisfiable contradictoryAt8 (.int .u8) := by
  intro h
  obtain ⟨env, hadm, hc⟩ := h 64 trivial
  simp only [contradictoryAt8, contradictory, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, _, x, _, rfl, _, rfl⟩ := hadm
  exact absurd (hc.1.trans (by decide : litR 8 false 256 = litR 8 false 0)) hc.2.1

/-- At sixteen bits the conditions are met by `c = 256`, and the rule is
    false there: satisfiability, like soundness, is a fact per type. -/
theorem contradictory_at8_satisfiable_u16 : Satisfiable contradictoryAt8 (.int .u16) :=
  fun _ _ => ⟨[.int .u16 256, .int .u16 0],
    ⟨⟨256, rfl, (by decide : (256 : Nat) < 65536)⟩, ⟨0, rfl, (by decide : (0 : Nat) < 65536)⟩,
      trivial⟩,
    ⟨(by decide : (256 : Nat) = litR 16 false 256), (by decide : (256 : Nat) ≠ litR 16 false 0),
      trivial⟩⟩

theorem contradictory_at8_not_sound_u16 : ¬ Sound contradictoryAt8 (.int .u16) := fun h =>
  not_equiv_of_values (a := .int .u16 257) (b := .int .u16 256) rfl rfl (int_ne (by decide))
    (h 64 [.int .u16 256, .int .u16 1] trivial
      ⟨⟨256, rfl, by decide⟩, ⟨1, rfl, by decide⟩, trivial⟩
      ⟨(by decide : (256 : Nat) = litR 16 false 256), (by decide : (256 : Nat) ≠ litR 16 false 0),
        trivial⟩)

/-! ## Literals that are one proposition

The kernel binds a lemma to the proposition, not to the literal. Two pairs of
different literals with one proposition; the gate offers each lemma for the
other literal and requires the entry to accept. -/

/-- `(const -1)` and `(const 255)` are one residue at eight bits, so
    `mul_neg_one` and `mul_255_neg_i8` are one statement there. -/
theorem same_residue_one_statement :
    Sound Defs.mul_neg_one (.int .u8) ↔ Sound Defs.mul_255_neg_i8 (.int .u8) := by
  have hl : ∀ pb : Nat, litR (IntTy.u8.bits pb) true 1 = litR (IntTy.u8.bits pb) false 255 :=
    fun _ => (by decide : litR 8 true 1 = litR 8 false 255)
  constructor <;> intro h pb env hpb hadm hc <;> have := h pb env hpb hadm hc <;>
    simp only [Defs.mul_neg_one, Defs.mul_255_neg_i8, Pat.eval, litVal, hl] at this ⊢ <;>
    exact this

/-- `mul_mul_const` as the checker's parser reads the same rule written with
    term variables and no `eval`: `(mul (mul ?x ?a) ?b) = (mul ?x (mul ?a ?b))`. -/
def mulAssocTerms : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil)))
    (Pat.bin BinOp.mul (Pat.bin BinOp.mul (Pat.var (nat_lit 2)) (Pat.var (nat_lit 0)))
      (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 2))
      (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    Conds.nil

/-- A rule that uses `eval` and its `eval`-free twin are one statement: the
    `const` flags and `cvar` against `var` do not reach the proposition. So
    whether a row carries the premise `checker-ground-eval` cannot be read
    from its statement. -/
theorem eval_free_twin_holds (t : IntTy) : Sound mulAssocTerms (.int t) := by
  intro pb env hpb hadm _
  simp only [mulAssocTerms, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨a, _, rfl, ha, b, _, rfl, hb, x, _, rfl, hx, rfl⟩ := hadm
  exact EqsatInt.mul_mul_const t pb _ hpb ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩, ⟨x, rfl, hx⟩, trivial⟩
    trivial

/-- A `fold_*` literal has one pattern on both sides: its statement would be
    reflexive, which is why it gets no lemma. -/
theorem fold_literal_is_reflexive : Defs.fold_add.lhs = Defs.fold_add.rhs := rfl

end EqsatIntControls
