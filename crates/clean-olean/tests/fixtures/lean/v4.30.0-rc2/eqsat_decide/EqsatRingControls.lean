/- EqsatRingControls: what `ringAll` admits and what it does not (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   The evidence that `ringAll_sound` is used the way a registry will use it
   and that the procedure does not answer `true` for nothing. A rule is
   written here as the generator writes it (constructors and raw `Nat`
   literals), and every `Sound` theorem whose proof is
   `ringAll_sound _ _ rflTrue` is the term form a discharge record carries;
   every `… = false` is `rfl`, so the kernel evaluated the procedure to
   `false`.

   | Rule | `ringAll` answers | Why |
   |---|---|---|
   | `subAdd` `(sub (add ?x ?y) ?y) = ?x` | `true` at each of the twelve integer types; `false` at `bool` | two variables of the instance type, every width |
   | `subAddRefines`, the same sides as `refines` | `true` at `u64` | the direction is not read: both sides are one common value |
   | `addSelf` `(add ?x ?x) = (mul ?x (const 2))` | `true` at `u8`, `i32`, `u128` | a literal coefficient |
   | `negNot` `(neg (not ?x)) = (add ?x (const 1))` | `true` at `i8`, `u64`, `isize` | `(not a)` is `-a - 1` |
   | `distrib` `(mul ?x (add ?y ?z)) = (add (mul ?x ?y) (mul ?x ?z))` | `true` at `u16`, `i64`, `usize` | three variables, a product of variables |
   | `notAsSub` `(not ?x) = (sub (const -1) ?x)` | `true` at `u32` | a negative literal |
   | `mulNegOne` `(mul ?x (const -1)) = (neg ?x)` | `true` at `i16` | |
   | `subSelf` `(sub ?x ?x) = (const 0)` | `true` at `u8` | every term cancels |
   | `square` `(mul (add ?x ?y) (add ?x ?y)) = (add (add (mul ?x ?x) (mul (const 2) (mul ?x ?y))) (mul ?y ?y))` | `true` at `i128` | degree two |
   | `mulComm` `(mul ?x ?y) = (mul ?y ?x)` | `true` at `u8` | one order of the variables in a monomial |
   | `diffSquares` `(mul (sub ?x ?y) (add ?x ?y)) = (sub (mul ?x ?x) (mul ?y ?y))` | `true` at `i64` | the cross terms cancel |
   | `constVar` `(add (const ?c) (const 0)) = (const ?c)` | `true` at `u8` | a constant variable is a variable |
   | `besideBool` `(add ?x (const 0)) = ?x` beside a variable of sort `bool` it does not read | `true` at `u8` | |
   | `addOne` `(add ?x (const 1)) = ?x` | `false` at `u8`, `u64` | false (`add_one_not_sound_u8`: x = 0) |
   | `wrongConstant` `(mul ?x (const 2)) = ?x` | `false` at `u8` | false |
   | `wrongOperandOrder` `(add ?x (neg ?y)) = (sub ?y ?x)` | `false` at `u8` | false |
   | `wrongNot` `(neg (not ?x)) = (sub ?x (const 1))` | `false` at `u8` | false: the sign of the constant |
   | `mul256` `(mul ?x (const 256)) = (const 0)` | `false` at `u8` | true modulo 256 only, not over the integers; the rule is `Sound` at `u8` (`mul256_sound_u8`, by `exhaust8`) |
   | `and255` `(and ?x (const 255)) = ?x` | `false` at `u8`, `u16` | `and` is outside the fragment (the rule is `Sound` at `u8` and false at `u16`) |
   | `andSelf` `(and ?x ?x) = ?x` | `false` at `u8` | `and` is outside the fragment; the rule is `Sound` at `u8` (`and_self_sound_u8`, by `exhaust8`) |
   | `udivOne` `(udiv ?x (const 1)) = ?x` | `false` at `u8` | `udiv` is outside the fragment |
   | `selectSame` `(select ?c ?x ?x) = ?x` | `false` at `u8` | `select` is outside the fragment |
   | `cmpSelf` `(icmp.eq ?x ?x) = true` | `false` at `u8` | `icmp` and `true` are outside the fragment |
   | `condZero` `(add ?c (const 0)) = ?c where (eq ?c 0)` | `false` at `u8` | a side condition, whatever the sides are |
   | `unboundSide` `?y = ?y` with `?y` unbound | `false` at `u8` | a side is not a term |
   | `boolVar` `(add ?p ?p) = (mul ?p (const 2))` with `?p` of sort `bool` | `false` at `u8` | a variable of sort `bool` is not a ring variable |
   | `subAdd` at `bool` | `false` | `ringAll` covers the integer types only |

   Three rows are `false` for a rule that is `Sound` at the type asked:
   `mul256` (true modulo the type's modulus only), `and255` at `u8` and
   `andSelf` (outside the fragment). A `false` of `ringAll` is never a
   refutation.

   The wrong rules are trust-cg's (`crates/trust-cg-eqsat/tests/wrong_rules/`),
   restated, as in `EqsatDecideControls`.
-/
import EqsatRing

namespace EqsatRingControls
open SemR EqsatRule EqsatDecide

/-! ## Rules the procedure proves -/

/-- `(sub (add ?x ?y) ?y) = ?x`: two variables of the instance type. -/
def subAdd : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.sub (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem sub_add_i8 : Sound subAdd (.int .i8) := ringAll_sound _ _ rflTrue
theorem sub_add_i16 : Sound subAdd (.int .i16) := ringAll_sound _ _ rflTrue
theorem sub_add_i32 : Sound subAdd (.int .i32) := ringAll_sound _ _ rflTrue
theorem sub_add_i64 : Sound subAdd (.int .i64) := ringAll_sound _ _ rflTrue
theorem sub_add_i128 : Sound subAdd (.int .i128) := ringAll_sound _ _ rflTrue
theorem sub_add_isize : Sound subAdd (.int .isize) := ringAll_sound _ _ rflTrue
theorem sub_add_u8 : Sound subAdd (.int .u8) := ringAll_sound _ _ rflTrue
theorem sub_add_u16 : Sound subAdd (.int .u16) := ringAll_sound _ _ rflTrue
theorem sub_add_u32 : Sound subAdd (.int .u32) := ringAll_sound _ _ rflTrue
theorem sub_add_u64 : Sound subAdd (.int .u64) := ringAll_sound _ _ rflTrue
theorem sub_add_u128 : Sound subAdd (.int .u128) := ringAll_sound _ _ rflTrue
theorem sub_add_usize : Sound subAdd (.int .usize) := ringAll_sound _ _ rflTrue

/-- One evaluation is the answer at all twelve types. -/
theorem sub_add_every_type (t : IntTy) : Sound subAdd (.int t) :=
  RingAll.ringRun_sound subAdd rflTrue t

/-- At `bool` the answer is `false`, so the proof of `sub_add_u8` is not a
    proof there. -/
theorem sub_add_bool_false : ringAll subAdd .bool = false := rfl

/-- The same rule says something at each type: `Defined` and `Satisfiable`
    from the same `true`. -/
theorem sub_add_defined_u64 : Defined subAdd (.int .u64) := ringAll_defined _ _ rflTrue
theorem sub_add_satisfiable_u64 : Satisfiable subAdd (.int .u64) := ringAll_satisfiable _ _ rflTrue

/-- The same sides as a `refines` rule: both sides are one common value on
    every assignment, which `refines` admits. -/
def subAddRefines : Rule :=
  Rule.mk Dir.refines subAdd.vars subAdd.lhs subAdd.rhs Conds.nil

theorem sub_add_refines_u64 : Sound subAddRefines (.int .u64) := ringAll_sound _ _ rflTrue

/-- `(add ?x ?x) = (mul ?x (const 2))`. -/
def addSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 2)))
    Conds.nil

theorem add_self_u8 : Sound addSelf (.int .u8) := ringAll_sound _ _ rflTrue
theorem add_self_i32 : Sound addSelf (.int .i32) := ringAll_sound _ _ rflTrue
theorem add_self_u128 : Sound addSelf (.int .u128) := ringAll_sound _ _ rflTrue

/-- `(neg (not ?x)) = (add ?x (const 1))`: `(not a)` is `-a - 1`. -/
def negNot : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.un UnOp.neg (Pat.un UnOp.not (Pat.var (nat_lit 0))))
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    Conds.nil

theorem neg_not_i8 : Sound negNot (.int .i8) := ringAll_sound _ _ rflTrue
theorem neg_not_u64 : Sound negNot (.int .u64) := ringAll_sound _ _ rflTrue
theorem neg_not_isize : Sound negNot (.int .isize) := ringAll_sound _ _ rflTrue

/-- `(mul ?x (add ?y ?z)) = (add (mul ?x ?y) (mul ?x ?z))`: three variables
    and products of variables. -/
def distrib : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0))
      (Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.var (nat_lit 2))))
    (Pat.bin BinOp.add (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 2))))
    Conds.nil

theorem distrib_u16 : Sound distrib (.int .u16) := ringAll_sound _ _ rflTrue
theorem distrib_i64 : Sound distrib (.int .i64) := ringAll_sound _ _ rflTrue
theorem distrib_usize : Sound distrib (.int .usize) := ringAll_sound _ _ rflTrue

/-- `(not ?x) = (sub (const -1) ?x)`: a negative literal. -/
def notAsSub : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.un UnOp.not (Pat.var (nat_lit 0)))
    (Pat.bin BinOp.sub (Pat.lit true (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem not_as_sub_u32 : Sound notAsSub (.int .u32) := ringAll_sound _ _ rflTrue

/-- `(mul ?x (const -1)) = (neg ?x)`. -/
def mulNegOne : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit true (nat_lit 1)))
    (Pat.un UnOp.neg (Pat.var (nat_lit 0)))
    Conds.nil

theorem mul_neg_one_i16 : Sound mulNegOne (.int .i16) := ringAll_sound _ _ rflTrue

/-- `(sub ?x ?x) = (const 0)`: every term cancels. -/
def subSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem sub_self_u8 : Sound subSelf (.int .u8) := ringAll_sound _ _ rflTrue

/-- `(mul (add ?x ?y) (add ?x ?y)) =
    (add (add (mul ?x ?x) (mul (const 2) (mul ?x ?y))) (mul ?y ?y))`. -/
def square : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.mul (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.add
      (Pat.bin BinOp.add (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
        (Pat.bin BinOp.mul (Pat.lit false (nat_lit 2))
          (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))))
      (Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.var (nat_lit 1))))
    Conds.nil

theorem square_i128 : Sound square (.int .i128) := ringAll_sound _ _ rflTrue

/-- `(mul ?x ?y) = (mul ?y ?x)`: a monomial has one order of its variables. -/
def mulComm : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem mul_comm_u8 : Sound mulComm (.int .u8) := ringAll_sound _ _ rflTrue

/-- `(mul (sub ?x ?y) (add ?x ?y)) = (sub (mul ?x ?x) (mul ?y ?y))`: the
    cross terms cancel. -/
def diffSquares : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.mul (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.sub (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
      (Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.var (nat_lit 1))))
    Conds.nil

theorem diff_squares_i64 : Sound diffSquares (.int .i64) := ringAll_sound _ _ rflTrue

/-- `(add (const ?c) (const 0)) = (const ?c)`: a constant variable ranges
    over the same values as a variable. -/
def constVar : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    (Pat.cvar (nat_lit 0))
    Conds.nil

theorem const_var_u8 : Sound constVar (.int .u8) := ringAll_sound _ _ rflTrue

/-- `(add ?x (const 0)) = ?x` beside a variable of sort `bool` that neither
    side reads. -/
def besideBool : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.lit false (nat_lit 0)))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem beside_bool_u8 : Sound besideBool (.int .u8) := ringAll_sound _ _ rflTrue

/-! ## False rules -/

/-- `(add ?x (const 1)) = ?x`. -/
def addOne : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem add_one_u8_false : ringAll addOne (.int .u8) = false := rfl
theorem add_one_u64_false : ringAll addOne (.int .u64) = false := rfl

/-- And the rule is false, not only unproved: 0 + 1 is 1. -/
theorem add_one_not_sound_u8 : ¬ Sound addOne (.int .u8) := fun h => by
  obtain ⟨v, hl, hr⟩ := h 64 [.int .u8 0] trivial ⟨⟨0, rfl, by decide⟩, trivial⟩ trivial
  have hl' : addOne.lhs.eval 64 (.int .u8) [.int .u8 0] = .ok (.int .u8 1) := rfl
  have hr' : addOne.rhs.eval 64 (.int .u8) [.int .u8 0] = .ok (.int .u8 0) := rfl
  rw [hl'] at hl
  rw [hr'] at hr
  cases hl
  cases hr

/-- `(mul ?x (const 2)) = ?x`: a wrong constant. -/
def wrongConstant : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 2)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem wrong_constant_false : ringAll wrongConstant (.int .u8) = false := rfl

/-- `(add ?x (neg ?y)) = (sub ?y ?x)`: the operands of the right side are
    swapped. -/
def wrongOperandOrder : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.un UnOp.neg (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.sub (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem wrong_operand_order_false : ringAll wrongOperandOrder (.int .u8) = false := rfl

/-- `(neg (not ?x)) = (sub ?x (const 1))`: `negNot` with the sign of the
    constant wrong. -/
def wrongNot : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.un UnOp.neg (Pat.un UnOp.not (Pat.var (nat_lit 0))))
    (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    Conds.nil

theorem wrong_not_false : ringAll wrongNot (.int .u8) = false := rfl

/-! ## True rules the procedure does not prove -/

/-- `(mul ?x (const 256)) = (const 0)`: true at eight bits because 256 is 0
    there, and not an identity of polynomials over the integers. -/
def mul256 : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 256)))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem mul256_false : ringAll mul256 (.int .u8) = false := rfl

/-- The rule is `Sound` at `u8`: a `false` of `ringAll` is not a
    refutation. -/
theorem mul256_sound_u8 : Sound mul256 (.int .u8) := exhaust8_sound _ _ rflTrue

/-- `(and ?x (const 255)) = ?x`: `and` is outside the fragment, at the type
    where the rule holds and at the type where it does not. -/
def and255 : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 255)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem and255_u8_false : ringAll and255 (.int .u8) = false := rfl
theorem and255_u16_false : ringAll and255 (.int .u16) = false := rfl

/-- `(and ?x ?x) = ?x`. -/
def andSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem and_self_false : ringAll andSelf (.int .u8) = false := rfl
theorem and_self_sound_u8 : Sound andSelf (.int .u8) := exhaust8_sound _ _ rflTrue

/-! ## Outside the fragment -/

/-- `(udiv ?x (const 1)) = ?x`. -/
def udivOne : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.udiv (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem udiv_one_false : ringAll udivOne (.int .u8) = false := rfl

/-- `(select ?c ?x ?x) = ?x`. -/
def selectSame : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.sel (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)) (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem select_same_false : ringAll selectSame (.int .u8) = false := rfl

/-- `(icmp.eq ?x ?x) = true`. -/
def cmpSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.cmp ICmpOp.eq (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    Pat.tt
    Conds.nil

theorem cmp_self_false : ringAll cmpSelf (.int .u8) = false := rfl

/-- `(add ?c (const 0)) = ?c where (eq ?c 0)`: a rule with a side condition
    is refused whatever its sides are. -/
def condZero : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    (Pat.cvar (nat_lit 0))
    (Conds.cons (Cond.eq (nat_lit 0) false (nat_lit 0)) Conds.nil)

theorem cond_zero_false : ringAll condZero (.int .u8) = false := rfl

/-- `?y = ?y` with `?y` unbound: a side is not a term. -/
def unboundSide : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.var (nat_lit 1))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem unbound_side_false : ringAll unboundSide (.int .u8) = false := rfl

/-- `(add ?p ?p) = (mul ?p (const 2))` with `?p` of sort `bool`: not a term
    of the instance type, and not a ring variable. -/
def boolVar : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false Sorts.nil)
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 2)))
    Conds.nil

theorem bool_var_false : ringAll boolVar (.int .u8) = false := rfl

/-! ## The parts of the procedure -/

/-- The fragment test on `subAdd`, `addOne` and three sides outside the
    fragment, each as the kernel evaluates it. -/
theorem sub_add_in_fragment :
    RingAll.ringPat subAdd.vars subAdd.lhs = true ∧
      RingAll.ringPat subAdd.vars subAdd.rhs = true :=
  ⟨rfl, rfl⟩
theorem add_one_in_fragment :
    RingAll.ringPat addOne.vars addOne.lhs = true ∧
      RingAll.ringPat addOne.vars addOne.rhs = true :=
  ⟨rfl, rfl⟩
theorem and255_outside_fragment : RingAll.ringPat and255.vars and255.lhs = false := rfl
theorem unbound_outside_fragment : RingAll.ringPat unboundSide.vars unboundSide.lhs = false := rfl
theorem bool_var_outside_fragment : RingAll.ringPat boolVar.vars boolVar.lhs = false := rfl

/-- The polynomial of each side of `subAdd` is the one term `1 * ?x`, and
    the two sides of `addOne` differ by the constant term. -/
theorem sub_add_norm :
    RingAll.ringNorm subAdd.lhs = .add 1 (.mul 0 .one) .zero ∧
      RingAll.ringNorm subAdd.rhs = .add 1 (.mul 0 .one) .zero :=
  ⟨rfl, rfl⟩
theorem add_one_norm :
    RingAll.ringNorm addOne.lhs = .add 1 .one (.add 1 (.mul 0 .one) .zero) ∧
      RingAll.ringNorm addOne.rhs = .add 1 (.mul 0 .one) .zero :=
  ⟨rfl, rfl⟩

end EqsatRingControls
