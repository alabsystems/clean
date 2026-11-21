/- EqsatPackedControls: what `exhaust8p` admits and what it does not
   (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   The evidence that `exhaust8p_sound` is used the way a registry will use it
   and that the procedure does not answer `true` for nothing. A rule is
   written here as the generator writes it (constructors and raw `Nat`
   literals), and every `Sound` theorem whose proof is
   `exhaust8p_sound _ _ rflTrue` is the term form a discharge record carries;
   every `… = false` is `rfl`, so the kernel evaluated the procedure to
   `false`.

   | Rule | `exhaust8p` answers | Why |
   |---|---|---|
   | `absorb` `(and ?x (or ?x ?y)) = ?x` | `true` at `u8`, `i8`; `false` at `u16`, `u64`, `usize`, `bool` | two 8-bit variables: 256 comparisons of 256 lanes; no other type is covered |
   | `subAdd` `(sub (add ?x ?y) ?y) = ?x` | `true` at `u8`, `i8` | `add` and `sub` leave their lane only by the bit the mask clears |
   | `xorXor` `(xor (xor ?x ?y) ?y) = ?x` | `true` at `u8`, `i8` | |
   | `addCarry` `(add (and ?x ?y) (or ?x ?y)) = (add ?x ?y)` | `true` at `u8`, `i8` | arithmetic over bitwise operators |
   | `subOrAnd` `(sub (or ?x ?y) (and ?x ?y)) = (xor ?x ?y)` | `true` at `u8` | |
   | `negSub` `(neg (sub ?x ?y)) = (sub ?y ?x)` | `true` at `u8`, `i8` | `neg` |
   | `deMorgan` `(not (and (not ?x) (not ?y))) = (or ?x ?y)` | `true` at `u8` | `not` |
   | `subNeg` `(sub ?x (neg ?y)) = (add ?x ?y)` | `true` at `u8` | |
   | `addComm` `(add ?x ?y)` refines to `(add ?y ?x)` | `true` at `u8` | a `refines` rule whose sides are one value |
   | `cvarComm` `(add (const ?c) ?x) = (add ?x (const ?c))` | `true` at `u8` | a constant variable is a variable |
   | `addWide` `(add ?x (const 256)) = ?x` | `true` at `u8` | a literal is read modulo the type: 256 is 0 |
   | `subAllOnes` `(sub (const -1) ?x) = (not ?x)` | `true` at `u8`, `i8` | -1 is 255; one variable |
   | `constFold` `(add (const 1) (const 255)) = (const 0)` | `true` at `u8` | no variable |
   | `subAddWrong` `(sub (add ?x ?y) ?x) = ?x` | `false` at `u8`, `i8` | false (x = 0, y = 1) |
   | `wrongOperandOrder` `(add ?x (neg ?y)) = (sub ?y ?x)` | `false` at `u8` | trust-cg's wrong rule; false (x = 1, y = 0) |
   | `addIsOr` `(add ?x ?y) = (or ?x ?y)` | `false` at `u8` | false wherever a carry is produced |
   | `cornerTopTop`, `cornerZeroZero`, `cornerTopZero`, `cornerZeroTop` | `false` at `u8` | each fails on one assignment only: both variables at 255, both at 0, and one at each end |
   | `mulComm` `(mul ?x ?y) = (mul ?y ?x)` | `false` at `u8` | `mul` is outside the lane fragment |
   | `rotRound` `(rotl (rotr ?x ?y) ?y) = ?x` | `false` at `u8` | a rotation |
   | `selectEq` `(select (icmp.eq ?x ?y) ?x ?y) = ?y` | `false` at `u8` | a comparison and a select |
   | `boolBeside` `?x = ?x` beside a Boolean variable | `false` at `u8` | a variable that is not of sort `t`; the rule is `Sound` (`bool_beside_sound_u8`) |
   | `condAllOnes` `(and ?x (const ?c)) = ?x where (eq ?c -1)` | `false` at `u8` | a side condition |
   | `threeVars` `?x = ?x` beside two more 8-bit variables | `false` at `u8` | over `maxVars`; the rule is `Sound` (`three_vars_sound_u8`) |
   | `unboundSide` `?z = ?z` with two variables | `false` at `u8` | a side is not a term |
   | `ttSide` `?x = true` | `false` at `u8` | a Boolean literal |

   A `false` of `exhaust8p` is never a refutation: `boolBeside` and
   `threeVars` are answered `false` and proved `Sound` at `u8` here by hand,
   and `mulComm` and `condAllOnes` are true rules too (not proved here).

   The last section pins the evaluators on closed terms: one lane vector
   compared with the vector of the answer on each lane (`pack` of the scalar
   answers through `lanesOk`), for each operator of the fragment at the two
   ends of its range.
-/
import EqsatPacked

namespace EqsatPackedControls
open SemR EqsatRule EqsatDecide

/-- Two variables of the instance type. -/
def xy : Sorts := Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil)

/-! ## Rules the procedure proves -/

/-- `(and ?x (or ?x ?y)) = ?x`. -/
def absorb : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.and (Pat.var (nat_lit 0))
      (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem absorb_u8 : Sound absorb (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem absorb_i8 : Sound absorb (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- The same `true` gives the statements that the rule says something. -/
theorem absorb_defined_u8 : Defined absorb (.int .u8) := exhaust8p_defined _ _ rflTrue
theorem absorb_satisfiable_u8 : Satisfiable absorb (.int .u8) :=
  exhaust8p_satisfiable _ _ rflTrue

/-- At a type the procedure does not cover the answer is `false`, so the
    proof of `absorb_u8` is not a proof at another type. -/
theorem absorb_u16_false : exhaust8p absorb (.int .u16) = false := rfl
theorem absorb_u64_false : exhaust8p absorb (.int .u64) = false := rfl
theorem absorb_usize_false : exhaust8p absorb (.int .usize) = false := rfl
theorem absorb_bool_false : exhaust8p absorb .bool = false := rfl

/-- `(sub (add ?x ?y) ?y) = ?x`. -/
def subAdd : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.sub (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem sub_add_u8 : Sound subAdd (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem sub_add_i8 : Sound subAdd (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- `(xor (xor ?x ?y) ?y) = ?x`. -/
def xorXor : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.xor (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem xor_xor_u8 : Sound xorXor (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem xor_xor_i8 : Sound xorXor (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- `(add (and ?x ?y) (or ?x ?y)) = (add ?x ?y)`: arithmetic over bitwise
    operators, which neither a truth table nor a polynomial decides. -/
def addCarry : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.add
      (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem add_carry_u8 : Sound addCarry (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem add_carry_i8 : Sound addCarry (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- `(sub (or ?x ?y) (and ?x ?y)) = (xor ?x ?y)`. -/
def subOrAnd : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.sub
      (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem sub_or_and_u8 : Sound subOrAnd (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(neg (sub ?x ?y)) = (sub ?y ?x)`. -/
def negSub : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.un UnOp.neg (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.sub (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem neg_sub_u8 : Sound negSub (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem neg_sub_i8 : Sound negSub (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- `(not (and (not ?x) (not ?y))) = (or ?x ?y)`. -/
def deMorgan : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.un UnOp.not
      (Pat.bin BinOp.and (Pat.un UnOp.not (Pat.var (nat_lit 0)))
        (Pat.un UnOp.not (Pat.var (nat_lit 1)))))
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem de_morgan_u8 : Sound deMorgan (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(sub ?x (neg ?y)) = (add ?x ?y)`. -/
def subNeg : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.un UnOp.neg (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem sub_neg_u8 : Sound subNeg (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(add ?x ?y)` refines to `(add ?y ?x)`: both sides are a value on every
    assignment, so the `refines` statement is the `equiv` statement. -/
def addComm : Rule :=
  Rule.mk Dir.refines xy
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem add_comm_refines_u8 : Sound addComm (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(add (const ?c) ?x) = (add ?x (const ?c))`: a constant variable ranges
    over the same residues as any other. -/
def cvarComm : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.add (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 0)))
    Conds.nil

theorem cvar_comm_u8 : Sound cvarComm (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(add ?x (const 256)) = ?x`, beside a second variable it does not read:
    the literal is read modulo the type, where 256 is 0. -/
def addWide : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 256)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem add_wide_u8 : Sound addWide (.int .u8) := exhaust8p_sound _ _ rflTrue

/-- `(sub (const -1) ?x) = (not ?x)`: one variable, and -1 is 255. -/
def subAllOnes : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.sub (Pat.lit true (nat_lit 1)) (Pat.var (nat_lit 0)))
    (Pat.un UnOp.not (Pat.var (nat_lit 0)))
    Conds.nil

theorem sub_all_ones_u8 : Sound subAllOnes (.int .u8) := exhaust8p_sound _ _ rflTrue
theorem sub_all_ones_i8 : Sound subAllOnes (.int .i8) := exhaust8p_sound _ _ rflTrue

/-- `(add (const 1) (const 255)) = (const 0)`: no variable, one comparison. -/
def constFold : Rule :=
  Rule.mk Dir.equiv Sorts.nil
    (Pat.bin BinOp.add (Pat.lit false (nat_lit 1)) (Pat.lit false (nat_lit 255)))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem const_fold_u8 : Sound constFold (.int .u8) := exhaust8p_sound _ _ rflTrue

/-! ## False rules -/

/-- `(sub (add ?x ?y) ?x) = ?x`: `subAdd` with the wrong operand taken
    away. -/
def subAddWrong : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.sub (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem sub_add_wrong_u8_false : exhaust8p subAddWrong (.int .u8) = false := rfl
theorem sub_add_wrong_i8_false : exhaust8p subAddWrong (.int .i8) = false := rfl

/-- trust-cg's `wrong_operand_order`: `(add ?x (neg ?y)) = (sub ?y ?x)`. -/
def wrongOperandOrder : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.un UnOp.neg (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.sub (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem wrong_operand_order_false : exhaust8p wrongOperandOrder (.int .u8) = false := rfl

/-- `(add ?x ?y) = (or ?x ?y)`: true wherever no carry is produced. -/
def addIsOr : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem add_is_or_false : exhaust8p addIsOr (.int .u8) = false := rfl

/-- `(and (or Z (neg Z)) (const 128)) = (const 128)`: true exactly where `Z`
    is not 0 (the sign bit of `Z | -Z`). -/
def nonZero (z : Pat) : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.and (Pat.bin BinOp.or z (Pat.un UnOp.neg z)) (Pat.lit false (nat_lit 128)))
    (Pat.lit false (nat_lit 128))
    Conds.nil

/-- `?v + 1`: 0 at 255 only. -/
def succP (i : Nat) : Pat := Pat.bin BinOp.add (Pat.var i) (Pat.lit false (nat_lit 1))

/-- False only where both variables are 255: the top lane of the first
    comparison. -/
def cornerTopTop : Rule := nonZero (Pat.bin BinOp.or (succP (nat_lit 0)) (succP (nat_lit 1)))

/-- False only where both variables are 0: lane 0 of the last comparison. -/
def cornerZeroZero : Rule := nonZero (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))

/-- False only where the lane variable is 255 and the counted one is 0. -/
def cornerTopZero : Rule := nonZero (Pat.bin BinOp.or (succP (nat_lit 0)) (Pat.var (nat_lit 1)))

/-- False only where the lane variable is 0 and the counted one is 255. -/
def cornerZeroTop : Rule := nonZero (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (succP (nat_lit 1)))

theorem corner_top_top_false : exhaust8p cornerTopTop (.int .u8) = false := rfl
theorem corner_zero_zero_false : exhaust8p cornerZeroZero (.int .u8) = false := rfl
theorem corner_top_zero_false : exhaust8p cornerTopZero (.int .u8) = false := rfl
theorem corner_zero_top_false : exhaust8p cornerZeroTop (.int .u8) = false := rfl

/-- The same test of a pattern that is never 0 is a rule the procedure
    proves, so the four `false` above are the one failing assignment each:
    `Z` is `?x | 1`. -/
def cornerNone : Rule :=
  nonZero (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))

theorem corner_none_u8 : Sound cornerNone (.int .u8) := exhaust8p_sound _ _ rflTrue

/-! ## Outside the fragment -/

/-- `(mul ?x ?y) = (mul ?y ?x)`: `mul` does not act lane by lane. -/
def mulComm : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.mul (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem mul_comm_false : exhaust8p mulComm (.int .u8) = false := rfl

/-- `(rotl (rotr ?x ?y) ?y) = ?x`. -/
def rotRound : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.bin BinOp.rotl (Pat.bin BinOp.rotr (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem rot_round_false : exhaust8p rotRound (.int .u8) = false := rfl

/-- `(select (icmp.eq ?x ?y) ?x ?y) = ?y`. -/
def selectEq : Rule :=
  Rule.mk Dir.equiv xy
    (Pat.sel (Pat.cmp ICmpOp.eq (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
      (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem select_eq_false : exhaust8p selectEq (.int .u8) = false := rfl

/-- An operator outside the fragment is refused wherever it stands, also
    where both sides are the same pattern. -/
def mulSame : Rule := Rule.mk Dir.equiv xy mulComm.lhs mulComm.lhs Conds.nil

theorem mul_same_false : exhaust8p mulSame (.int .u8) = false := rfl

/-- `?x = ?x` beside a Boolean variable. -/
def boolBeside : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.bool false Sorts.nil))
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem bool_beside_false : exhaust8p boolBeside (.int .u8) = false := rfl

theorem bool_beside_sound_u8 : Sound boolBeside (.int .u8) := by
  intro pb env _ hadm _
  simp only [boolBeside, admits_cons_t_int, admits_cons_bool, admits_nil] at hadm
  obtain ⟨x, _, rfl, _, b, _, rfl, rfl⟩ := hadm
  exact ⟨.int .u8 x, rfl, rfl⟩

/-- `(and ?x (const ?c)) = ?x where (eq ?c -1)`: a side condition. -/
def condAllOnes : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.and (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 0)))
    (Pat.var (nat_lit 1))
    (Conds.cons (Cond.eq (nat_lit 0) true (nat_lit 1)) Conds.nil)

theorem cond_all_ones_false : exhaust8p condAllOnes (.int .u8) = false := rfl

/-- `?x = ?x` beside two more 8-bit variables it does not read. -/
def threeVars : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil)))
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem three_vars_false : exhaust8p threeVars (.int .u8) = false := rfl

theorem three_vars_sound_u8 : Sound threeVars (.int .u8) := by
  intro pb env _ hadm _
  simp only [threeVars, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, _, y, _, rfl, _, z, _, rfl, _, rfl⟩ := hadm
  exact ⟨.int .u8 x, rfl, rfl⟩

/-- `?z = ?z` where the rule has two variables: neither side is a term. -/
def unboundSide : Rule :=
  Rule.mk Dir.equiv xy (Pat.var (nat_lit 2)) (Pat.var (nat_lit 2)) Conds.nil

theorem unbound_side_false : exhaust8p unboundSide (.int .u8) = false := rfl

/-- `?x = true`: a Boolean literal is not a pattern of the fragment. -/
def ttSide : Rule :=
  Rule.mk Dir.equiv xy (Pat.var (nat_lit 0)) Pat.tt Conds.nil

theorem tt_side_false : exhaust8p ttSide (.int .u8) = false := rfl

/-! ## The evaluators on closed terms -/

open Packed in
/-- One lane vector against the scalar answers: the first variable is the
    lane's index and the second is `y` on every lane, so lane `i` of the
    vector for `p` must be `evalS [i, y] p`. `lanesOk` reads each of the 256
    lanes. -/
noncomputable def lanesAgree (y : Nat) (p : Pat) : Bool :=
  lanesOk 16 256 (fun i => evalS [i, y] p) (evalV ones mask mods [iota, y * ones] p)

/-- `add` and `sub` at both ends of the counted variable: the carry and the
    borrow out of eight bits are dropped on every lane. -/
theorem lanes_add_0 :
    lanesAgree 0 (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_add_255 :
    lanesAgree 255 (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_sub_0 :
    lanesAgree 0 (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_sub_255 :
    lanesAgree 255 (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_sub_rev_255 :
    lanesAgree 255 (Pat.bin BinOp.sub (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0))) = true := rfl
theorem lanes_and_170 :
    lanesAgree 170 (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_or_170 :
    lanesAgree 170 (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_xor_170 :
    lanesAgree 170 (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = true := rfl
theorem lanes_neg : lanesAgree 0 (Pat.un UnOp.neg (Pat.var (nat_lit 0))) = true := rfl
theorem lanes_not : lanesAgree 0 (Pat.un UnOp.not (Pat.var (nat_lit 0))) = true := rfl
theorem lanes_lit_neg :
    lanesAgree 0 (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit true (nat_lit 1))) = true := rfl

/-- The scalar evaluator is the residue evaluator of `EqsatResidue` on a
    closed instance of each operator (`Packed.evalS_evalR` is the
    theorem). -/
theorem scalar_sub :
    (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))).evalR true 8 256
      [.res 3, .res 5] = .ok (.res 254) := rfl
theorem scalar_sub_s :
    Packed.evalS [3, 5] (Pat.bin BinOp.sub (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = 254 :=
  rfl

/-- An operator outside the fragment is 0 on every lane in `evalV`, which is
    why `frag` and not the comparison refuses it. -/
theorem outside_is_zero :
    Packed.evalV Packed.ones Packed.mask Packed.mods [Packed.iota, Packed.ones]
      (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = 0 := rfl
theorem outside_refused :
    Packed.frag 2 (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))) = false := rfl

end EqsatPackedControls
