/- EqsatDecideControls: what `exhaust8` admits and what it does not (PKG-U6).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   The evidence that `exhaust8_sound` is used the way a registry will use it
   and that the procedure does not answer `true` for nothing. A rule is
   written here as the generator writes it (constructors and raw `Nat`
   literals), and every `Sound` theorem whose proof is
   `exhaust8_sound _ _ rflTrue` is the term form a discharge record carries;
   every `… = false` is `rfl`, so the kernel evaluated the procedure to
   `false`. The gate (`crates/clean-olean/tests/eqsat_decide.rs`) rebuilds
   these literals in Rust, has Clean's entry accept the same terms under the
   budget, and has it refuse `exhaust8_sound <rule> <type> rflTrue` for a
   false rule and for a true 8-bit rule at `u64`.

   | Rule | `exhaust8` answers | Why |
   |---|---|---|
   | `and255` `(and ?x (const 255)) = ?x` | `true` at `u8`, `i8`; `false` at `u16`, `u64`, `usize` | true at eight bits only (`and255_not_sound_u16`: x = 256) |
   | `andNot` `(and ?x (not ?x)) = (const 0)` | `true` at `u8`, `i8` | |
   | `bandAbsorb` `(band ?p (bor ?p ?q)) = ?p` | `true` at `bool` | four assignments, the whole domain |
   | `selectSame` `(select ?c ?x ?x) = ?x` | `true` at `u8`, `i8`, `bool` | a Boolean beside the 8-bit variable: 512 assignments |
   | `selectNested` `(select ?p (select ?q ?x ?x) ?x) = ?x` | `true` at `u8` | 1,024 assignments, the most `exhaust8` enumerates |
   | `selectThree`, one more Boolean | `false` at `u8` | 2,048 assignments: over `maxAssignments` |
   | `bitsHeavy` `(ctpop (bitreverse (bswap ?x))) = (ctpop ?x)` | `true` at `u8` | the dearest one-variable rule measured |
   | `bitsHeavyNested`, the same left side under two selects that read two Booleans | `true` at `u8` | 1,024 assignments of three bit operators: the dearest rule at the size limit the gate measures |
   | `udivSelfRefines` `(udiv ?x ?x)` refines to `(const 1)` | `true` at `u8`, `i8` | the left side is undefined at 0 |
   | `udivSelfEquiv`, the same sides as `equiv` | `false` at `u8` | a refines-only rule offered as `equiv` |
   | `pow2Clear` `(and ?c (sub ?c 1)) = 0 where (pow2 ?c)` | `true` at `u8` | a side condition some assignment meets (`pow2_clear_satisfiable_u8`) |
   | `pow2ClearNoCond`, the same sides with no condition | `false` at `u8` | a missing side condition (c = 255) |
   | `rotlSelfFull` `(rotl ?n ?n) = ?n where ?n == 0 mod width` | `true` at `u8` | |
   | `wrongConstant` `(mul ?x (const 2)) = ?x` | `false` at `u8` | x = 255 |
   | `wrongBooleanConstant` `(icmp.ult ?x ?x) = true` | `false` at `u8` | x = 255 |
   | `wrongSelectArm` `(select true ?x ?y) = ?y` | `false` at `bool` and at `u8` | at `bool` by x = true, y = false; at `u8` it has two 8-bit variables and its `sweep` is `false` too |
   | `wrongOperandOrder` `(add ?x (neg ?y)) = (sub ?y ?x)` | `false` at `u8` | two 8-bit variables; its `sweep` is `false` (x = 255, y = 254) |
   | `missingSideCondition` `(rotl ?x (const ?c)) = ?x` | `false` at `u8` | two 8-bit variables; its `sweep` is `false` |
   | `contradictory` `(add ?c 1) = ?c where (eq ?c 0) (ne ?c 0)` | `false` at `u8` | no assignment meets its conditions: `sweep` is `true`, `live` is `false`, and the rule is `Sound` (`contradictory_is_sound_u8`) |
   | `contradictoryBeside`, the same beside a Boolean variable | `false` at `u8` | neither Boolean gives the conditions an assignment |
   | `udivZeroRefines` `(udiv ?x (const 0))` refines to `(const 7)` | `false` at `u8` | the left side is undefined on every assignment: `sweep` is `true`, `live` is `false`, and the rule is `Sound` (`udiv_zero_refines_is_sound_u8`) |
   | `udivZeroRefinesTt`, the same left side refined to `true` | `false` at `u8` | the same, with a Boolean where a value of the type belongs |
   | `udivZeroRefinesUnbound`, the same left side refined to an unbound `?y` | `false` at `u8` | the right side is not a term: `sweep` is `false` too, beside an undefined left side |
   | `falseAtTop`, `falseAtZero`, `falseAtFalse`, `falseAtTrue` | `false` at `u8`, `u8`, `bool`, `bool` | each fails on one assignment only: the first and the last residue tested, and each Boolean |
   | `pow2TopOnly` `(icmp.ult ?c (const 128)) = true where (pow2 ?c)` | `false` at `u8` | fails at 128 only, the top power of two |
   | `zeroModWidthAtWidth` `(icmp.eq ?n (const 0)) = true where ?n == 0 mod width` | `false` at `u8` | fails at 8, a multiple of the width that is not 0 |
   | `eqNegOne` `(add ?c (const 1)) = (const 0) where (eq ?c -1)` | `true` at `u8` | the condition's literal is read modulo the type: -1 is 255 |
   | `condAtBool` `?p = ?p where (eq ?p 0)` | `true` at `bool` | a condition says nothing of a variable with no residue, as `EqsatRule.onResidue` reads it |
   | `twoVars` `?x = ?x` beside a second 8-bit variable | `false` at `u8` | 65,536 assignments; the rule is `Sound` (`two_vars_sound_u8`) |
   | `unboundSide` `?y = ?y` with `?y` unbound | `false` at `u8` | a side is not a term |
   | `zeroAtBool` `(const 0) = (const 0)` | `true` at `u8`, `false` at `bool` | `(const INT)` is not a term at `bool` |

   The wrong rules are trust-cg's (`crates/trust-cg-eqsat/tests/wrong_rules/`),
   restated: the `eqsat_rules` family quotes them in
   `EqsatIntWrongRuleDefs.lean` and refutes them by hand in
   `EqsatIntControls.lean`; this family takes neither module.

   Five rows are `false` for a rule that is `Sound`: `contradictory` and
   `contradictoryBeside` (by design: a rule that never fires is not admitted),
   `udivZeroRefines` and `udivZeroRefinesTt` (by design: a rule whose left
   side is never a value says nothing of its right side) and `twoVars` (the
   limit). A `false` of `exhaust8` is never a refutation.

   The last section holds four closed outcomes of the evaluator's operator
   forms on a residue where the instance type is `bool`. `RV.WF` excludes
   that operand and no enumeration here builds it, so no proof of this family
   reads those arms; the theorems pin what they answer.
-/
import EqsatExhaust

namespace EqsatDecideControls
open SemR EqsatRule EqsatDecide

/-! ## Rules the procedure proves -/

/-- `(and ?x (const 255)) = ?x`: true at eight bits, false at every wider
    type. -/
def and255 : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 255)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem and255_u8 : Sound and255 (.int .u8) := exhaust8_sound _ _ rflTrue
theorem and255_i8 : Sound and255 (.int .i8) := exhaust8_sound _ _ rflTrue

/-- At a type the procedure does not cover the answer is `false`, so the
    proof of `and255_u8` is not a proof at `u16`, `u64` or `usize`. -/
theorem and255_u16_false : exhaust8 and255 (.int .u16) = false := rfl
theorem and255_u64_false : exhaust8 and255 (.int .u64) = false := rfl
theorem and255_usize_false : exhaust8 and255 (.int .usize) = false := rfl

/-- And at sixteen bits the rule is false, not only unproved: 256 and 255 is
    0. -/
theorem and255_not_sound_u16 : ¬ Sound and255 (.int .u16) := fun h => by
  obtain ⟨v, hl, hr⟩ := h 64 [.int .u16 256] trivial ⟨⟨256, rfl, by decide⟩, trivial⟩ trivial
  have hl' : and255.lhs.eval 64 (.int .u16) [.int .u16 256] = .ok (.int .u16 0) := rfl
  have hr' : and255.rhs.eval 64 (.int .u16) [.int .u16 256] = .ok (.int .u16 256) := rfl
  rw [hl'] at hl
  rw [hr'] at hr
  cases hl
  cases hr

/-- `(and ?x (not ?x)) = (const 0)`. -/
def andNot : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.un UnOp.not (Pat.var (nat_lit 0))))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem and_not_u8 : Sound andNot (.int .u8) := exhaust8_sound _ _ rflTrue
theorem and_not_i8 : Sound andNot (.int .i8) := exhaust8_sound _ _ rflTrue

/-- `(band ?p (bor ?p ?q)) = ?p`. -/
def bandAbsorb : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.bool false Sorts.nil))
    (Pat.bin BinOp.bAnd (Pat.var (nat_lit 0))
      (Pat.bin BinOp.bOr (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem band_absorb_bool : Sound bandAbsorb .bool := exhaust8_sound _ _ rflTrue

/-- `(select ?c ?x ?x) = ?x`: a Boolean variable beside one of the instance
    type. -/
def selectSame : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.sel (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)) (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem select_same_u8 : Sound selectSame (.int .u8) := exhaust8_sound _ _ rflTrue
theorem select_same_i8 : Sound selectSame (.int .i8) := exhaust8_sound _ _ rflTrue
theorem select_same_bool : Sound selectSame .bool := exhaust8_sound _ _ rflTrue

/-- `(select ?p (select ?q ?x ?x) ?x) = ?x`: two Booleans and one 8-bit
    variable, 1,024 assignments, the most `exhaust8` enumerates. -/
def selectNested : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.bool false (Sorts.cons Srt.t false Sorts.nil)))
    (Pat.sel (Pat.var (nat_lit 0))
      (Pat.sel (Pat.var (nat_lit 1)) (Pat.var (nat_lit 2)) (Pat.var (nat_lit 2)))
      (Pat.var (nat_lit 2)))
    (Pat.var (nat_lit 2))
    Conds.nil

theorem select_nested_u8 : Sound selectNested (.int .u8) := exhaust8_sound _ _ rflTrue

/-- The same with a third Boolean it does not read: 2,048 assignments. -/
def selectThree : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false
      (Sorts.cons Srt.bool false (Sorts.cons Srt.t false (Sorts.cons Srt.bool false Sorts.nil))))
    selectNested.lhs selectNested.rhs Conds.nil

/-- Over `maxAssignments` the answer is `false` before any assignment is
    tested. -/
theorem select_three_over_limit : small selectThree true 256 = false := rfl
theorem select_three_false : exhaust8 selectThree (.int .u8) = false := rfl

/-- `(ctpop (bitreverse (bswap ?x))) = (ctpop ?x)`: three bit operators the
    evaluator range-tests on every assignment. -/
def bitsHeavy : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.un UnOp.ctpop (Pat.un UnOp.bitreverse (Pat.un UnOp.bswap (Pat.var (nat_lit 0)))))
    (Pat.un UnOp.ctpop (Pat.var (nat_lit 0)))
    Conds.nil

theorem bits_heavy_u8 : Sound bitsHeavy (.int .u8) := exhaust8_sound _ _ rflTrue

/-- `(select ?p (select ?q H H) H) = (ctpop ?x)` with `H` the left side of
    `bitsHeavy`: three bit operators in each arm, two Booleans the selects
    read, 1,024 assignments. -/
def bitsHeavyNested : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.bool false (Sorts.cons Srt.t false Sorts.nil)))
    (Pat.sel (Pat.var (nat_lit 0))
      (Pat.sel (Pat.var (nat_lit 1))
        (Pat.un UnOp.ctpop (Pat.un UnOp.bitreverse (Pat.un UnOp.bswap (Pat.var (nat_lit 2)))))
        (Pat.un UnOp.ctpop (Pat.un UnOp.bitreverse (Pat.un UnOp.bswap (Pat.var (nat_lit 2))))))
      (Pat.un UnOp.ctpop (Pat.un UnOp.bitreverse (Pat.un UnOp.bswap (Pat.var (nat_lit 2))))))
    (Pat.un UnOp.ctpop (Pat.var (nat_lit 2)))
    Conds.nil

theorem bits_heavy_nested_u8 : Sound bitsHeavyNested (.int .u8) := exhaust8_sound _ _ rflTrue

/-! ## Direction -/

/-- `(udiv ?x ?x)` refines to `(const 1)`: undefined at 0, 1 elsewhere. -/
def udivSelfRefines : Rule :=
  Rule.mk Dir.refines
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.udiv (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.lit false (nat_lit 1))
    Conds.nil

/-- The same sides as an `equiv` rule. -/
def udivSelfEquiv : Rule :=
  Rule.mk Dir.equiv udivSelfRefines.vars udivSelfRefines.lhs udivSelfRefines.rhs Conds.nil

theorem udiv_self_refines_u8 : Sound udivSelfRefines (.int .u8) := exhaust8_sound _ _ rflTrue
theorem udiv_self_refines_i8 : Sound udivSelfRefines (.int .i8) := exhaust8_sound _ _ rflTrue

/-- A refines-only rule offered as `equiv` is not admitted. -/
theorem udiv_self_equiv_false : exhaust8 udivSelfEquiv (.int .u8) = false := rfl

/-- `(udiv ?x (const 0))` refines to `(const 7)`: the left side is undefined
    behaviour on every assignment, so the rule is `Sound` whatever its right
    side is. -/
def udivZeroRefines : Rule :=
  Rule.mk Dir.refines
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.udiv (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    (Pat.lit false (nat_lit 7))
    Conds.nil

/-- Every assignment passes, each by its undefined left side. -/
theorem udiv_zero_refines_sweep : sweep udivZeroRefines true 8 256 = true := rfl

/-- So the rule is `Sound`: by the enumeration alone (`sweep_sound`), which
    is what `Sound` asks. -/
theorem udiv_zero_refines_is_sound_u8 : Sound udivZeroRefines (.int .u8) :=
  fun _ env _ hadm hc =>
    sweep_sound (T := .int .u8) (w := 8) (m := 256) rfl rfl udivZeroRefines
      udiv_zero_refines_sweep env hadm hc

/-- No assignment gives the left side a value. -/
theorem udiv_zero_refines_not_live : live udivZeroRefines true 8 256 = false := rfl

/-- So the rule is not admitted, although it is `Sound`. -/
theorem udiv_zero_refines_false : exhaust8 udivZeroRefines (.int .u8) = false := rfl

/-- The same left side refined to `true`: a Boolean where a value of the
    instance type belongs. `Sound` asks nothing of it, the enumeration
    passes, and the rule is not admitted for the same reason. -/
def udivZeroRefinesTt : Rule :=
  Rule.mk Dir.refines udivZeroRefines.vars udivZeroRefines.lhs Pat.tt Conds.nil

theorem udiv_zero_refines_tt_sweep : sweep udivZeroRefinesTt true 8 256 = true := rfl
theorem udiv_zero_refines_tt_false : exhaust8 udivZeroRefinesTt (.int .u8) = false := rfl

/-- The same left side refined to `?y`, which the rule does not bind: the
    right side is not a term. -/
def udivZeroRefinesUnbound : Rule :=
  Rule.mk Dir.refines udivZeroRefines.vars udivZeroRefines.lhs (Pat.var (nat_lit 1)) Conds.nil

/-- The enumeration alone refuses it: a side that is `bad` stands nowhere,
    not even beside an undefined left side (`holdsR_bad_right`). -/
theorem udiv_zero_refines_unbound_sweep : sweep udivZeroRefinesUnbound true 8 256 = false := rfl
theorem udiv_zero_refines_unbound_false :
    exhaust8 udivZeroRefinesUnbound (.int .u8) = false := rfl

/-! ## Side conditions -/

/-- `(and (const ?c) (sub (const ?c) (const 1))) = (const 0) where (pow2 ?c)`. -/
def pow2Clear : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.and (Pat.cvar (nat_lit 0))
      (Pat.bin BinOp.sub (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 1))))
    (Pat.lit false (nat_lit 0))
    (Conds.cons (Cond.pow2 (nat_lit 0)) Conds.nil)

/-- The same sides with no side condition. -/
def pow2ClearNoCond : Rule :=
  Rule.mk Dir.equiv pow2Clear.vars pow2Clear.lhs pow2Clear.rhs Conds.nil

theorem pow2_clear_u8 : Sound pow2Clear (.int .u8) := exhaust8_sound _ _ rflTrue

/-- The same `true` gives the statement that the conditions can be met. -/
theorem pow2_clear_satisfiable_u8 : Satisfiable pow2Clear (.int .u8) :=
  exhaust8_satisfiable _ _ rflTrue

/-- Without its condition the rule is not admitted: a missing side
    condition. -/
theorem pow2_clear_no_cond_false : exhaust8 pow2ClearNoCond (.int .u8) = false := rfl

/-- `(rotl (const ?n) (const ?n)) = (const ?n) where ?n == 0 mod width`. -/
def rotlSelfFull : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.rotl (Pat.cvar (nat_lit 0)) (Pat.cvar (nat_lit 0)))
    (Pat.cvar (nat_lit 0))
    (Conds.cons (Cond.zeroModWidth (nat_lit 0)) Conds.nil)

theorem rotl_self_full_u8 : Sound rotlSelfFull (.int .u8) := exhaust8_sound _ _ rflTrue

/-- `(add (const ?c) (const 1)) = (const ?c) where (eq ?c 0) (ne ?c 0)`: the
    sides differ on every assignment and no assignment meets the
    conditions. -/
def contradictory : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    (Pat.cvar (nat_lit 0))
    (Conds.cons (Cond.eq (nat_lit 0) false (nat_lit 0))
      (Conds.cons (Cond.ne (nat_lit 0) false (nat_lit 0)) Conds.nil))

/-- The rule is `Sound`, for want of an assignment. -/
theorem contradictory_is_sound_u8 : Sound contradictory (.int .u8) := by
  intro pb env _ hadm hc
  simp only [contradictory, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨c, _, rfl, _, rfl⟩ := hadm
  exact absurd hc.1 hc.2.1

/-- Every assignment passes, each by failing the conditions. -/
theorem contradictory_sweep : sweep contradictory true 8 256 = true := rfl

/-- No assignment meets the conditions. -/
theorem contradictory_not_live : live contradictory true 8 256 = false := rfl

/-- So the rule is not admitted, although it is `Sound`. -/
theorem contradictory_false : exhaust8 contradictory (.int .u8) = false := rfl

/-- The same rule beside a Boolean variable it does not read: neither
    Boolean gives the conditions an assignment. -/
def contradictoryBeside : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false (Sorts.cons Srt.t true Sorts.nil))
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 1)) (Pat.lit false (nat_lit 1)))
    (Pat.cvar (nat_lit 1))
    (Conds.cons (Cond.eq (nat_lit 1) false (nat_lit 0))
      (Conds.cons (Cond.ne (nat_lit 1) false (nat_lit 0)) Conds.nil))

theorem contradictory_beside_false : exhaust8 contradictoryBeside (.int .u8) = false := rfl

/-- `(icmp.ult (const ?c) (const 128)) = true where (pow2 ?c)`: true at every
    power of two but the top one, 128. -/
def pow2TopOnly : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.cmp ICmpOp.ult (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 128)))
    Pat.tt
    (Conds.cons (Cond.pow2 (nat_lit 0)) Conds.nil)

theorem pow2_top_only_false : exhaust8 pow2TopOnly (.int .u8) = false := rfl

/-- `(icmp.eq (const ?n) (const 0)) = true where ?n == 0 mod width`: true at
    0 and false at 8, the first multiple of the width above it. -/
def zeroModWidthAtWidth : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.cmp ICmpOp.eq (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    Pat.tt
    (Conds.cons (Cond.zeroModWidth (nat_lit 0)) Conds.nil)

theorem zero_mod_width_at_width_false : exhaust8 zeroModWidthAtWidth (.int .u8) = false := rfl

/-- `(add (const ?c) (const 1)) = (const 0) where (eq ?c -1)`: the condition's
    literal is read modulo the type, so it holds at 255 and nowhere else. -/
def eqNegOne : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.bin BinOp.add (Pat.cvar (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    (Pat.lit false (nat_lit 0))
    (Conds.cons (Cond.eq (nat_lit 0) true (nat_lit 1)) Conds.nil)

theorem eq_neg_one_u8 : Sound eqNegOne (.int .u8) := exhaust8_sound _ _ rflTrue

/-- `?p = ?p where (eq ?p 0)` at `bool`: a condition says nothing of a
    variable that has no residue and holds there (`EqsatRule.onResidue`), so
    the rule has assignments that meet it. -/
def condAtBool : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false Sorts.nil)
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    (Conds.cons (Cond.eq (nat_lit 0) false (nat_lit 0)) Conds.nil)

theorem cond_at_bool : Sound condAtBool .bool := exhaust8_sound _ _ rflTrue

/-! ## The ends of the enumeration -/

/-- `(icmp.ult ?x (const 255)) = true`: false at 255 only, the first residue
    the enumeration tests. -/
def falseAtTop : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.cmp ICmpOp.ult (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 255)))
    Pat.tt
    Conds.nil

theorem false_at_top_false : exhaust8 falseAtTop (.int .u8) = false := rfl

/-- `(icmp.eq ?x (const 0)) = false`: false at 0 only, the last residue the
    enumeration tests. -/
def falseAtZero : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.cmp ICmpOp.eq (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    Pat.ff
    Conds.nil

theorem false_at_zero_false : exhaust8 falseAtZero (.int .u8) = false := rfl

/-- `(bor ?p ?p) = true`: false at `false` only. -/
def falseAtFalse : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false Sorts.nil)
    (Pat.bin BinOp.bOr (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    Pat.tt
    Conds.nil

theorem false_at_false_false : exhaust8 falseAtFalse .bool = false := rfl

/-- `(band ?p ?p) = false`: false at `true` only. -/
def falseAtTrue : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.bool false Sorts.nil)
    (Pat.bin BinOp.bAnd (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    Pat.ff
    Conds.nil

theorem false_at_true_false : exhaust8 falseAtTrue .bool = false := rfl

/-! ## The wrong rules of trust-cg's wrong-rule set -/

/-- `wrong_constant`: `(mul ?x (const 2)) = ?x`. -/
def wrongConstant : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.mul (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 2)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem wrong_constant_false : exhaust8 wrongConstant (.int .u8) = false := rfl

/-- `wrong_boolean_constant`: `(icmp.ult ?x ?x) = true`. -/
def wrongBooleanConstant : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.cmp ICmpOp.ult (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    Pat.tt
    Conds.nil

theorem wrong_boolean_constant_false : exhaust8 wrongBooleanConstant (.int .u8) = false := rfl

/-- `wrong_select_arm`: `(select true ?x ?y) = ?y`. -/
def wrongSelectArm : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.sel Pat.tt (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 1))
    Conds.nil

/-- At `bool` the rule has four assignments and one of them fails. -/
theorem wrong_select_arm_bool_false : exhaust8 wrongSelectArm .bool = false := rfl

/-- At `u8` it has two 8-bit variables: `exhaust8` answers `false` for its
    size, and the enumeration itself finds a failing assignment. -/
theorem wrong_select_arm_u8_false : exhaust8 wrongSelectArm (.int .u8) = false := rfl
theorem wrong_select_arm_u8_sweep : sweep wrongSelectArm true 8 256 = false := rfl

/-- `wrong_operand_order`: `(add ?x (neg ?y)) = (sub ?y ?x)`. -/
def wrongOperandOrder : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.un UnOp.neg (Pat.var (nat_lit 1))))
    (Pat.bin BinOp.sub (Pat.var (nat_lit 1)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem wrong_operand_order_false : exhaust8 wrongOperandOrder (.int .u8) = false := rfl
theorem wrong_operand_order_sweep : sweep wrongOperandOrder true 8 256 = false := rfl

/-- `missing_side_condition`: `(rotl ?x (const ?c)) = ?x` with no
    condition. -/
def missingSideCondition : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.rotl (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 0)))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem missing_side_condition_false : exhaust8 missingSideCondition (.int .u8) = false := rfl
theorem missing_side_condition_sweep : sweep missingSideCondition true 8 256 = false := rfl

/-! ## What a `false` does not say -/

/-- `?x = ?x`, with a second 8-bit variable it does not read. -/
def twoVars : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem two_vars_sound_u8 : Sound twoVars (.int .u8) := by
  intro pb env _ hadm _
  simp only [twoVars, admits_cons_t_int, admits_nil] at hadm
  obtain ⟨x, _, rfl, _, y, _, rfl, _, rfl⟩ := hadm
  exact ⟨.int .u8 x, rfl, rfl⟩

/-- Two 8-bit variables are 65,536 assignments: `false` for the size of the
    rule, which is `Sound`. A `false` of `exhaust8` is not a refutation. -/
theorem two_vars_over_limit : small twoVars true 256 = false := rfl
theorem two_vars_false : exhaust8 twoVars (.int .u8) = false := rfl

/-- `?y = ?y` where the rule has one variable: neither side is a term. -/
def unboundSide : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.var (nat_lit 1))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem unbound_side_false : exhaust8 unboundSide (.int .u8) = false := rfl

/-- `(const 0) = (const 0)`, no variable: one assignment at an integer type,
    and not a term at `bool`. -/
def zeroAtBool : Rule :=
  Rule.mk Dir.equiv Sorts.nil (Pat.lit false (nat_lit 0)) (Pat.lit false (nat_lit 0)) Conds.nil

theorem zero_u8 : Sound zeroAtBool (.int .u8) := exhaust8_sound _ _ rflTrue
theorem zero_at_bool_false : exhaust8 zeroAtBool .bool = false := rfl

/-! ## A residue where the instance type is `bool` -/

/-- At `bool` no value is a residue (`RV.WF`), and no enumeration of this
    family builds one. Each operator form answers `bad` on one anyway, never
    a value. -/
theorem res_at_bool_bin : binR false 8 256 BinOp.add (.res 1) (.res 2) = .bad := rfl
theorem res_at_bool_un : unR false 8 256 UnOp.neg (.res 1) = .bad := rfl
theorem res_at_bool_cmp : cmpR false 8 ICmpOp.eq (.res 1) (.res 1) = .bad := rfl
theorem res_at_bool_sel : selR false (.bit true) (.res 1) (.res 2) = .bad := rfl

end EqsatDecideControls
