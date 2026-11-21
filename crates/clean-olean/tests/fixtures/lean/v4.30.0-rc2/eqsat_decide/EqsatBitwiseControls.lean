/- EqsatBitwiseControls: what `bitwiseAll` admits and what it does not
   (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   The evidence that `bitwiseAll_sound` is used the way a registry will use
   it and that the procedure does not answer `true` for nothing. A rule is
   written here as the generator writes it (constructors and raw `Nat`
   literals); every `Sound` theorem whose proof is
   `bitwiseAll_sound _ _ rflTrue` is the term form a discharge record
   carries, and every `… = false` is `rfl`, so the kernel evaluated the
   procedure to `false`.

   | Rule | `bitwiseAll` answers | Why |
   |---|---|---|
   | `andNot` `(and ?x (not ?x)) = (const 0)` | `true` at each of the twelve integer types; `false` at `bool` | one variable, two rows |
   | `orAbsorb` `(or ?x (and ?x ?y)) = ?x` | `true` at `u8`, `i8`, `u16`, `u64`, `i128`, `usize` | two variables, four rows: what `exhaust8` refuses for size at eight bits |
   | `xorSelf` `(xor ?x ?x) = (const 0)` | `true` at `u8`, `u32`, `isize` | |
   | `orNot` `(or ?x (not ?x)) = (const -1)` | `true` at `u8`, `u128` | `(const -1)` is all ones at every width |
   | `xorOnes` `(xor ?x (const -1)) = (not ?x)` | `true` at `u16` | |
   | `deMorgan3`, `(not (and ?x (and ?y ?z)))` refines to `(or (not ?x) (or (not ?y) (not ?z)))` | `true` at `i64` | three variables, eight rows, direction `refines`, one `(const ?v)` |
   | `eightVars`, the `xor` of eight variables against the same in another order | `true` at `u64` | 256 rows, the most `bitwiseAll` builds |
   | `nineVars`, `?a = ?a` beside eight more variables | `false` at `u64` | over `maxBitVars`; the rule is `Sound` |
   | `and255` `(and ?x (const 255)) = ?x` | `false` at `u8`, `i8`, `u16`, `u64` | `(const 255)` is not in the fragment. The rule is true at eight bits (`exhaust8` proves it there) and false at `u16` (`and255_not_sound_u16`) |
   | `andOne` `(and ?x (const 1)) = ?x` | `false` at `u8` | the literal 1 is not in the fragment, and not all ones |
   | `orNegZero` `(or ?x (const -0)) = ?x` | `false` at `u8` | `lit true 0` is not in the fragment; the rule is `Sound` |
   | `orDrop` `(or ?x ?y) = ?x` | `false` at `u8` | the row x = 0, y = 1 differs; `or_drop_not_sound_u8` |
   | `xorSelfWrong` `(xor ?x ?x) = ?x` | `false` at `u8` | the row x = 1 differs |
   | `andIsOr` `(and ?x ?y) = (or ?x ?y)` | `false` at `u64` | |
   | `zeroIsOnes` `(const 0) = (const -1)` | `false` at `u8` | no variable, one row |
   | `addZero` `(add ?x (const 0)) = ?x` | `false` at `u8` | `add` is not in the fragment; the rule is `Sound` |
   | `negNeg` `(neg (neg ?x)) = ?x` | `false` at `u8` | `neg` is not in the fragment |
   | `bandSelf` `(band ?x ?x) = ?x` | `false` at `u8` | `band` is the Boolean operator, not in the fragment |
   | `selSame` `(select true ?x ?x) = ?x` | `false` at `u8` | `select` and `true` are not in the fragment |
   | `cmpSide` `(icmp.eq ?x ?x) = (icmp.eq ?x ?x)` | `false` at `u8` | a comparison is not in the fragment |
   | `unbound` `?y = ?y` with `?y` unbound | `false` at `u8` | a side is not a term |
   | `boolVar` `?x = ?x` beside a variable of sort `bool` | `false` at `u8` | every variable must be of sort `t` |
   | `withCond` `?x = ?x where (ne ?x 0)` | `false` at `u8` | a side condition; the rule is `Sound` |

   A `false` of `bitwiseAll` is never a refutation: `orNegZero`, `addZero`,
   `nineVars` and `withCond` are `Sound` and answered `false`.
-/
import EqsatBitwise

namespace EqsatBitwiseControls
open SemR EqsatRule EqsatDecide

/-! ## Rules the procedure proves, at every integer type from one table -/

/-- `(and ?x (not ?x)) = (const 0)`. -/
def andNot : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.un UnOp.not (Pat.var (nat_lit 0))))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem and_not_i8 : Sound andNot (.int .i8) := bitwiseAll_sound _ _ rflTrue
theorem and_not_i16 : Sound andNot (.int .i16) := bitwiseAll_sound _ _ rflTrue
theorem and_not_i32 : Sound andNot (.int .i32) := bitwiseAll_sound _ _ rflTrue
theorem and_not_i64 : Sound andNot (.int .i64) := bitwiseAll_sound _ _ rflTrue
theorem and_not_i128 : Sound andNot (.int .i128) := bitwiseAll_sound _ _ rflTrue
theorem and_not_isize : Sound andNot (.int .isize) := bitwiseAll_sound _ _ rflTrue
theorem and_not_u8 : Sound andNot (.int .u8) := bitwiseAll_sound _ _ rflTrue
theorem and_not_u16 : Sound andNot (.int .u16) := bitwiseAll_sound _ _ rflTrue
theorem and_not_u32 : Sound andNot (.int .u32) := bitwiseAll_sound _ _ rflTrue
theorem and_not_u64 : Sound andNot (.int .u64) := bitwiseAll_sound _ _ rflTrue
theorem and_not_u128 : Sound andNot (.int .u128) := bitwiseAll_sound _ _ rflTrue
theorem and_not_usize : Sound andNot (.int .usize) := bitwiseAll_sound _ _ rflTrue

/-- The same from the type-free form: one evaluation, twelve statements. -/
theorem and_not_every : ∀ t, Sound andNot (.int t) := bitwise_sound _ rflTrue

/-- At `bool` the answer is `false` before the rule is read. -/
theorem and_not_bool_false : bitwiseAll andNot .bool = false := rfl

/-- The rule says something at `u64`, from the same `true`. -/
theorem and_not_defined_u64 : Defined andNot (.int .u64) := bitwiseAll_defined _ _ rflTrue
theorem and_not_satisfiable_u64 : Satisfiable andNot (.int .u64) :=
  bitwiseAll_satisfiable _ _ rflTrue

/-- `(or ?x (and ?x ?y)) = ?x`: two variables of the instance type, which
    `exhaust8` answers `false` on for its 65,536 assignments at eight bits. -/
def orAbsorb : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.or (Pat.var (nat_lit 0))
      (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1))))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem or_absorb_u8 : Sound orAbsorb (.int .u8) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_i8 : Sound orAbsorb (.int .i8) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_u16 : Sound orAbsorb (.int .u16) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_u64 : Sound orAbsorb (.int .u64) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_i128 : Sound orAbsorb (.int .i128) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_usize : Sound orAbsorb (.int .usize) := bitwiseAll_sound _ _ rflTrue
theorem or_absorb_exhaust8_false : exhaust8 orAbsorb (.int .u8) = false := rfl

/-- `(xor ?x ?x) = (const 0)`. -/
def xorSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.lit false (nat_lit 0))
    Conds.nil

theorem xor_self_u8 : Sound xorSelf (.int .u8) := bitwiseAll_sound _ _ rflTrue
theorem xor_self_u32 : Sound xorSelf (.int .u32) := bitwiseAll_sound _ _ rflTrue
theorem xor_self_isize : Sound xorSelf (.int .isize) := bitwiseAll_sound _ _ rflTrue
theorem xor_self_bool_false : bitwiseAll xorSelf .bool = false := rfl

/-- `(or ?x (not ?x)) = (const -1)`: the literal -1 is all ones at every
    width. -/
def orNot : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.un UnOp.not (Pat.var (nat_lit 0))))
    (Pat.lit true (nat_lit 1))
    Conds.nil

theorem or_not_u8 : Sound orNot (.int .u8) := bitwiseAll_sound _ _ rflTrue
theorem or_not_u128 : Sound orNot (.int .u128) := bitwiseAll_sound _ _ rflTrue

/-- `(xor ?x (const -1)) = (not ?x)`. -/
def xorOnes : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.lit true (nat_lit 1)))
    (Pat.un UnOp.not (Pat.var (nat_lit 0)))
    Conds.nil

theorem xor_ones_u16 : Sound xorOnes (.int .u16) := bitwiseAll_sound _ _ rflTrue

/-- `(not (and ?x (and ?y ?z)))` refines to
    `(or (not ?x) (or (not ?y) (not ?z)))`: three variables, direction
    `refines`, and `?z` a constant variable read as `(const ?z)`. -/
def deMorgan3 : Rule :=
  Rule.mk Dir.refines
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t true Sorts.nil)))
    (Pat.un UnOp.not
      (Pat.bin BinOp.and (Pat.var (nat_lit 0))
        (Pat.bin BinOp.and (Pat.var (nat_lit 1)) (Pat.cvar (nat_lit 2)))))
    (Pat.bin BinOp.or (Pat.un UnOp.not (Pat.var (nat_lit 0)))
      (Pat.bin BinOp.or (Pat.un UnOp.not (Pat.var (nat_lit 1)))
        (Pat.un UnOp.not (Pat.cvar (nat_lit 2)))))
    Conds.nil

theorem de_morgan3_i64 : Sound deMorgan3 (.int .i64) := bitwiseAll_sound _ _ rflTrue

/-- Eight variables of sort `t`. -/
def sorts8 : Sorts :=
  Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false (Sorts.cons Srt.t false
      (Sorts.cons Srt.t false Sorts.nil)))))))

/-- The `xor` of eight variables, nested to the right in rank order, against
    the same nested to the left in the reverse order: 256 rows, the most
    `bitwiseAll` builds, and no row ends the table early. -/
def eightVars : Rule :=
  Rule.mk Dir.equiv sorts8
    (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.bin BinOp.xor (Pat.var (nat_lit 1))
      (Pat.bin BinOp.xor (Pat.var (nat_lit 2)) (Pat.bin BinOp.xor (Pat.var (nat_lit 3))
        (Pat.bin BinOp.xor (Pat.var (nat_lit 4)) (Pat.bin BinOp.xor (Pat.var (nat_lit 5))
          (Pat.bin BinOp.xor (Pat.var (nat_lit 6)) (Pat.var (nat_lit 7)))))))))
    (Pat.bin BinOp.xor (Pat.bin BinOp.xor (Pat.bin BinOp.xor (Pat.bin BinOp.xor
      (Pat.bin BinOp.xor (Pat.bin BinOp.xor (Pat.bin BinOp.xor (Pat.var (nat_lit 7))
        (Pat.var (nat_lit 6))) (Pat.var (nat_lit 5))) (Pat.var (nat_lit 4)))
          (Pat.var (nat_lit 3))) (Pat.var (nat_lit 2))) (Pat.var (nat_lit 1)))
            (Pat.var (nat_lit 0)))
    Conds.nil

theorem eight_vars_u64 : Sound eightVars (.int .u64) := bitwiseAll_sound _ _ rflTrue

/-- `?a = ?a` beside eight more variables: over `maxBitVars`, `false` before
    a row is built. -/
def nineVars : Rule :=
  Rule.mk Dir.equiv (Sorts.cons Srt.t false sorts8)
    (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)) Conds.nil

theorem nine_vars_false : bitwiseAll nineVars (.int .u64) = false := rfl

/-! ## Literals outside the fragment -/

/-- `(and ?x (const 255)) = ?x`: true at eight bits only. The literal 255 is
    not in the fragment, so the answer is `false` at every type, the two
    eight-bit types included. -/
def and255 : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 255)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem and255_u8_false : bitwiseAll and255 (.int .u8) = false := rfl
theorem and255_i8_false : bitwiseAll and255 (.int .i8) = false := rfl
theorem and255_u16_false : bitwiseAll and255 (.int .u16) = false := rfl
theorem and255_u64_false : bitwiseAll and255 (.int .u64) = false := rfl
theorem and255_bitwise_false : bitwise and255 = false := rfl

/-- And at sixteen bits the rule is false, not only unproved: 256 and 255 is
    0. A procedure that read 255 as all ones would have proved it there. -/
theorem and255_not_sound_u16 : ¬ Sound and255 (.int .u16) := fun h => by
  obtain ⟨v, hl, hr⟩ := h 64 [.int .u16 256] trivial ⟨⟨256, rfl, by decide⟩, trivial⟩ trivial
  have hl' : and255.lhs.eval 64 (.int .u16) [.int .u16 256] = .ok (.int .u16 0) := rfl
  have hr' : and255.rhs.eval 64 (.int .u16) [.int .u16 256] = .ok (.int .u16 256) := rfl
  rw [hl'] at hl
  rw [hr'] at hr
  cases hl
  cases hr

/-- `(and ?x (const 1)) = ?x`: the magnitude of `(const -1)` without its
    sign. -/
def andOne : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem and_one_false : bitwiseAll andOne (.int .u8) = false := rfl

/-- `(or ?x (const -0)) = ?x`: `lit true 0` is zero at every width, and is
    not one of the two literals the fragment admits. -/
def orNegZero : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.lit true (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem or_neg_zero_false : bitwiseAll orNegZero (.int .u8) = false := rfl
theorem or_neg_zero_sound_u8 : Sound orNegZero (.int .u8) := exhaust8_sound _ _ rflTrue

/-! ## Rows that differ -/

/-- `(or ?x ?y) = ?x`: the row x = 0, y = 1 differs. -/
def orDrop : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem or_drop_false : bitwiseAll orDrop (.int .u8) = false := rfl

/-- The rule is false at `u8`: 0 or 1 is 1. -/
theorem or_drop_not_sound_u8 : ¬ Sound orDrop (.int .u8) := fun h => by
  obtain ⟨v, hl, hr⟩ := h 64 [.int .u8 0, .int .u8 1] trivial
    ⟨⟨0, rfl, by decide⟩, ⟨1, rfl, by decide⟩, trivial⟩ trivial
  have hl' : orDrop.lhs.eval 64 (.int .u8) [.int .u8 0, .int .u8 1] = .ok (.int .u8 1) := rfl
  have hr' : orDrop.rhs.eval 64 (.int .u8) [.int .u8 0, .int .u8 1] = .ok (.int .u8 0) := rfl
  rw [hl'] at hl
  rw [hr'] at hr
  cases hl
  cases hr

/-- `(xor ?x ?x) = ?x`: the row x = 1 differs. -/
def xorSelfWrong : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.xor (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem xor_self_wrong_false : bitwiseAll xorSelfWrong (.int .u8) = false := rfl

/-- `(and ?x ?y) = (or ?x ?y)`. -/
def andIsOr : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.t false Sorts.nil))
    (Pat.bin BinOp.and (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    (Pat.bin BinOp.or (Pat.var (nat_lit 0)) (Pat.var (nat_lit 1)))
    Conds.nil

theorem and_is_or_false : bitwiseAll andIsOr (.int .u64) = false := rfl

/-- `(const 0) = (const -1)`: no variable, one row. -/
def zeroIsOnes : Rule :=
  Rule.mk Dir.equiv Sorts.nil (Pat.lit false (nat_lit 0)) (Pat.lit true (nat_lit 1)) Conds.nil

theorem zero_is_ones_false : bitwiseAll zeroIsOnes (.int .u8) = false := rfl

/-! ## Forms outside the fragment -/

/-- `(add ?x (const 0)) = ?x`: `Sound`, and `add` is not in the fragment. -/
def addZero : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.add (Pat.var (nat_lit 0)) (Pat.lit false (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem add_zero_false : bitwiseAll addZero (.int .u8) = false := rfl
theorem add_zero_sound_u8 : Sound addZero (.int .u8) := exhaust8_sound _ _ rflTrue

/-- `(neg (neg ?x)) = ?x`. -/
def negNeg : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.un UnOp.neg (Pat.un UnOp.neg (Pat.var (nat_lit 0))))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem neg_neg_false : bitwiseAll negNeg (.int .u8) = false := rfl

/-- `(band ?x ?x) = ?x`: the Boolean operator on a variable of the instance
    type. -/
def bandSelf : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.bin BinOp.bAnd (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem band_self_false : bitwiseAll bandSelf (.int .u8) = false := rfl

/-- `(select true ?x ?x) = ?x`. -/
def selSame : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.sel Pat.tt (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem sel_same_false : bitwiseAll selSame (.int .u8) = false := rfl

/-- `(icmp.eq ?x ?x) = (icmp.eq ?x ?x)`. -/
def cmpSide : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.cmp ICmpOp.eq (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    (Pat.cmp ICmpOp.eq (Pat.var (nat_lit 0)) (Pat.var (nat_lit 0)))
    Conds.nil

theorem cmp_side_false : bitwiseAll cmpSide (.int .u8) = false := rfl

/-! ## Variables and side conditions -/

/-- `?y = ?y` with `?y` unbound: a side is not a term. -/
def unbound : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false Sorts.nil)
    (Pat.var (nat_lit 1))
    (Pat.var (nat_lit 1))
    Conds.nil

theorem unbound_false : bitwiseAll unbound (.int .u8) = false := rfl

/-- `?x = ?x` beside a variable of sort `bool`. -/
def boolVar : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t false (Sorts.cons Srt.bool false Sorts.nil))
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    Conds.nil

theorem bool_var_false : bitwiseAll boolVar (.int .u8) = false := rfl

/-- `?x = ?x where (ne ?x 0)`: `Sound`, and a rule with a side condition is
    not admitted by this route. -/
def withCond : Rule :=
  Rule.mk Dir.equiv
    (Sorts.cons Srt.t true Sorts.nil)
    (Pat.var (nat_lit 0))
    (Pat.var (nat_lit 0))
    (Conds.cons (Cond.ne (nat_lit 0) false (nat_lit 0)) Conds.nil)

theorem with_cond_false : bitwiseAll withCond (.int .u8) = false := rfl
theorem with_cond_sound_u8 : Sound withCond (.int .u8) := exhaust8_sound _ _ rflTrue

end EqsatBitwiseControls
