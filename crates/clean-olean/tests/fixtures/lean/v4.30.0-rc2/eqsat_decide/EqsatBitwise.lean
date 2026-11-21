/- EqsatBitwise: a rule of bitwise operators decided at every integer type
   from one truth table, and what a `true` proves (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `bitwiseAll r T` is a decision procedure for `EqsatRule.Sound r T`, and
   `bitwiseAll_sound : bitwiseAll r T = true → Sound r T` is its one theorem,
   with no other hypothesis. The proof of a rule a search found is

       EqsatDecide.bitwiseAll_sound <rule literal> <type> EqsatDecide.rflTrue

   the same closed application as `exhaust8_sound <literal> <type> rflTrue`
   with one constant renamed; the kernel accepts it only by evaluating
   `bitwiseAll <literal> <type>` to `true`. Nothing here is trusted and
   nothing here is part of what a rule means: `EqsatRule.Sound` does not
   reach this module, and a wrong `bitwiseAll` has no `bitwiseAll_sound`.

   What `bitwiseAll r T` answers `true` on (the parts named below are in
   `EqsatDecide.Bitwise`). All six must hold:
   * `T` is an integer type, any of the twelve. At `bool` the answer is
     `false` before the rule is read. The answer does not depend on which
     integer type `T` is: `bitwiseAll r (.int t)` is `bitwise r`, so one
     evaluation of the same cost stands at each width, and
     `bitwise_sound : bitwise r = true → ∀ t, Sound r (.int t)` states all
     twelve at once;
   * the rule has no side condition (`noConds`);
   * every variable is of sort `t` (`allT`), and there are at most
     `maxBitVars` (8) of them, so at most 256 rows;
   * the left side is in the fragment and names only bound variables
     (`fragB`): `?v` and `(const ?v)`, `(const 0)` written `lit false 0`,
     `(const -1)` written `lit true 1`, `and`, `or`, `xor`, `not`. Every
     other pattern form, operator and literal answers `false`: `(const 255)`
     is not in the fragment (it is all ones at eight bits only);
   * the right side likewise;
   * on every assignment of one bit to each variable the two sides are the
     same bit (`allBits`, `evalB`): the truth table, `2^k` rows for `k`
     variables.
   The direction is not read: every pattern of the fragment is a value on
   every admitted assignment, so `equiv` and `refines` say the same.

   Why a truth table decides every width (`frag_eval`): at an integer type
   of width `w`, on residues below `2^w`, a pattern of the fragment
   evaluates in SemR to a residue below `2^w` whose bit `j`, for each
   `j < w`, is `evalB` of the pattern on bit `j` of each variable. So when
   the table agrees, the two residues agree on every bit below `w`, both are
   below `2^w`, and they are one residue. No fact about `w` is used: the
   theorem holds at each pointer width, `PbOk` is not read.

   So `false` is not a refutation. It says the rule is not proved by this
   procedure: the type is `bool`, the rule has a side condition, a variable
   of sort `bool`, more than eight variables, a form outside the fragment,
   an unbound variable, or a row that differs. (A rule of the fragment with
   a row that differs is in fact false at every integer type of positive
   width; that is not proved here and nothing relies on it.)
   `bitwiseAll_sound` is the claim; `bitwiseAll_defined` and
   `bitwiseAll_satisfiable` give `Defined` and `EqsatRule.Satisfiable` from
   the same `true`, as `exhaust8`'s do. Completeness is not stated.

   How it is written, and why: as `EqsatResidue`, every definition the
   kernel evaluates is one recursor application with closed minor premises
   (no matcher, no `brecOn`, no instance). The enumeration is `both` per
   variable, nested by a continuation that receives the row; `both` tests
   before it goes on, so the first differing row ends it.
-/
import EqsatExhaust

namespace EqsatDecide
open SemR EqsatRule

/-! The parts of the procedure and the lemmas about them are in
    `EqsatDecide.Bitwise`, so that a sibling procedure of this family may
    name its own parts as it likes; `bitwise`, `bitwiseAll` and their
    theorems are in `EqsatDecide`. -/
namespace Bitwise

noncomputable section

/-- The bit of the variable of rank `i` in a row; `false` where the rank is
    unbound (`fragB` refuses a pattern that reads one). -/
def getB (env : List Bool) (i : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun v _ ih i => Nat.rec (motive := fun _ => Bool) v (fun j _ => ih j) i) env i

/-- `and`, `or`, `xor` on one bit; `false` for every other operator (`fragB`
    refuses it). -/
def binB (op : BinOp) (a b : Bool) : Bool :=
  BinOp.rec (motive := fun _ => Bool)
    false false false false false false false
    (Bool.rec (motive := fun _ => Bool) false b a)
    (Bool.rec (motive := fun _ => Bool) b true a)
    (Bool.rec (motive := fun _ => Bool) b (Bool.rec (motive := fun _ => Bool) true false b) a)
    false false false false false false false false
    op

/-- `not` on one bit; `false` for every other operator (`fragB` refuses
    it). -/
def unB (op : UnOp) (a : Bool) : Bool :=
  UnOp.rec (motive := fun _ => Bool)
    false (Bool.rec (motive := fun _ => Bool) true false a) false false false false false op

/-- A pattern of the fragment on one bit of each variable. `(const 0)` is
    `lit false 0` and `(const -1)` is `lit true 1` (`fragB` admits no other
    literal), so the bit of a literal is its sign flag. -/
def evalB (env : List Bool) (p : Pat) : Bool :=
  Pat.rec (motive := fun _ => Bool)
    (fun i => getB env i)
    (fun i => getB env i)
    (fun neg _ => neg)
    false
    false
    (fun op _ _ a b => binB op a b)
    (fun op _ a => unB op a)
    (fun _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ => false)
    p

/-- `fa` and `fb` for `and`, `or`, `xor`; `false` for every other
    operator. -/
def fragBin (op : BinOp) (fa fb : Bool) : Bool :=
  BinOp.rec (motive := fun _ => Bool)
    false false false false false false false
    (Bool.rec (motive := fun _ => Bool) false fb fa)
    (Bool.rec (motive := fun _ => Bool) false fb fa)
    (Bool.rec (motive := fun _ => Bool) false fb fa)
    false false false false false false false false
    op

/-- `fa` for `not`; `false` for every other operator. -/
def fragUn (op : UnOp) (fa : Bool) : Bool :=
  UnOp.rec (motive := fun _ => Bool) false fa false false false false false op

/-- The pattern is in the fragment and reads only variables of rank below
    `n`: `var`, `cvar`, `lit false 0` (zero), `lit true 1` (all ones), `and`,
    `or`, `xor`, `not`. -/
def fragB (n : Nat) (p : Pat) : Bool :=
  Pat.rec (motive := fun _ => Bool)
    (fun i => Nat.blt i n)
    (fun i => Nat.blt i n)
    (fun neg mag => Bool.rec (motive := fun _ => Bool) (Nat.beq mag 0) (Nat.beq mag 1) neg)
    false
    false
    (fun op _ _ fa fb => fragBin op fa fb)
    (fun op _ fa => fragUn op fa)
    (fun _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ => false)
    p

/-- The rule has no side condition. -/
def noConds (cs : Conds) : Bool :=
  Conds.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs

/-- Every variable is of sort `t`. -/
def allT (s : Sorts) : Bool :=
  Sorts.rec (motive := fun _ => Bool) true
    (fun srt _ _ ih => Srt.rec (motive := fun _ => Bool) ih false srt) s

/-- The number of variables (a literal after evaluation: `Nat.add` on
    literals). -/
def countV (s : Sorts) : Nat :=
  Sorts.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ _ ih => Nat.add ih (nat_lit 1)) s

/-- The most variables `bitwiseAll` builds a truth table for: 256 rows. -/
def maxBitVars : Nat := nat_lit 8

/-- `k` is `true` on every row: one Boolean per variable of `s`. -/
def allBits (s : Sorts) : (List Bool → Bool) → Bool :=
  Sorts.rec (motive := fun _ => (List Bool → Bool) → Bool)
    (fun k => k [])
    (fun _ _ _ ih k => both fun v => ih fun vs => k (v :: vs))
    s

/-- Two bits are the same bit. -/
def eqB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

end

end Bitwise

open Bitwise

noncomputable section

/-- The procedure at an integer type, whichever it is: no side condition,
    every variable of sort `t`, at most `maxBitVars` of them, both sides in
    the fragment, and the two sides the same bit on every row. The first
    `false` is the answer. -/
def bitwise (r : Rule) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun _ vars lhs rhs cs =>
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (Bool.rec (motive := fun _ => Bool) false
                (allBits vars fun env => eqB (evalB env lhs) (evalB env rhs))
                (fragB (countV vars) rhs))
              (fragB (countV vars) lhs))
            (Nat.ble (countV vars) maxBitVars))
          (allT vars))
        (noConds cs))
    r

/-- The procedure: `bitwise` at each of the twelve integer types (the type
    is not read further), `false` at `bool`. -/
def bitwiseAll (r : Rule) (T : STy) : Bool :=
  STy.rec (motive := fun _ => Bool) (fun _ => bitwise r) false T

end

namespace Bitwise

/-! ## What the definitions reduce to -/

theorem getB_nil (i : Nat) : getB [] i = false := rfl
theorem getB_zero (v : Bool) (vs : List Bool) : getB (v :: vs) 0 = v := rfl
theorem getB_succ (v : Bool) (vs : List Bool) (i : Nat) :
    getB (v :: vs) (i + 1) = getB vs i := rfl

theorem binB_and (a b : Bool) : binB .and a b = (a && b) := by cases a <;> rfl
theorem binB_or (a b : Bool) : binB .or a b = (a || b) := by cases a <;> rfl
theorem binB_xor (a b : Bool) : binB .xor a b = (a ^^ b) := by cases a <;> cases b <;> rfl
theorem unB_not (a : Bool) : unB .not a = !a := by cases a <;> rfl

theorem evalB_var (env : List Bool) (i : Nat) : evalB env (.var i) = getB env i := rfl
theorem evalB_cvar (env : List Bool) (i : Nat) : evalB env (.cvar i) = getB env i := rfl
theorem evalB_lit (env : List Bool) (neg : Bool) (mag : Nat) :
    evalB env (.lit neg mag) = neg := rfl
theorem evalB_bin (env : List Bool) (op : BinOp) (a b : Pat) :
    evalB env (.bin op a b) = binB op (evalB env a) (evalB env b) := rfl
theorem evalB_un (env : List Bool) (op : UnOp) (a : Pat) :
    evalB env (.un op a) = unB op (evalB env a) := rfl

theorem fragB_bin (n : Nat) (op : BinOp) (a b : Pat) :
    fragB n (.bin op a b) = fragBin op (fragB n a) (fragB n b) := rfl
theorem fragB_un (n : Nat) (op : UnOp) (a : Pat) :
    fragB n (.un op a) = fragUn op (fragB n a) := rfl

theorem eqB_eq {a b : Bool} (h : eqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion (show false = true from h)

theorem countV_nil : countV .nil = 0 := rfl
theorem countV_cons (srt : Srt) (c : Bool) (rest : Sorts) :
    countV (.cons srt c rest) = countV rest + 1 := rfl

/-! ## One bit of a residue is the pattern on one bit of each variable -/

/-- A bound variable: its value is one of the residues, and its bit in row
    `j` is bit `j` of that residue. -/
theorem getVar_bits {t : IntTy} {m : Nat} :
    ∀ (xs : List Nat) (i : Nat), i < xs.length → (∀ x, x ∈ xs → x < m) →
      ∃ x, x < m ∧ getVar (xs.map (Val.int t)) i = .ok (.int t x) ∧
        ∀ j, getB (xs.map fun y => y.testBit j) i = x.testBit j
  | [], i, h, _ => absurd h (Nat.not_lt_zero i)
  | x :: _, 0, _, hall => ⟨x, hall x List.mem_cons_self, rfl, fun _ => rfl⟩
  | _ :: xs, i + 1, h, hall =>
    getVar_bits xs i (Nat.lt_of_succ_lt_succ h) fun x hx => hall x (List.mem_cons_of_mem _ hx)

/-- The adequacy of the bit evaluator. At an integer type `t` under pointer
    width `pb`, on residues below the modulus, a pattern of the fragment that
    reads only bound variables is a value in SemR's own evaluation: a residue
    below the modulus whose bit `j`, for every `j` below the width, is
    `evalB` of the pattern on bit `j` of each variable. -/
theorem frag_eval {pb : Nat} {t : IntTy} {xs : List Nat}
    (hall : ∀ x, x ∈ xs → x < modulus (t.bits pb)) (p : Pat)
    (hf : fragB xs.length p = true) :
    ∃ r, r < modulus (t.bits pb) ∧
      p.eval pb (.int t) (xs.map (Val.int t)) = .ok (.int t r) ∧
      ∀ j, j < t.bits pb → r.testBit j = evalB (xs.map fun y => y.testBit j) p := by
  induction p with
  | var i =>
    have hi : i < xs.length := Nat.blt_eq.mp hf
    obtain ⟨x, hx, hv, hb⟩ := getVar_bits (t := t) xs i hi hall
    exact ⟨x, hx, hv, fun j _ => (hb j).symm⟩
  | cvar i =>
    have hi : i < xs.length := Nat.blt_eq.mp hf
    obtain ⟨x, hx, hv, hb⟩ := getVar_bits (t := t) xs i hi hall
    exact ⟨x, hx, hv, fun j _ => (hb j).symm⟩
  | lit neg mag =>
    cases neg with
    | false =>
      have hm : mag = 0 := Nat.eq_of_beq_eq_true hf
      subst hm
      refine ⟨0, modulus_pos _, ?_, fun j _ => ?_⟩
      · show R.ok (Val.int t (0 % modulus (t.bits pb))) = _
        rw [Nat.zero_mod]
      · rw [Nat.zero_testBit, evalB_lit]
    | true =>
      have hm : mag = 1 := Nat.eq_of_beq_eq_true hf
      subst hm
      refine ⟨2 ^ t.bits pb - 1, ?_, ?_, fun j hj => ?_⟩
      · have := modulus_pos (t.bits pb)
        show 2 ^ t.bits pb - 1 < 2 ^ t.bits pb
        exact Nat.sub_lt this (by decide)
      · show R.ok (Val.int t (litR (t.bits pb) true 1)) = _
        rw [litR_neg_one]
      · rw [Nat.testBit_two_pow_sub_one, evalB_lit]
        exact decide_eq_true hj
  | tt => exact Bool.noConfusion (show false = true from hf)
  | ff => exact Bool.noConfusion (show false = true from hf)
  | bin op a b iha ihb =>
    rw [fragB_bin] at hf
    have key : ∀ (f : Nat → Nat → Nat) (g : Bool → Bool → Bool),
        fragB xs.length a = true → fragB xs.length b = true →
        (∀ x y, x < modulus (t.bits pb) → y < modulus (t.bits pb) →
          evalBinop pb op (binTy (.int t) op) (.int t x) (.int t y) =
            .ok (.int t (f x y % modulus (t.bits pb)))) →
        (∀ x y j, (f x y).testBit j = g (x.testBit j) (y.testBit j)) →
        (∀ u v, binB op u v = g u v) →
        ∃ r, r < modulus (t.bits pb) ∧
          (Pat.bin op a b).eval pb (.int t) (xs.map (Val.int t)) = .ok (.int t r) ∧
          ∀ j, j < t.bits pb →
            r.testBit j = evalB (xs.map fun y => y.testBit j) (.bin op a b) := by
      intro f g ha hb hev hbit hg
      obtain ⟨ra, hra, hea, hba⟩ := iha ha
      obtain ⟨rb, hrb, heb, hbb⟩ := ihb hb
      refine ⟨f ra rb % modulus (t.bits pb), mod_modulus_lt _ _, ?_, fun j hj => ?_⟩
      · show ((a.eval pb (.int t) _).bind fun x => (b.eval pb (.int t) _).bind fun y =>
          evalBinop pb op (binTy (.int t) op) x y) = _
        rw [hea, heb]
        exact hev ra rb hra hrb
      · show (f ra rb % 2 ^ t.bits pb).testBit j = _
        rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, hbit, evalB_bin, hg,
          hba j hj, hbb j hj]
    cases op
    case and =>
      obtain ⟨ha, hb⟩ := guard_true hf
      refine key Nat.land (fun u v => u && v) ha hb (fun x y hx hy => ?_)
        (fun x y j => Nat.testBit_and x y j) binB_and
      show evalBinop pb .and (.int t) (.int t x) (.int t y) = _
      rw [evalBinop_int hx hy]; rfl
    case or =>
      obtain ⟨ha, hb⟩ := guard_true hf
      refine key Nat.lor (fun u v => u || v) ha hb (fun x y hx hy => ?_)
        (fun x y j => Nat.testBit_or x y j) binB_or
      show evalBinop pb .or (.int t) (.int t x) (.int t y) = _
      rw [evalBinop_int hx hy]; rfl
    case xor =>
      obtain ⟨ha, hb⟩ := guard_true hf
      refine key Nat.xor (fun u v => u ^^ v) ha hb (fun x y hx hy => ?_)
        (fun x y j => Nat.testBit_xor x y j) binB_xor
      show evalBinop pb .xor (.int t) (.int t x) (.int t y) = _
      rw [evalBinop_int hx hy]; rfl
    all_goals exact Bool.noConfusion (show false = true from hf)
  | un op a iha =>
    rw [fragB_un] at hf
    cases op
    case not =>
      obtain ⟨ra, hra, hea, hba⟩ := iha hf
      have hra' : ra < 2 ^ t.bits pb := hra
      refine ⟨2 ^ t.bits pb - (ra + 1), ?_, ?_, fun j hj => ?_⟩
      · show 2 ^ t.bits pb - (ra + 1) < 2 ^ t.bits pb
        omega
      · show ((a.eval pb (.int t) _).bind fun x => evalUnop pb .not (.int t) x) = _
        rw [hea]
        show evalUnop pb .not (.int t) (.int t ra) = _
        rw [evalUnop_int hra]
        show R.ok (Val.int t (2 ^ t.bits pb - 1 - ra % 2 ^ t.bits pb)) = _
        rw [Nat.mod_eq_of_lt hra', Nat.sub_sub, Nat.add_comm 1 ra]
      · rw [Nat.testBit_two_pow_sub_succ hra', decide_eq_true hj, Bool.true_and, evalB_un,
          unB_not, hba j hj]
    all_goals exact Bool.noConfusion (show false = true from hf)
  | cmp op a b _ _ => exact Bool.noConfusion (show false = true from hf)
  | sel c a b _ _ _ => exact Bool.noConfusion (show false = true from hf)

/-! ## The rows, and the assignments the variables admit -/

/-- A `true` of `allBits s k` is `k` at every row of one Boolean per
    variable. -/
theorem allBits_spec :
    ∀ (s : Sorts) (k : List Bool → Bool), allBits s k = true →
      ∀ bs : List Bool, bs.length = countV s → k bs = true := by
  intro s
  induction s with
  | nil =>
    intro k h bs hlen
    cases bs with
    | nil => exact h
    | cons b bs => exact absurd hlen (by simp [countV_nil])
  | cons srt c rest ih =>
    intro k h bs hlen
    cases bs with
    | nil => exact absurd hlen (by simp [countV_cons])
    | cons b bs =>
      have h1 : both (fun v => allBits rest fun vs => k (v :: vs)) = true := h
      rw [countV_cons] at hlen
      exact ih (fun vs => k (b :: vs)) (both_spec h1 b) bs (by simpa using hlen)

/-- Where every variable is of sort `t`, an assignment the variables admit at
    an integer type is one residue below the modulus per variable. -/
theorem admits_allT {pb : Nat} {t : IntTy} :
    ∀ (s : Sorts) (env : List Val), allT s = true → Admits pb (.int t) s env →
      ∃ xs : List Nat, env = xs.map (Val.int t) ∧ xs.length = countV s ∧
        ∀ x, x ∈ xs → x < modulus (t.bits pb) := by
  intro s
  induction s with
  | nil =>
    intro env _ hadm
    rw [admits_nil] at hadm
    subst hadm
    exact ⟨[], rfl, rfl, fun x hx => absurd hx (List.not_mem_nil)⟩
  | cons srt c rest ih =>
    intro env ht hadm
    cases srt with
    | bool => exact Bool.noConfusion (show false = true from ht)
    | t =>
      obtain ⟨x, vs, rfl, hx, hrest⟩ := admits_cons_t_int.mp hadm
      obtain ⟨xs, rfl, hlen, hall⟩ := ih vs ht hrest
      refine ⟨x :: xs, rfl, ?_, fun y hy => ?_⟩
      · rw [countV_cons, List.length_cons, hlen]
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hall y hy

end Bitwise

/-! ## What a `true` proves -/

/-- The tests of a `bitwise` that answered `true`. -/
theorem bitwise_parts {d : Dir} {vars : Sorts} {lhs rhs : Pat} {cs : Conds}
    (h : bitwise (Rule.mk d vars lhs rhs cs) = true) :
    noConds cs = true ∧ allT vars = true ∧ fragB (countV vars) lhs = true ∧
      fragB (countV vars) rhs = true ∧
      allBits vars (fun env => eqB (evalB env lhs) (evalB env rhs)) = true := by
  obtain ⟨h1, h⟩ := guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
  obtain ⟨h2, h⟩ := guard_true h
  obtain ⟨_, h⟩ := guard_true h
  obtain ⟨h4, h⟩ := guard_true h
  obtain ⟨h5, h⟩ := guard_true h
  exact ⟨h1, h2, h4, h5, h⟩

/-- What a `true` of `bitwise` proves of one admitted assignment at an
    integer type, at any pointer width: both sides are one common value. -/
theorem bitwise_value {pb : Nat} {t : IntTy} (r : Rule) (h : bitwise r = true) (env : List Val)
    (hadm : Admits pb (.int t) r.vars env) :
    ∃ v, r.lhs.eval pb (.int t) env = .ok v ∧ r.rhs.eval pb (.int t) env = .ok v := by
  cases r with
  | mk d vars lhs rhs cs =>
    obtain ⟨_, ht, hfl, hfr, hrows⟩ := bitwise_parts h
    obtain ⟨xs, rfl, hlen, hall⟩ := admits_allT vars env ht hadm
    rw [← hlen] at hfl hfr
    obtain ⟨rl, hrl, hel, hbl⟩ := frag_eval hall lhs hfl
    obtain ⟨rr, hrr, her, hbr⟩ := frag_eval hall rhs hfr
    have heq : rl = rr := by
      refine Nat.eq_of_testBit_eq fun j => ?_
      by_cases hj : j < t.bits pb
      · rw [hbl j hj, hbr j hj]
        exact eqB_eq (allBits_spec vars _ hrows (xs.map fun y => y.testBit j)
          (by rw [List.length_map, hlen]))
      · have hpow : 2 ^ t.bits pb ≤ 2 ^ j :=
          Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj)
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hrl hpow),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hrr hpow)]
    subst heq
    exact ⟨.int t rl, hel, her⟩

/-- One truth table proves the rule at every integer type: a rule on which
    `bitwise` answers `true` is `Sound` at each of the twelve. -/
theorem bitwise_sound (r : Rule) (h : bitwise r = true) (t : IntTy) : Sound r (.int t) := by
  intro pb env _ hadm _
  obtain ⟨v, hl, hr⟩ := bitwise_value r h env hadm
  rw [hl, hr]
  cases r.dir
  · exact ⟨v, rfl, rfl⟩
  · exact .inr ⟨v, rfl, rfl⟩

/-- `bitwiseAll` answers `true` only at an integer type, and there it is
    `bitwise`, whichever the type. At `bool` it is `false` whatever the
    rule. -/
theorem bitwiseAll_run {r : Rule} {T : STy} (h : bitwiseAll r T = true) :
    ∃ t, T = .int t ∧ bitwise r = true := by
  cases T with
  | int t => exact ⟨t, rfl, h⟩
  | bool => exact Bool.noConfusion (show false = true from h)

/-- The soundness of the procedure, with no other hypothesis: a rule on
    which `bitwiseAll` answers `true` at `T` is `Sound` at `T`. -/
theorem bitwiseAll_sound (r : Rule) (T : STy) (h : bitwiseAll r T = true) : Sound r T := by
  obtain ⟨t, rfl, hb⟩ := bitwiseAll_run h
  exact bitwise_sound r hb t

/-! ## The rule says something -/

namespace Bitwise

/-- Where every variable is of sort `t`, some assignment is admitted at an
    integer type: every variable zero. -/
theorem admits_some {pb : Nat} {t : IntTy} :
    ∀ (s : Sorts), allT s = true → ∃ env, Admits pb (.int t) s env := by
  intro s
  induction s with
  | nil => exact fun _ => ⟨[], trivial⟩
  | cons srt c rest ih =>
    intro ht
    cases srt with
    | bool => exact Bool.noConfusion (show false = true from ht)
    | t =>
      obtain ⟨env, henv⟩ := ih ht
      exact ⟨.int t 0 :: env, ⟨0, rfl, modulus_pos _⟩, henv⟩

/-- No side condition, so the side conditions hold of every assignment. -/
theorem condsHold_of_noConds {pb : Nat} {T : STy} {env : List Val} :
    ∀ (cs : Conds), noConds cs = true → CondsHold pb T env cs
  | .nil, _ => trivial
  | .cons _ _, h => Bool.noConfusion (show false = true from h)

end Bitwise

/-- A rule on which `bitwiseAll` answers `true` at `T` says something there
    (`Defined`, `EqsatExhaust`): some admitted assignment satisfies its side
    conditions (it has none) and both sides are one common value on it. They
    are on every admitted assignment (`bitwise_value`). -/
theorem bitwiseAll_defined (r : Rule) (T : STy) (h : bitwiseAll r T = true) : Defined r T := by
  obtain ⟨t, rfl, hb⟩ := bitwiseAll_run h
  intro pb _
  cases r with
  | mk d vars lhs rhs cs =>
    obtain ⟨hc, ht, _⟩ := bitwise_parts hb
    obtain ⟨env, hadm⟩ := admits_some (pb := pb) (t := t) vars ht
    obtain ⟨v, hl, hr⟩ := bitwise_value (Rule.mk d vars lhs rhs cs) hb env hadm
    exact ⟨env, v, hadm, condsHold_of_noConds cs hc, hl, hr⟩

/-- A rule on which `bitwiseAll` answers `true` at `T` has side conditions
    some assignment satisfies there (the first half of `bitwiseAll_defined`,
    in the `eqsat_rules` family's own statement). -/
theorem bitwiseAll_satisfiable (r : Rule) (T : STy) (h : bitwiseAll r T = true) :
    Satisfiable r T := by
  intro pb hpb
  obtain ⟨env, _, hadm, hc, _⟩ := bitwiseAll_defined r T h pb hpb
  exact ⟨env, hadm, hc⟩

end EqsatDecide
