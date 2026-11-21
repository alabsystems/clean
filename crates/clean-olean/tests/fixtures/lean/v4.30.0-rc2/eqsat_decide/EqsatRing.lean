/- EqsatRing: a ring rule decided at every integer type from one normal form,
   and what a `true` proves (PKG-U6b).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `ringAll r T` is a decision procedure for `EqsatRule.Sound r T`, and
   `ringAll_sound : ringAll r T = true → Sound r T` is its one theorem, with
   no other hypothesis. The proof of a rule a search found is

       EqsatDecide.ringAll_sound <rule literal> <type> EqsatDecide.rflTrue

   with `rflTrue : true = true` of `EqsatExhaust`. Its type is
   `Sound <literal> <type>` only if `ringAll <literal> <type>` and `true` are
   one term up to evaluation, so the kernel accepts it only by evaluating the
   procedure on the literal. Nothing here is trusted and nothing here is part
   of what a rule means: `EqsatRule.Sound` does not reach this module, and a
   wrong `ringAll` has no `ringAll_sound`.

   What `ringAll r T` answers `true` on. All four must hold:
   * `T` is an integer type, any of the twelve. At `bool` the answer is
     `false` before the rule is read (`ringAll_bool`). At an integer type the
     answer does not depend on the type (`ringAll_int`): one evaluation of
     `RingAll.ringRun r` is the answer at all twelve, and
     `RingAll.ringRun_sound` states that form;
   * the rule has no side condition (`Conds.nil`);
   * both sides are in the ring fragment over the rule's variables
     (`RingAll.ringPat`): `?v` and `(const ?v)` for a variable of sort `t`
     that the rule binds, `(const INT)` for any integer, `add`, `sub`, `mul`,
     `neg` and `not`. Every other pattern form and operator, a variable of
     sort `bool` and an unbound variable make the answer `false`;
   * the two sides are one polynomial with integer coefficients in the rule's
     variables (`RingAll.ringNorm`, compared by `RingAll.Polyn.beq`).
     `(const INT)` is the integer `INT`, and `(not a)` is `-a - 1`.

   The direction is not read: every operator of the fragment is total, so on
   every admitted assignment both sides are one common value
   (`RingAll.ringRun_value`), which is what `equiv` asks and more than
   `refines` asks. For the same reason a rule this procedure admits says
   something at `T`: `ringAll_defined` gives `EqsatDecide.Defined r T` and
   `ringAll_satisfiable` gives `EqsatRule.Satisfiable r T` from the same
   `true`.

   So `false` is not a refutation. It says the rule is not proved by this
   procedure: the type is `bool`, the rule has a side condition, a side is
   outside the fragment, or the two sides are different polynomials over the
   integers. The last includes every rule that holds only modulo the type's
   modulus: `(mul ?x (const 256)) = (const 0)` is `Sound` at `u8` and
   `ringAll` answers `false` on it (`EqsatRingControls`). `ringAll_sound` is
   the only claim; completeness is not stated, and neither is it stated that
   `ringNorm` is a normal form: the proof needs only that a pattern's
   polynomial has the pattern's value (`RingAll.ringPat_norm`).

   Why it is sound. At an integer type of width `w` (whatever `w` is: the
   pointer width of `isize` and `usize` is not constrained here) SemR's
   `add sub mul neg not` on residues below `2^w` are, modulo `2^w`, the
   operations of the integers (`RingAll.res_add` and its siblings). So the
   residue of a pattern of the fragment is, modulo `2^w`, the value of its
   polynomial at the assignment's residues (`RingAll.ringPat_norm`: each
   operation on polynomials has the value of the operation on integers,
   `RingAll.Polyn.den_plus` and its siblings). Two sides with one polynomial
   then have residues that are one integer modulo `2^w`, and two residues
   below `2^w` that are one integer modulo `2^w` are one residue
   (`RingAll.res_inj`). Signed and unsigned types of one width share the
   argument, as SemR gives them one residue arithmetic.

   How it is written, and why: as `EqsatResidue`, every definition of this
   module that the kernel evaluates is one recursor application with closed
   minor premises: no matcher, no `brecOn`, no fuel and no counter. A monomial is the ascending
   list of its variables' ranks and a polynomial the list of its terms in
   the order `Mono.cmp` gives; a sum inserts each term of one polynomial into
   the other, and a product does so for each pair of terms. The cost grows
   with the number of terms of the expanded sides (a product of polynomials
   of `k` and `l` terms is `k * l` insertions) and no size is refused: a rule
   whose expansion is too large for the budget runs out of it, which admits
   nothing. Coefficients are `Int`, by core's `Int.add`, `Int.mul` and
   `Int.neg` (compiled matches) and `Int.beq'`.

   Lean's own normalizer (`Lean.Grind.CommRing.Expr.toPoly_k`) proves the
   same theorem and was measured beside this one under the pinned Lean: a
   check costs three to six times the kernel time, and the cone of the
   soundness theorem holds 1,275 declarations that `exhaust8_sound`'s does
   not (`Lean.Grind`, `BitVec`), against 137 here. It is not used.
-/
import EqsatExhaust

namespace EqsatDecide
open SemR EqsatRule

namespace RingAll

/-- A monomial: the ranks of its variables in ascending order, a variable
    repeated once for each power. -/
inductive Mono where
  | one
  | mul (x : Nat) (m : Mono)

/-- A polynomial with integer coefficients: its terms. As `ringNorm` builds
    it, the monomials ascend in the order `Mono.cmp` gives, none occurs
    twice and no coefficient is 0; no proof here reads that. -/
inductive Polyn where
  | zero
  | add (c : Int) (m : Mono) (p : Polyn)

noncomputable section

/-- The variable of rank `i` is of sort `t`; `false` for a variable of sort
    `bool` and for an unbound rank. -/
def isT (s : Sorts) : Nat → Bool :=
  Sorts.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun srt _ _ ih i =>
      Nat.rec (motive := fun _ => Bool) (Srt.rec (motive := fun _ => Bool) true false srt)
        (fun j _ => ih j) i)
    s

/-- The pattern is in the ring fragment over the variables `s`: variables of
    sort `t`, integer literals, `add sub mul neg not`. -/
def ringPat (s : Sorts) (p : Pat) : Bool :=
  Pat.rec (motive := fun _ => Bool)
    (fun i => isT s i)
    (fun i => isT s i)
    (fun _ _ => true)
    false
    false
    (fun op _ _ ia ib =>
      BinOp.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false ib ia)
        (Bool.rec (motive := fun _ => Bool) false ib ia)
        (Bool.rec (motive := fun _ => Bool) false ib ia)
        false false false false false false false false false false false false false false false
        op)
    (fun op _ ia =>
      UnOp.rec (motive := fun _ => Bool) ia ia false false false false false op)
    (fun _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ => false)
    p

/-- The monomial times the variable `x`. -/
def Mono.ins (x : Nat) (m : Mono) : Mono :=
  Mono.rec (motive := fun _ => Mono) (.mul x .one)
    (fun y ys ih =>
      Bool.rec (motive := fun _ => Mono) (.mul y ih) (.mul x (.mul y ys)) (Nat.ble x y))
    m

/-- The product of two monomials. -/
def Mono.times (a b : Mono) : Mono :=
  Mono.rec (motive := fun _ => Mono) b (fun x _ ih => Mono.ins x ih) a

/-- An order of monomials; `eq` only for one monomial (`Mono.cmp_eq`). -/
def Mono.cmp (a : Mono) : Mono → Ordering :=
  Mono.rec (motive := fun _ => Mono → Ordering)
    (fun b => Mono.rec (motive := fun _ => Ordering) .eq (fun _ _ _ => .lt) b)
    (fun x _ ih b =>
      Mono.rec (motive := fun _ => Ordering) .gt
        (fun y ys _ =>
          Bool.rec (motive := fun _ => Ordering)
            (Bool.rec (motive := fun _ => Ordering) (ih ys) .gt (Nat.blt y x)) .lt (Nat.blt x y))
        b)
    a

/-- The polynomial plus the term `c * m`: before the first greater monomial,
    or into the term of the same monomial, which is dropped when its
    coefficient becomes 0. -/
def Polyn.ins (c : Int) (m : Mono) (p : Polyn) : Polyn :=
  Polyn.rec (motive := fun _ => Polyn) (.add c m .zero)
    (fun c' m' p' ih =>
      Ordering.rec (motive := fun _ => Polyn)
        (.add c m (.add c' m' p'))
        (Bool.rec (motive := fun _ => Polyn) (.add (Int.add c c') m p') p'
          (Int.beq' (Int.add c c') (Int.ofNat (nat_lit 0))))
        (.add c' m' ih)
        (Mono.cmp m m'))
    p

/-- The polynomial plus the term `c * m`; the polynomial itself when `c` is
    0. -/
def Polyn.term (c : Int) (m : Mono) (p : Polyn) : Polyn :=
  Bool.rec (motive := fun _ => Polyn) (Polyn.ins c m p) p (Int.beq' c (Int.ofNat (nat_lit 0)))

/-- The sum of two polynomials. -/
def Polyn.plus (p q : Polyn) : Polyn :=
  Polyn.rec (motive := fun _ => Polyn) q (fun c m _ ih => Polyn.term c m ih) p

/-- The polynomial times the term `c * m`. -/
def Polyn.scale (c : Int) (m : Mono) (q : Polyn) : Polyn :=
  Polyn.rec (motive := fun _ => Polyn) .zero
    (fun c' m' _ ih => Polyn.term (Int.mul c c') (Mono.times m m') ih) q

/-- The product of two polynomials. -/
def Polyn.times (p q : Polyn) : Polyn :=
  Polyn.rec (motive := fun _ => Polyn) .zero
    (fun c m _ ih => Polyn.plus (Polyn.scale c m q) ih) p

/-- The polynomial negated. -/
def Polyn.negate (p : Polyn) : Polyn :=
  Polyn.rec (motive := fun _ => Polyn) .zero (fun c m _ ih => .add (Int.neg c) m ih) p

/-- Two polynomials are one list of terms. -/
def Polyn.beq (p : Polyn) : Polyn → Bool :=
  Polyn.rec (motive := fun _ => Polyn → Bool)
    (fun q => Polyn.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false) q)
    (fun c m _ ih q =>
      Polyn.rec (motive := fun _ => Bool) false
        (fun c' m' q' _ =>
          Bool.rec (motive := fun _ => Bool) false
            (Ordering.rec (motive := fun _ => Bool) false (ih q') false (Mono.cmp m m'))
            (Int.beq' c c'))
        q)
    p

/-- The polynomial of a pattern of the fragment: the variable of rank `i`
    is the variable `i`, `(const INT)` is the integer `INT`, and `(not a)` is
    `-a - 1`. Outside the fragment the polynomial is not read (`ringPat`
    answers `false` first); the first operand's, or 0, fills the place. -/
def ringNorm (p : Pat) : Polyn :=
  Pat.rec (motive := fun _ => Polyn)
    (fun i => .add (Int.ofNat (nat_lit 1)) (.mul i .one) .zero)
    (fun i => .add (Int.ofNat (nat_lit 1)) (.mul i .one) .zero)
    (fun neg mag =>
      Polyn.term
        (Bool.rec (motive := fun _ => Int) (Int.ofNat mag) (Int.neg (Int.ofNat mag)) neg) .one
        .zero)
    .zero
    .zero
    (fun op _ _ pa pb =>
      BinOp.rec (motive := fun _ => Polyn)
        (Polyn.plus pa pb) (Polyn.plus pa (Polyn.negate pb)) (Polyn.times pa pb)
        pa pa pa pa pa pa pa pa pa pa pa pa pa pa pa
        op)
    (fun op _ pa =>
      UnOp.rec (motive := fun _ => Polyn)
        (Polyn.negate pa)
        (Polyn.plus (Polyn.negate pa) (.add (Int.negSucc (nat_lit 0)) .one .zero))
        pa pa pa pa pa op)
    (fun _ _ _ pa _ => pa)
    (fun _ _ _ _ pa _ => pa)
    p

/-- No side condition, both sides in the fragment, one polynomial; the first
    `false` is the answer. The direction is not read. -/
def ringRun (r : Rule) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun _ vars lhs rhs cs =>
      Conds.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            ((ringNorm lhs).beq (ringNorm rhs))
            (ringPat vars rhs))
          (ringPat vars lhs))
        (fun _ _ _ => false)
        cs)
    r

end

end RingAll

/-- The procedure: `RingAll.ringRun` at every integer type, `false` at
    `bool`. -/
noncomputable def ringAll (r : Rule) (T : STy) : Bool :=
  STy.rec (motive := fun _ => Bool) (fun _ => RingAll.ringRun r) false T

namespace RingAll

/-! ## What a polynomial denotes -/

/-- The value of a monomial at an assignment of integers. -/
def Mono.den (ρ : Nat → Int) : Mono → Int
  | .one => 1
  | .mul x m => ρ x * m.den ρ

/-- The value of a polynomial at an assignment of integers. -/
def Polyn.den (ρ : Nat → Int) : Polyn → Int
  | .zero => 0
  | .add c m p => c * m.den ρ + p.den ρ

theorem Mono.ins_mul (x y : Nat) (ys : Mono) :
    Mono.ins x (.mul y ys) =
      Bool.rec (motive := fun _ => Mono) (.mul y (Mono.ins x ys)) (.mul x (.mul y ys))
        (Nat.ble x y) := rfl

theorem Mono.den_ins (ρ : Nat → Int) (x : Nat) :
    ∀ (m : Mono), (Mono.ins x m).den ρ = ρ x * m.den ρ
  | .one => rfl
  | .mul y ys => by
    rw [Mono.ins_mul]
    cases Nat.ble x y
    · show ρ y * (Mono.ins x ys).den ρ = ρ x * (ρ y * ys.den ρ)
      rw [Mono.den_ins ρ x ys, Int.mul_left_comm]
    · rfl

theorem Mono.den_times (ρ : Nat → Int) (b : Mono) :
    ∀ (a : Mono), (Mono.times a b).den ρ = a.den ρ * b.den ρ
  | .one => (Int.one_mul _).symm
  | .mul x xs => by
    show (Mono.ins x (Mono.times xs b)).den ρ = ρ x * xs.den ρ * b.den ρ
    rw [Mono.den_ins, Mono.den_times ρ b xs, Int.mul_assoc]

/-- Two monomials `Mono.cmp` calls equal are one monomial. -/
theorem Mono.cmp_eq : ∀ (a b : Mono), Mono.cmp a b = .eq → a = b
  | .one, .one, _ => rfl
  | .one, .mul _ _, h => Ordering.noConfusion (show Ordering.lt = .eq from h)
  | .mul _ _, .one, h => Ordering.noConfusion (show Ordering.gt = .eq from h)
  | .mul x xs, .mul y ys, h => by
    have h' : Bool.rec (motive := fun _ => Ordering)
        (Bool.rec (motive := fun _ => Ordering) (Mono.cmp xs ys) .gt (Nat.blt y x)) .lt
        (Nat.blt x y) = .eq := h
    cases hxy : Nat.blt x y with
    | true => rw [hxy] at h'; exact Ordering.noConfusion h'
    | false =>
      rw [hxy] at h'
      cases hyx : Nat.blt y x with
      | true => rw [hyx] at h'; exact Ordering.noConfusion h'
      | false =>
        rw [hyx] at h'
        have h1 : ¬ x < y := fun hlt => by
          rw [← Nat.blt_eq] at hlt; rw [hlt] at hxy; exact Bool.noConfusion hxy
        have h2 : ¬ y < x := fun hlt => by
          rw [← Nat.blt_eq] at hlt; rw [hlt] at hyx; exact Bool.noConfusion hyx
        have hx : x = y := by omega
        rw [hx, Mono.cmp_eq xs ys h']

/-- A coefficient `Int.beq'` calls 0 is 0. -/
theorem beq_zero {c : Int} (h : Int.beq' c (Int.ofNat (nat_lit 0)) = true) : c = 0 := by
  rw [Int.beq'_eq] at h
  exact h

theorem Polyn.ins_add (c : Int) (m : Mono) (c' : Int) (m' : Mono) (p' : Polyn) :
    Polyn.ins c m (.add c' m' p') =
      Ordering.rec (motive := fun _ => Polyn)
        (.add c m (.add c' m' p'))
        (Bool.rec (motive := fun _ => Polyn) (.add (Int.add c c') m p') p'
          (Int.beq' (Int.add c c') (Int.ofNat (nat_lit 0))))
        (.add c' m' (Polyn.ins c m p'))
        (Mono.cmp m m') := rfl

theorem Polyn.den_ins (ρ : Nat → Int) (c : Int) (m : Mono) :
    ∀ (p : Polyn), (Polyn.ins c m p).den ρ = c * m.den ρ + p.den ρ
  | .zero => rfl
  | .add c' m' p' => by
    rw [Polyn.ins_add]
    cases hcmp : Mono.cmp m m' with
    | lt => rfl
    | eq =>
      have hm : m = m' := Mono.cmp_eq m m' hcmp
      subst hm
      show (Bool.rec (motive := fun _ => Polyn) (.add (Int.add c c') m p') p'
        (Int.beq' (Int.add c c') (Int.ofNat (nat_lit 0)))).den ρ =
          c * m.den ρ + (c' * m.den ρ + p'.den ρ)
      rw [← Int.add_assoc, ← Int.add_mul]
      cases hz : Int.beq' (Int.add c c') (Int.ofNat (nat_lit 0)) with
      | false => rfl
      | true =>
        have h0 : c + c' = 0 := beq_zero hz
        show p'.den ρ = _
        rw [h0, Int.zero_mul, Int.zero_add]
    | gt =>
      show c' * m'.den ρ + (Polyn.ins c m p').den ρ = c * m.den ρ + (c' * m'.den ρ + p'.den ρ)
      rw [Polyn.den_ins ρ c m p', Int.add_left_comm]

theorem Polyn.den_term (ρ : Nat → Int) (c : Int) (m : Mono) (p : Polyn) :
    (Polyn.term c m p).den ρ = c * m.den ρ + p.den ρ := by
  show (Bool.rec (motive := fun _ => Polyn) (Polyn.ins c m p) p
    (Int.beq' c (Int.ofNat (nat_lit 0)))).den ρ = _
  cases hz : Int.beq' c (Int.ofNat (nat_lit 0)) with
  | false => exact Polyn.den_ins ρ c m p
  | true =>
    have h0 : c = 0 := beq_zero hz
    show p.den ρ = _
    rw [h0, Int.zero_mul, Int.zero_add]

/-- The sum of two polynomials has the sum of their values. -/
theorem Polyn.den_plus (ρ : Nat → Int) (q : Polyn) :
    ∀ (p : Polyn), (Polyn.plus p q).den ρ = p.den ρ + q.den ρ
  | .zero => (Int.zero_add _).symm
  | .add c m p => by
    show (Polyn.term c m (Polyn.plus p q)).den ρ = c * m.den ρ + p.den ρ + q.den ρ
    rw [Polyn.den_term, Polyn.den_plus ρ q p, Int.add_assoc]

theorem Polyn.den_scale (ρ : Nat → Int) (c : Int) (m : Mono) :
    ∀ (q : Polyn), (Polyn.scale c m q).den ρ = c * m.den ρ * q.den ρ
  | .zero => (Int.mul_zero _).symm
  | .add c' m' q => by
    show (Polyn.term (Int.mul c c') (Mono.times m m') (Polyn.scale c m q)).den ρ =
      c * m.den ρ * (c' * m'.den ρ + q.den ρ)
    rw [Polyn.den_term, Polyn.den_scale ρ c m q, Mono.den_times, Int.mul_add]
    congr 1
    show c * c' * (m.den ρ * m'.den ρ) = c * m.den ρ * (c' * m'.den ρ)
    simp only [Int.mul_assoc, Int.mul_left_comm]

/-- The product of two polynomials has the product of their values. -/
theorem Polyn.den_times (ρ : Nat → Int) (q : Polyn) :
    ∀ (p : Polyn), (Polyn.times p q).den ρ = p.den ρ * q.den ρ
  | .zero => (Int.zero_mul _).symm
  | .add c m p => by
    show (Polyn.plus (Polyn.scale c m q) (Polyn.times p q)).den ρ =
      (c * m.den ρ + p.den ρ) * q.den ρ
    rw [Polyn.den_plus, Polyn.den_scale, Polyn.den_times ρ q p, Int.add_mul]

/-- The negated polynomial has the negated value. -/
theorem Polyn.den_negate (ρ : Nat → Int) :
    ∀ (p : Polyn), (Polyn.negate p).den ρ = - p.den ρ
  | .zero => rfl
  | .add c m p => by
    show (-c) * m.den ρ + (Polyn.negate p).den ρ = -(c * m.den ρ + p.den ρ)
    rw [Polyn.den_negate ρ p, Int.neg_add, Int.neg_mul]

/-- Two polynomials `Polyn.beq` passes are one polynomial. -/
theorem Polyn.beq_eq : ∀ (p q : Polyn), Polyn.beq p q = true → p = q
  | .zero, .zero, _ => rfl
  | .zero, .add _ _ _, h => Bool.noConfusion (show false = true from h)
  | .add _ _ _, .zero, h => Bool.noConfusion (show false = true from h)
  | .add c m p, .add c' m' q, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Ordering.rec (motive := fun _ => Bool) false (Polyn.beq p q) false (Mono.cmp m m'))
        (Int.beq' c c') = true := h
    obtain ⟨hc, h2⟩ := guard_true h'
    have hc' : c = c' := by rw [Int.beq'_eq] at hc; exact hc
    cases hcmp : Mono.cmp m m' with
    | lt => rw [hcmp] at h2; exact Bool.noConfusion h2
    | gt => rw [hcmp] at h2; exact Bool.noConfusion h2
    | eq =>
      rw [hcmp] at h2
      rw [hc', Mono.cmp_eq m m' hcmp, Polyn.beq_eq p q h2]

theorem den_var (ρ : Nat → Int) (i : Nat) :
    (Polyn.add (Int.ofNat (nat_lit 1)) (.mul i .one) .zero).den ρ = ρ i := by
  show 1 * (ρ i * 1) + 0 = ρ i
  rw [Int.add_zero, Int.one_mul, Int.mul_one]

theorem den_const (ρ : Nat → Int) (c : Int) : (Polyn.term c .one .zero).den ρ = c := by
  rw [Polyn.den_term]
  show c * 1 + 0 = c
  rw [Int.add_zero, Int.mul_one]

/-! ## Residues as integers modulo the modulus -/

theorem cong_add {M a a' b b' : Int} (h1 : a % M = a' % M) (h2 : b % M = b' % M) :
    (a + b) % M = (a' + b') % M := by
  rw [Int.add_emod, h1, h2, ← Int.add_emod]

theorem cong_sub {M a a' b b' : Int} (h1 : a % M = a' % M) (h2 : b % M = b' % M) :
    (a - b) % M = (a' - b') % M := by
  rw [Int.sub_emod, h1, h2, ← Int.sub_emod]

theorem cong_mul {M a a' b b' : Int} (h1 : a % M = a' % M) (h2 : b % M = b' % M) :
    (a * b) % M = (a' * b') % M := by
  rw [Int.mul_emod, h1, h2, ← Int.mul_emod]

theorem cong_neg {M a a' : Int} (h : a % M = a' % M) : (-a) % M = (-a') % M := by
  have h0 := cong_sub (rfl : (0 : Int) % M = 0 % M) h
  rwa [Int.zero_sub, Int.zero_sub] at h0

/-- Adding the modulus changes no residue. -/
theorem add_self_emod (a M : Int) : (a + M) % M = a % M := by
  rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

/-- SemR's `add` on residues is, modulo the modulus, the sum of integers. -/
theorem res_add (m ra rb : Nat) :
    (((ra + rb) % m : Nat) : Int) % (m : Int) = ((ra : Int) + (rb : Int)) % (m : Int) := by
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add]

/-- SemR's `mul` on residues is, modulo the modulus, the product of
    integers. -/
theorem res_mul (m ra rb : Nat) :
    (((ra * rb) % m : Nat) : Int) % (m : Int) = ((ra : Int) * (rb : Int)) % (m : Int) := by
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_mul]

/-- SemR's `sub` on residues is, modulo the modulus, the difference of
    integers. -/
theorem res_sub (m ra rb : Nat) (hm : 0 < m) :
    (((ra + (m - rb % m)) % m : Nat) : Int) % (m : Int) =
      ((ra : Int) - (rb : Int)) % (m : Int) := by
  have hle : rb % m ≤ m := Nat.le_of_lt (Nat.mod_lt _ hm)
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_add, Int.natCast_sub hle, Int.natCast_emod]
  have h1 : (ra : Int) + ((m : Int) - (rb : Int) % (m : Int)) =
      ((ra : Int) - (rb : Int) % (m : Int)) + (m : Int) := by omega
  rw [h1, add_self_emod]
  exact cong_sub rfl (Int.emod_emod _ _)

/-- SemR's `neg` on a residue (`negR`) is, modulo the modulus, the negation
    of integers. -/
theorem res_neg (m ra : Nat) (hm : 0 < m) :
    (((m - ra % m) % m : Nat) : Int) % (m : Int) = (-(ra : Int)) % (m : Int) := by
  have hle : ra % m ≤ m := Nat.le_of_lt (Nat.mod_lt _ hm)
  rw [Int.natCast_emod, Int.emod_emod, Int.natCast_sub hle, Int.natCast_emod]
  have h1 : (m : Int) - (ra : Int) % (m : Int) = (-((ra : Int) % (m : Int))) + (m : Int) := by
    omega
  rw [h1, add_self_emod]
  exact cong_neg (Int.emod_emod _ _)

/-- SemR's `not` on a residue is, modulo the modulus, `-a - 1`. -/
theorem res_not (m ra : Nat) (hm : 0 < m) :
    ((m - 1 - ra % m : Nat) : Int) % (m : Int) = (-(ra : Int) + -1) % (m : Int) := by
  have hlt : ra % m < m := Nat.mod_lt _ hm
  have h1 : ((m - 1 - ra % m : Nat) : Int) =
      (-((ra : Int) % (m : Int)) + -1) + (m : Int) := by
    rw [← Int.natCast_emod]; omega
  rw [h1, add_self_emod]
  exact cong_add (cong_neg (Int.emod_emod _ _)) rfl

/-- The residue of `(const INT)` is, modulo the modulus, the integer
    `INT`. -/
theorem res_lit (w : Nat) (neg : Bool) (mag : Nat) :
    ((litR w neg mag : Nat) : Int) % (modulus w : Int) =
      (Bool.rec (motive := fun _ => Int) (Int.ofNat mag) (Int.neg (Int.ofNat mag)) neg) %
        (modulus w : Int) := by
  cases neg
  · show ((mag % modulus w : Nat) : Int) % (modulus w : Int) = _
    rw [Int.natCast_emod, Int.emod_emod]
    rfl
  · exact res_neg (modulus w) mag (modulus_pos w)

/-- Two residues below the modulus that are one integer modulo it are one
    residue. -/
theorem res_inj {m a b : Nat} (ha : a < m) (hb : b < m)
    (h : (a : Int) % (m : Int) = (b : Int) % (m : Int)) : a = b := by
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg a) (Int.ofNat_lt.mpr ha),
    Int.emod_eq_of_lt (Int.natCast_nonneg b) (Int.ofNat_lt.mpr hb)] at h
  exact Int.ofNat_inj.mp h

/-! ## The assignment as integers -/

/-- The residue bound to the variable of rank `i`; 0 where there is none. -/
def resOf (env : List Val) (i : Nat) : Nat :=
  match getVar env i with
  | .ok (.int _ x) => x
  | _ => 0

/-- A variable `isT` passes is bound, in every admitted assignment at an
    integer type, to a residue below the modulus. -/
theorem isT_spec {pb : Nat} {t : IntTy} :
    ∀ (s : Sorts) (env : List Val) (i : Nat), Admits pb (.int t) s env → isT s i = true →
      ∃ x, getVar env i = .ok (.int t x) ∧ x < modulus (t.bits pb)
  | .nil, _, _, _, h => Bool.noConfusion (show false = true from h)
  | .cons srt c rest, env, i, hadm, h => by
    cases srt with
    | t =>
      obtain ⟨x, vs, rfl, hx, hrest⟩ := admits_cons_t_int.mp hadm
      cases i with
      | zero => exact ⟨x, rfl, hx⟩
      | succ j => exact isT_spec rest vs j hrest h
    | bool =>
      obtain ⟨b, vs, rfl, hrest⟩ := admits_cons_bool.mp hadm
      cases i with
      | zero => exact Bool.noConfusion (show false = true from h)
      | succ j => exact isT_spec rest vs j hrest h

/-- What an assignment of integers must read: at every variable of sort `t`,
    the residue the assignment binds. -/
def EnvOk (pb : Nat) (t : IntTy) (s : Sorts) (env : List Val) (ρ : Nat → Int) : Prop :=
  ∀ i, isT s i = true →
    ∃ x, getVar env i = .ok (.int t x) ∧ x < modulus (t.bits pb) ∧ ρ i = (x : Int)

/-- Every admitted assignment at an integer type has such a reading. -/
theorem envOk_of_admits {pb : Nat} {t : IntTy} {s : Sorts} {env : List Val}
    (hadm : Admits pb (.int t) s env) : EnvOk pb t s env (fun i => (resOf env i : Int)) := by
  intro i hi
  obtain ⟨x, hx, hlt⟩ := isT_spec s env i hadm hi
  refine ⟨x, hx, hlt, ?_⟩
  simp only [resOf, hx]

/-! ## A pattern of the fragment against its polynomial -/

/-- The adequacy of the polynomial. At an integer type `t` under pointer
    width `pb`, on an assignment whose residues `ρ` reads, a pattern `ringPat`
    passes evaluates in SemR to a value of type `t` whose residue is below
    the modulus and is, modulo the modulus, the value of the pattern's
    polynomial at `ρ`. -/
theorem ringPat_norm {pb : Nat} {t : IntTy} {s : Sorts} {env : List Val} {ρ : Nat → Int}
    (hρ : EnvOk pb t s env ρ) (p : Pat) (h : ringPat s p = true) :
    ∃ r, p.eval pb (.int t) env = .ok (.int t r) ∧ r < modulus (t.bits pb) ∧
      (r : Int) % (modulus (t.bits pb) : Int) =
        (ringNorm p).den ρ % (modulus (t.bits pb) : Int) := by
  induction p with
  | var i =>
    obtain ⟨x, hx, hlt, hc⟩ := hρ i h
    refine ⟨x, hx, hlt, ?_⟩
    show _ = (Polyn.add (Int.ofNat (nat_lit 1)) (.mul i .one) .zero).den ρ % _
    rw [den_var, hc]
  | cvar i =>
    obtain ⟨x, hx, hlt, hc⟩ := hρ i h
    refine ⟨x, hx, hlt, ?_⟩
    show _ = (Polyn.add (Int.ofNat (nat_lit 1)) (.mul i .one) .zero).den ρ % _
    rw [den_var, hc]
  | lit neg mag =>
    refine ⟨litR (t.bits pb) neg mag, rfl, litR_lt _ neg mag, ?_⟩
    show _ = (Polyn.term _ .one .zero).den ρ % _
    rw [den_const]
    exact res_lit _ neg mag
  | tt => exact Bool.noConfusion (show false = true from h)
  | ff => exact Bool.noConfusion (show false = true from h)
  | bin op a b iha ihb =>
    cases op
    case add =>
      obtain ⟨ha, hb⟩ :=
        guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
      obtain ⟨ra, hea, hra, hda⟩ := iha ha
      obtain ⟨rb, heb, hrb, hdb⟩ := ihb hb
      refine ⟨(ra + rb) % modulus (t.bits pb), ?_, mod_modulus_lt _ _, ?_⟩
      · show ((a.eval pb (.int t) env).bind fun x => (b.eval pb (.int t) env).bind fun y =>
          evalBinop pb .add (.int t) x y) = _
        rw [hea, heb]
        show evalBinop pb .add (.int t) (.int t ra) (.int t rb) = _
        rw [evalBinop_int hra hrb]
        rfl
      · show _ = (Polyn.plus (ringNorm a) (ringNorm b)).den ρ % _
        rw [res_add, Polyn.den_plus]
        exact cong_add hda hdb
    case sub =>
      obtain ⟨ha, hb⟩ :=
        guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
      obtain ⟨ra, hea, hra, hda⟩ := iha ha
      obtain ⟨rb, heb, hrb, hdb⟩ := ihb hb
      refine ⟨(ra + (modulus (t.bits pb) - rb % modulus (t.bits pb))) % modulus (t.bits pb), ?_,
        mod_modulus_lt _ _, ?_⟩
      · show ((a.eval pb (.int t) env).bind fun x => (b.eval pb (.int t) env).bind fun y =>
          evalBinop pb .sub (.int t) x y) = _
        rw [hea, heb]
        show evalBinop pb .sub (.int t) (.int t ra) (.int t rb) = _
        rw [evalBinop_int hra hrb]
        rfl
      · show _ = (Polyn.plus (ringNorm a) (Polyn.negate (ringNorm b))).den ρ % _
        rw [res_sub _ _ _ (modulus_pos _), Polyn.den_plus, Polyn.den_negate, ← Int.sub_eq_add_neg]
        exact cong_sub hda hdb
    case mul =>
      obtain ⟨ha, hb⟩ :=
        guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
      obtain ⟨ra, hea, hra, hda⟩ := iha ha
      obtain ⟨rb, heb, hrb, hdb⟩ := ihb hb
      refine ⟨(ra * rb) % modulus (t.bits pb), ?_, mod_modulus_lt _ _, ?_⟩
      · show ((a.eval pb (.int t) env).bind fun x => (b.eval pb (.int t) env).bind fun y =>
          evalBinop pb .mul (.int t) x y) = _
        rw [hea, heb]
        show evalBinop pb .mul (.int t) (.int t ra) (.int t rb) = _
        rw [evalBinop_int hra hrb]
        rfl
      · show _ = (Polyn.times (ringNorm a) (ringNorm b)).den ρ % _
        rw [res_mul, Polyn.den_times]
        exact cong_mul hda hdb
    all_goals exact Bool.noConfusion (show false = true from h)
  | un op a iha =>
    cases op
    case neg =>
      obtain ⟨ra, hea, hra, hda⟩ := iha h
      refine ⟨negR (t.bits pb) ra, ?_, negR_lt _ _, ?_⟩
      · show ((a.eval pb (.int t) env).bind fun x => evalUnop pb .neg (.int t) x) = _
        rw [hea]
        show evalUnop pb .neg (.int t) (.int t ra) = _
        rw [evalUnop_int hra]
        rfl
      · show (((modulus (t.bits pb) - ra % modulus (t.bits pb)) % modulus (t.bits pb) : Nat) :
            Int) % _ = (Polyn.negate (ringNorm a)).den ρ % _
        rw [res_neg _ _ (modulus_pos _), Polyn.den_negate]
        exact cong_neg hda
    case not =>
      obtain ⟨ra, hea, hra, hda⟩ := iha h
      refine ⟨modulus (t.bits pb) - 1 - ra % modulus (t.bits pb), ?_, ?_, ?_⟩
      · show ((a.eval pb (.int t) env).bind fun x => evalUnop pb .not (.int t) x) = _
        rw [hea]
        show evalUnop pb .not (.int t) (.int t ra) = _
        rw [evalUnop_int hra]
        rfl
      · have := modulus_pos (t.bits pb)
        omega
      · show _ = (Polyn.plus (Polyn.negate (ringNorm a))
            (.add (Int.negSucc (nat_lit 0)) .one .zero)).den ρ % _
        rw [res_not _ _ (modulus_pos _), Polyn.den_plus, Polyn.den_negate]
        refine cong_add (cong_neg hda) ?_
        show (-1 : Int) % _ = ((-1 : Int) * 1 + 0) % _
        rw [Int.add_zero, Int.mul_one]
    all_goals exact Bool.noConfusion (show false = true from h)
  | cmp op a b _ _ => exact Bool.noConfusion (show false = true from h)
  | sel c a b _ _ _ => exact Bool.noConfusion (show false = true from h)

/-! ## What a `true` of `ringRun` proves -/

/-- The four tests of a `ringRun` that answered `true`. -/
theorem ringRun_parts {d : Dir} {vars : Sorts} {lhs rhs : Pat} {cs : Conds}
    (h : ringRun ⟨d, vars, lhs, rhs, cs⟩ = true) :
    cs = .nil ∧ ringPat vars lhs = true ∧ ringPat vars rhs = true ∧
      (ringNorm lhs).beq (ringNorm rhs) = true := by
  cases cs with
  | nil =>
    obtain ⟨hl, h2⟩ :=
      guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
    obtain ⟨hr, hn⟩ := guard_true h2
    exact ⟨rfl, hl, hr, hn⟩
  | cons c rest => exact Bool.noConfusion (show false = true from h)

/-- On every admitted assignment, at every integer type and pointer width,
    both sides of a rule `ringRun` passes are one common value. -/
theorem ringRun_value {pb : Nat} {t : IntTy} {r : Rule} (h : ringRun r = true)
    {env : List Val} (hadm : Admits pb (.int t) r.vars env) :
    ∃ v, r.lhs.eval pb (.int t) env = .ok v ∧ r.rhs.eval pb (.int t) env = .ok v := by
  cases r with
  | mk d vars lhs rhs cs =>
    obtain ⟨_, hl, hr, hn⟩ := ringRun_parts h
    have hρ := envOk_of_admits hadm
    obtain ⟨r1, he1, hr1, hd1⟩ := ringPat_norm hρ lhs hl
    obtain ⟨r2, he2, hr2, hd2⟩ := ringPat_norm hρ rhs hr
    have h12 : r1 = r2 := res_inj hr1 hr2 (by rw [hd1, hd2, Polyn.beq_eq _ _ hn])
    subst h12
    exact ⟨_, he1, he2⟩

/-- One common value stands under either direction. -/
theorem holds_of_value {d : Dir} {l r : R Val} (h : ∃ v, l = .ok v ∧ r = .ok v) :
    Holds d l r := by
  cases d
  · exact h
  · exact .inr h

/-- A rule `ringRun` passes has no side condition. -/
theorem ringRun_conds {r : Rule} (h : ringRun r = true) : r.conds = .nil := by
  cases r with
  | mk d vars lhs rhs cs => exact (ringRun_parts h).1

/-- Every list of variables has an admitted assignment at an integer type:
    the residue 0 for a variable of sort `t`, `false` for one of sort
    `bool`. -/
theorem admits_some (pb : Nat) (t : IntTy) : ∀ (s : Sorts), ∃ env, Admits pb (.int t) s env
  | .nil => ⟨[], admits_nil.mpr rfl⟩
  | .cons srt c rest => by
    obtain ⟨vs, hvs⟩ := admits_some pb t rest
    cases srt with
    | t => exact ⟨.int t 0 :: vs, admits_cons_t_int.mpr ⟨0, vs, rfl, modulus_pos _, hvs⟩⟩
    | bool => exact ⟨.bool false :: vs, admits_cons_bool.mpr ⟨false, vs, rfl, hvs⟩⟩

/-- What a `true` of `ringRun` proves, in the form that names no type: the
    rule is `Sound` at each of the twelve integer types. One evaluation of
    `ringRun r` is the answer of `ringAll r` at all of them (`ringAll_int`). -/
theorem ringRun_sound (r : Rule) (h : ringRun r = true) (t : IntTy) : Sound r (.int t) := by
  intro pb env _ hadm _
  exact holds_of_value (ringRun_value h hadm)

end RingAll

open RingAll

/-- At an integer type `ringAll` is `ringRun`, whatever the type. -/
theorem ringAll_int (r : Rule) (t : IntTy) : ringAll r (.int t) = ringRun r := rfl

/-- At `bool` `ringAll` is `false`, whatever the rule. -/
theorem ringAll_bool (r : Rule) : ringAll r .bool = false := rfl

/-- `ringAll` answers `true` only at an integer type, and there it is
    `ringRun`. -/
theorem ringAll_run {r : Rule} {T : STy} (h : ringAll r T = true) :
    (∃ t, T = .int t) ∧ ringRun r = true := by
  cases T with
  | int t => exact ⟨⟨t, rfl⟩, h⟩
  | bool => exact Bool.noConfusion (show false = true from h)

/-- The soundness of the procedure, with no other hypothesis: a rule on
    which `ringAll` answers `true` at `T` is `Sound` at `T`. -/
theorem ringAll_sound (r : Rule) (T : STy) (h : ringAll r T = true) : Sound r T := by
  obtain ⟨⟨t, rfl⟩, hrun⟩ := ringAll_run h
  exact ringRun_sound r hrun t

/-- A rule on which `ringAll` answers `true` at `T` says something there: at
    every pointer width some admitted assignment (it has no side condition)
    gives both sides one common value. Every admitted assignment does
    (`RingAll.ringRun_value`). -/
theorem ringAll_defined (r : Rule) (T : STy) (h : ringAll r T = true) : Defined r T := by
  intro pb _
  obtain ⟨⟨t, rfl⟩, hrun⟩ := ringAll_run h
  obtain ⟨env, hadm⟩ := admits_some pb t r.vars
  obtain ⟨v, hl, hr⟩ := ringRun_value hrun hadm
  refine ⟨env, v, hadm, ?_, hl, hr⟩
  rw [ringRun_conds hrun]
  trivial

/-- A rule on which `ringAll` answers `true` at `T` has side conditions some
    assignment satisfies there: it has none (the first half of
    `ringAll_defined`, in the `eqsat_rules` family's own statement). -/
theorem ringAll_satisfiable (r : Rule) (T : STy) (h : ringAll r T = true) : Satisfiable r T := by
  intro pb hpb
  obtain ⟨env, _, hadm, hc, _⟩ := ringAll_defined r T h pb hpb
  exact ⟨env, hadm, hc⟩

end EqsatDecide
