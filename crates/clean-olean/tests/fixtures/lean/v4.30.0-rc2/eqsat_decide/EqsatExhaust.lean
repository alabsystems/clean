/- EqsatExhaust: a rule checked on every assignment at eight bits and at
   `bool`, and what a `true` proves (PKG-U6).
   Copyright 2026 Andrew Yates. Apache-2.0.
   Author: Andrew Yates <andrewyates.name@gmail.com>

   `exhaust8 r T` is a decision procedure for `EqsatRule.Sound r T`, and
   `exhaust8_sound : exhaust8 r T = true → Sound r T` is its one theorem. The
   proof of a rule a search found is

       EqsatDecide.exhaust8_sound <rule literal> <type> EqsatDecide.rflTrue

   with `rflTrue : true = true`. Its type is `Sound <literal> <type>` only if
   `exhaust8 <literal> <type>` and `true` are one term up to evaluation, so
   the kernel accepts it only by evaluating the procedure on the literal.
   Nothing here is trusted and nothing here is part of what a rule means:
   `EqsatRule.Sound` does not reach this module, and a wrong `exhaust8` has no
   `exhaust8_sound`.

   What `exhaust8 r T` answers `true` on. All four must hold:
   * `T` is `i8`, `u8` or `bool`. At every other type the answer is `false`
     before the rule is read (`exhaust8_run`), so the term above cannot be
     reused at another width: `exhaust8 r (.int .u64)` and `true` are two
     terms;
   * the rule has at most `maxAssignments` (1,024) assignments: a variable of
     sort `t` at an integer type counts 256, every other variable 2 (`small`,
     `space`). One 8-bit variable with up to two Booleans, or up to ten
     Booleans. A rule with two 8-bit variables has 65,536 and is answered
     `false` at once, where the enumeration would only run out of budget;
   * some assignment satisfies the side conditions and gives the left side a
     value (`live`). A rule is `Sound` whatever its sides are when no
     assignment satisfies its conditions, and a `refines` rule is `Sound`
     whatever its right side is when its left side is undefined behaviour on
     every assignment that does. Neither is admitted by this route:
     `exhaust8_defined` gives, from the same `true`, an assignment that meets
     the conditions and on which both sides are one common value (`Defined`),
     and `exhaust8_satisfiable` gives `EqsatRule.Satisfiable r T`;
   * every assignment passes `checkR` (`sweep`): its side conditions fail, or
     its two sides stand as the direction says and neither is `bad`.

   So `false` is not a refutation. It says the rule is not proved by this
   procedure: the type is not covered, the rule is too large, its conditions
   are never met, its left side is never a value, a side is not a term
   (`RR.bad`), or some assignment fails.
   `exhaust8_sound` is the only claim; completeness is not stated.

   `sweep_sound`, `live_defined` and `live_satisfiable` hold at every type,
   width and modulus
   (`WidthOf pb T w`, `m = modulus w`); `exhaust8` instantiates them at width
   8 and modulus 256, which `width8` shows are the width and modulus of the
   three types it covers, under every pointer width.

   How it is written, and why: as `EqsatResidue`, every definition the kernel
   evaluates is one recursor application with closed minor premises. The
   enumeration is one counter per variable (`allBelow` over the modulus for a
   residue, `both` for a Boolean), nested by a continuation that receives the
   assignment, never one counter over all assignments: Clean's kernel leaves a
   `Nat.rec` with a constant motive unreduced when its count is a literal of
   65,536 or more (`native_closed_fold_grind_stuck`). The minor premise of a
   counter tests before it recurses, so the first failing assignment ends the
   enumeration and a false rule costs little. The rule is taken apart by
   `Rule.rec` once per part, not once per assignment.
-/
import EqsatResidue

namespace EqsatDecide
open SemR EqsatRule

noncomputable section

/-- `f` is `true` at every number below `n`, tested from `n - 1` down; the
    first `false` is the answer. -/
def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (f k)) n

/-- `f` is `true` at both Booleans. -/
def both (f : Bool → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (f false) (f true)

/-- `f` is `true` at some number below `n`; the first `true` is the answer. -/
def anyBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k ih => Bool.rec (motive := fun _ => Bool) ih true (f k)) n

/-- `f` is `true` at some Boolean. -/
def either (f : Bool → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f true) true (f false)

/-- `k` is `true` on every assignment of the sorts `s`: a residue below `m`
    for a variable of sort `t` at an integer type (`int`), a Boolean for every
    other variable (`EqsatRule.AdmitsVal`). -/
def allFrom (int : Bool) (m : Nat) (s : Sorts) : (List RV → Bool) → Bool :=
  Sorts.rec (motive := fun _ => (List RV → Bool) → Bool)
    (fun k => k [])
    (fun srt _ _ ih k =>
      Srt.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (both fun v => ih fun vs => k (.bit v :: vs))
          (allBelow m fun x => ih fun vs => k (.res x :: vs)) int)
        (both fun v => ih fun vs => k (.bit v :: vs))
        srt)
    s

/-- `k` is `true` on some assignment of the sorts `s`. -/
def anyFrom (int : Bool) (m : Nat) (s : Sorts) : (List RV → Bool) → Bool :=
  Sorts.rec (motive := fun _ => (List RV → Bool) → Bool)
    (fun k => k [])
    (fun srt _ _ ih k =>
      Srt.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (either fun v => ih fun vs => k (.bit v :: vs))
          (anyBelow m fun x => ih fun vs => k (.res x :: vs)) int)
        (either fun v => ih fun vs => k (.bit v :: vs))
        srt)
    s

/-- The number of assignments of the sorts `s`: `m` for a variable of sort `t`
    at an integer type, 2 for every other variable. -/
def space (int : Bool) (m : Nat) (s : Sorts) : Nat :=
  Sorts.rec (motive := fun _ => Nat) 1
    (fun srt _ _ ih =>
      Srt.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (2 * ih) (m * ih) int) (2 * ih) srt)
    s

/-- The most assignments `exhaust8` enumerates (the module header; the
    family's README has the measured cost behind it). -/
def maxAssignments : Nat := 1024

/-- The rule has at most `maxAssignments` assignments. -/
def small (r : Rule) (int : Bool) (m : Nat) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun _ vars _ _ _ => Nat.ble (space int m vars) maxAssignments) r

/-- The outcome is a value: neither undefined behaviour nor `bad`. -/
def isOk (x : RR) : Bool :=
  RR.rec (motive := fun _ => Bool) (fun _ => true) false false x

/-- Some assignment of the rule's variables satisfies its side conditions and
    gives its left side a value (`live_defined`). -/
def live (r : Rule) (int : Bool) (w m : Nat) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun _ vars lhs _ cs => anyFrom int m vars fun env =>
      Bool.rec (motive := fun _ => Bool) false (isOk (lhs.evalR int w m env))
        (condsR int w env cs)) r

/-- Every assignment of the rule's variables passes `checkR`
    (`sweep_sound`). -/
def sweep (r : Rule) (int : Bool) (w m : Nat) : Bool :=
  Rule.rec (motive := fun _ => Bool)
    (fun d vars lhs rhs cs => allFrom int m vars (checkR d lhs rhs cs int w m)) r

/-- `small`, then `live`, then `sweep`; the first `false` is the answer. -/
def run (r : Rule) (int : Bool) (w m : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (sweep r int w m) (live r int w m))
    (small r int m)

/-- The procedure: `run` at width 8 and modulus 256 at `i8` and `u8`, `run`
    over Booleans at `bool` (where the width and the modulus are not read),
    and `false` at every other type. -/
def exhaust8 (r : Rule) (T : STy) : Bool :=
  STy.rec (motive := fun _ => Bool)
    (fun t => IntTy.rec (motive := fun _ => Bool)
      (run r true (nat_lit 8) (nat_lit 256)) false false false false false
      (run r true (nat_lit 8) (nat_lit 256)) false false false false false t)
    (run r false (nat_lit 8) (nat_lit 256))
    T

end

/-- The proof that a procedure answered `true`: the kernel accepts it at type
    `exhaust8 r T = true` only by evaluating `exhaust8 r T`. A constant, so
    that a term built from it names no universe level. -/
theorem rflTrue : true = true := rfl

/-! ## The enumeration reaches every assignment -/

theorem allBelow_succ (n : Nat) (f : Nat → Bool) :
    allBelow (n + 1) f = Bool.rec (motive := fun _ => Bool) false (allBelow n f) (f n) := rfl

/-- A `true` of `allBelow n f` is `f k = true` at every `k` below `n`. -/
theorem allBelow_spec : ∀ (n : Nat) (f : Nat → Bool), allBelow n f = true →
    ∀ k, k < n → f k = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, f, h, k, hk => by
    rw [allBelow_succ] at h
    cases hf : f n with
    | false => rw [hf] at h; exact Bool.noConfusion h
    | true =>
      rw [hf] at h
      by_cases hkn : k = n
      · rw [hkn]; exact hf
      · exact allBelow_spec n f h k (by omega)

/-- A `true` of `both f` is `f b = true` at both Booleans. -/
theorem both_spec {f : Bool → Bool} (h : both f = true) : ∀ b, f b = true := by
  have h' : Bool.rec (motive := fun _ => Bool) false (f false) (f true) = true := h
  intro b
  cases ht : f true with
  | false => rw [ht] at h'; exact Bool.noConfusion h'
  | true =>
    rw [ht] at h'
    cases b
    · exact h'
    · exact ht

theorem anyBelow_succ (n : Nat) (f : Nat → Bool) :
    anyBelow (n + 1) f = Bool.rec (motive := fun _ => Bool) (anyBelow n f) true (f n) := rfl

/-- A `true` of `anyBelow n f` names a `k` below `n` with `f k = true`. -/
theorem anyBelow_spec : ∀ (n : Nat) (f : Nat → Bool), anyBelow n f = true →
    ∃ k, k < n ∧ f k = true
  | 0, _, h => Bool.noConfusion (show false = true from h)
  | n + 1, f, h => by
    rw [anyBelow_succ] at h
    cases hf : f n with
    | true => exact ⟨n, Nat.lt_succ_self n, hf⟩
    | false =>
      rw [hf] at h
      obtain ⟨k, hk, hfk⟩ := anyBelow_spec n f h
      exact ⟨k, Nat.lt_succ_of_lt hk, hfk⟩

/-- A `true` of `either f` names a Boolean with `f b = true`. -/
theorem either_spec {f : Bool → Bool} (h : either f = true) : ∃ b, f b = true := by
  have h' : Bool.rec (motive := fun _ => Bool) (f true) true (f false) = true := h
  cases hf : f false with
  | true => exact ⟨false, hf⟩
  | false => rw [hf] at h'; exact ⟨true, h'⟩

/-- The enumeration is complete: every assignment the rule's variables admit
    in SemR's reading (`EqsatRule.Admits`) is the image of a well-formed
    residue assignment that `allFrom` passed to `k`. -/
theorem allFrom_complete {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) :
    ∀ (s : Sorts) (k : List RV → Bool) (env : List Val),
      allFrom (isInt T) m s k = true → Admits pb T s env →
      ∃ envR, EnvWF (isInt T) m envR ∧ env = envR.map (RV.val T) ∧ k envR = true := by
  intro s
  induction s with
  | nil =>
    intro k env h hadm
    rw [admits_nil] at hadm
    subst hadm
    exact ⟨[], trivial, rfl, h⟩
  | cons srt c rest ih =>
    intro k env h hadm
    cases srt with
    | bool =>
      obtain ⟨b, vs, rfl, hrest⟩ := admits_cons_bool.mp hadm
      have h1 : both (fun v => allFrom (isInt T) m rest fun vs => k (.bit v :: vs)) = true := h
      obtain ⟨envR, hwf, rfl, hk⟩ := ih (fun vs => k (.bit b :: vs)) vs (both_spec h1 b) hrest
      exact ⟨.bit b :: envR, ⟨trivial, hwf⟩, rfl, hk⟩
    | t =>
      cases T with
      | int t =>
        obtain ⟨x, vs, rfl, hx, hrest⟩ := admits_cons_t_int.mp hadm
        have hw' : t.bits pb = w := hw
        subst hw'; subst hm
        have h1 : allBelow (modulus (t.bits pb))
            (fun x => allFrom true (modulus (t.bits pb)) rest fun vs => k (.res x :: vs)) = true := h
        obtain ⟨envR, hwf, rfl, hk⟩ :=
          ih (fun vs => k (.res x :: vs)) vs (allBelow_spec _ _ h1 x hx) hrest
        exact ⟨.res x :: envR, ⟨⟨rfl, hx⟩, hwf⟩, rfl, hk⟩
      | bool =>
        obtain ⟨b, vs, rfl, hrest⟩ := admits_cons_t_bool.mp hadm
        have h1 : both (fun v => allFrom false m rest fun vs => k (.bit v :: vs)) = true := h
        obtain ⟨envR, hwf, rfl, hk⟩ := ih (fun vs => k (.bit b :: vs)) vs (both_spec h1 b) hrest
        exact ⟨.bit b :: envR, ⟨trivial, hwf⟩, rfl, hk⟩

/-- A `true` of `anyFrom` names a well-formed residue assignment whose image
    the variables admit and on which `k` is `true`. -/
theorem anyFrom_witness {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) :
    ∀ (s : Sorts) (k : List RV → Bool), anyFrom (isInt T) m s k = true →
      ∃ envR, EnvWF (isInt T) m envR ∧ Admits pb T s (envR.map (RV.val T)) ∧ k envR = true := by
  intro s
  induction s with
  | nil =>
    intro k h
    exact ⟨[], trivial, admits_nil.mpr rfl, h⟩
  | cons srt c rest ih =>
    intro k h
    cases srt with
    | bool =>
      have h1 : either (fun v => anyFrom (isInt T) m rest fun vs => k (.bit v :: vs)) = true := h
      obtain ⟨b, hb⟩ := either_spec h1
      obtain ⟨envR, hwf, hadm, hk⟩ := ih (fun vs => k (.bit b :: vs)) hb
      exact ⟨.bit b :: envR, ⟨trivial, hwf⟩, admits_cons_bool.mpr ⟨b, _, rfl, hadm⟩, hk⟩
    | t =>
      cases T with
      | int t =>
        have hw' : t.bits pb = w := hw
        subst hw'; subst hm
        have h1 : anyBelow (modulus (t.bits pb))
            (fun x => anyFrom true (modulus (t.bits pb)) rest fun vs => k (.res x :: vs)) = true := h
        obtain ⟨x, hx, hb⟩ := anyBelow_spec _ _ h1
        obtain ⟨envR, hwf, hadm, hk⟩ := ih (fun vs => k (.res x :: vs)) hb
        exact ⟨.res x :: envR, ⟨⟨rfl, hx⟩, hwf⟩,
          admits_cons_t_int.mpr ⟨x, _, rfl, hx, hadm⟩, hk⟩
      | bool =>
        have h1 : either (fun v => anyFrom false m rest fun vs => k (.bit v :: vs)) = true := h
        obtain ⟨b, hb⟩ := either_spec h1
        obtain ⟨envR, hwf, hadm, hk⟩ := ih (fun vs => k (.bit b :: vs)) hb
        exact ⟨.bit b :: envR, ⟨trivial, hwf⟩, admits_cons_t_bool.mpr ⟨b, _, rfl, hadm⟩, hk⟩

/-! ## The side conditions, in the other direction -/

/-- What `pow2Upto` finds is a power of two. -/
theorem pow2Upto_sound : ∀ (n r : Nat), pow2Upto n r = true → ∃ k, r = 2 ^ k
  | 0, _, h => Bool.noConfusion (show false = true from h)
  | n + 1, r, h => by
    have h' : (Nat.beq r (2 ^ n) || pow2Upto n r) = true := h
    cases hb : Nat.beq r (2 ^ n) with
    | true => exact ⟨n, Nat.eq_of_beq_eq_true hb⟩
    | false =>
      rw [hb] at h'
      exact pow2Upto_sound n r h'

/-- The residue `EqsatRule.onResidue` reads for a variable is the residue the
    evaluator reads (the converse of `getVar_of_getR_res`). -/
theorem getR_of_getVar_int {t t' : IntTy} :
    ∀ (env : List RV) (i r : Nat),
      getVar (env.map (RV.val (.int t))) i = .ok (.int t' r) → getR env i = .ok (.res r)
  | [], _, _, h => by cases h
  | v :: _, 0, r, h => by
    cases v with
    | res a =>
      have h' : R.ok (Val.int t a) = .ok (.int t' r) := h
      cases h'
      rfl
    | bit b =>
      have h' : R.ok (Val.bool b) = .ok (.int t' r) := h
      cases h'
  | _ :: vs, i + 1, r, h => getR_of_getVar_int vs i r h

/-- `onResidue` holds wherever `condR` is `true` of a test that decides the
    property in that direction (the converse of `condR_of_onResidue`). -/
theorem onResidue_of_condR {pb : Nat} {T : STy} {w : Nat} (hw : WidthOf pb T w)
    {env : List RV} (i : Nat) {P : Nat → Nat → Prop} {Pb : Nat → Bool}
    (hP : ∀ r, Pb r = true → P w r) (h : condR (isInt T) env i Pb = true) :
    onResidue pb T (env.map (RV.val T)) i P := by
  cases T with
  | bool => simp only [onResidue]
  | int t =>
    have hw' : t.bits pb = w := hw
    subst hw'
    simp only [onResidue]
    split
    · next _ _ t1 t2 r hT hv =>
      cases hT
      have hg := getR_of_getVar_int env i r hv
      have h' : (match getR env i with | .ok (.res r) => Pb r | _ => true) = true := h
      rw [hg] at h'
      exact hP r h'
    · trivial

/-- A side condition that is `true` on residues holds in SemR's reading. -/
theorem holds_of_holdsR {pb : Nat} {T : STy} {w : Nat} (hw : WidthOf pb T w)
    {env : List RV} (c : Cond) (h : c.holdsR (isInt T) w env = true) :
    c.holds pb T (env.map (RV.val T)) := by
  cases c with
  | eq i neg mag =>
    have h' : condR (isInt T) env i (fun r => Nat.beq r (litR w neg mag)) = true := h
    show onResidue pb T (env.map (RV.val T)) i fun w r => r = litR w neg mag
    exact onResidue_of_condR hw i (fun r hr => Nat.eq_of_beq_eq_true hr) h'
  | ne i neg mag =>
    have h' : condR (isInt T) env i (fun r => !Nat.beq r (litR w neg mag)) = true := h
    show onResidue pb T (env.map (RV.val T)) i fun w r => r ≠ litR w neg mag
    refine onResidue_of_condR hw i (fun r hr heq => ?_) h'
    subst heq
    rw [Nat.beq_refl] at hr
    exact Bool.noConfusion hr
  | pow2 i =>
    have h' : condR (isInt T) env i (fun r => pow2Upto w r) = true := h
    show onResidue pb T (env.map (RV.val T)) i fun _ r => ∃ k, r = 2 ^ k
    exact onResidue_of_condR hw i (fun r hr => pow2Upto_sound w r hr) h'
  | zeroModWidth i =>
    have h' : condR (isInt T) env i (fun r => Nat.beq (r % w) 0) = true := h
    show onResidue pb T (env.map (RV.val T)) i fun w r => r % w = 0
    exact onResidue_of_condR hw i (fun r hr => Nat.eq_of_beq_eq_true hr) h'

/-- `condsR` decides the side conditions exactly: with
    `condsR_of_condsHold`, it is `true` where and only where `CondsHold`
    holds. This direction is what `live` needs. -/
theorem condsHold_of_condsR {pb : Nat} {T : STy} {w : Nat} (hw : WidthOf pb T w)
    {env : List RV} :
    ∀ (cs : Conds), condsR (isInt T) w env cs = true → CondsHold pb T (env.map (RV.val T)) cs
  | .nil, _ => trivial
  | .cons c rest, h => by
    rw [condsR_cons] at h
    cases hc : c.holdsR (isInt T) w env with
    | false => rw [hc] at h; exact Bool.noConfusion h
    | true =>
      rw [hc] at h
      exact ⟨holds_of_holdsR hw c hc, condsHold_of_condsR hw rest h⟩

/-! ## What a `true` proves -/

/-- Both parts of a guarded answer that is `true`. -/
theorem guard_true {c x : Bool}
    (h : Bool.rec (motive := fun _ => Bool) false x c = true) : c = true ∧ x = true := by
  cases c
  · exact Bool.noConfusion h
  · exact ⟨rfl, h⟩

/-- What a `true` of `sweep` proves, at any instance type `T` of width `w`
    and modulus `m`: the body of `EqsatRule.Sound r T` at pointer width
    `pb`. -/
theorem sweep_sound {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w) (hm : m = modulus w)
    (r : Rule) (h : sweep r (isInt T) w m = true) (env : List Val) :
    Admits pb T r.vars env → CondsHold pb T env r.conds →
      Holds r.dir (r.lhs.eval pb T env) (r.rhs.eval pb T env) := by
  cases r with
  | mk d vars lhs rhs cs =>
    intro hadm hc
    have h1 : allFrom (isInt T) m vars (checkR d lhs rhs cs (isInt T) w m) = true := h
    obtain ⟨envR, hwf, rfl, hk⟩ := allFrom_complete hw hm vars _ env h1 hadm
    exact checkR_sound hw hm hwf d lhs rhs cs hk hc

/-- An outcome `isOk` passes is a value. -/
theorem isOk_ok {x : RR} (h : isOk x = true) : ∃ v, x = .ok v := by
  cases x with
  | ok v => exact ⟨v, rfl⟩
  | ub => exact Bool.noConfusion (show false = true from h)
  | bad => exact Bool.noConfusion (show false = true from h)

/-- What a `true` of `live` proves, at any instance type `T` of width `w` and
    modulus `m`: at pointer width `pb` some admitted assignment satisfies the
    side conditions and gives the left side a value in SemR's own
    evaluation. -/
theorem live_defined {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) (r : Rule) (h : live r (isInt T) w m = true) :
    ∃ env, Admits pb T r.vars env ∧ CondsHold pb T env r.conds ∧
      ∃ v, r.lhs.eval pb T env = .ok v := by
  cases r with
  | mk d vars lhs rhs cs =>
    have h1 : anyFrom (isInt T) m vars (fun env =>
        Bool.rec (motive := fun _ => Bool) false (isOk (lhs.evalR (isInt T) w m env))
          (condsR (isInt T) w env cs)) = true := h
    obtain ⟨envR, hwf, hadm, hk⟩ := anyFrom_witness (pb := pb) hw hm vars _ h1
    obtain ⟨hc, hok⟩ :=
      guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from hk)
    obtain ⟨v, hv⟩ := isOk_ok hok
    have hag := evalR_agrees (pb := pb) hw hm hwf lhs
    rw [hv] at hag
    exact ⟨envR.map (RV.val T), hadm, condsHold_of_condsR hw cs hc, v.val T, hag.2⟩

/-- What a `true` of `live` proves of the side conditions alone: the body of
    `EqsatRule.Satisfiable r T` at pointer width `pb`. -/
theorem live_satisfiable {pb : Nat} {T : STy} {w m : Nat} (hw : WidthOf pb T w)
    (hm : m = modulus w) (r : Rule) (h : live r (isInt T) w m = true) :
    ∃ env, Admits pb T r.vars env ∧ CondsHold pb T env r.conds := by
  obtain ⟨env, hadm, hc, _⟩ := live_defined (pb := pb) hw hm r h
  exact ⟨env, hadm, hc⟩

/-- A left side that is a value leaves a direction one reading: the right
    side is that value. -/
theorem holds_ok {d : Dir} {v : Val} {x : R Val} (h : Holds d (.ok v) x) : x = .ok v := by
  cases d with
  | equiv =>
    obtain ⟨u, hl, hr⟩ := h
    cases hl
    exact hr
  | refines =>
    rcases h with ⟨msg, hmsg⟩ | ⟨u, hl, hr⟩
    · cases hmsg
    · cases hl
      exact hr

/-- The three tests of a `run` that answered `true`. -/
theorem run_parts {r : Rule} {int : Bool} {w m : Nat} (h : run r int w m = true) :
    small r int m = true ∧ live r int w m = true ∧ sweep r int w m = true := by
  obtain ⟨hs, h2⟩ := guard_true (show Bool.rec (motive := fun _ => Bool) false _ _ = true from h)
  obtain ⟨hl, hsw⟩ := guard_true h2
  exact ⟨hs, hl, hsw⟩

/-- `exhaust8` answers `true` only at `i8`, `u8` and `bool`, and there it is
    `run` at width 8 and modulus 256. At every other type it is `false`
    whatever the rule. -/
theorem exhaust8_run {r : Rule} {T : STy} (h : exhaust8 r T = true) :
    (T = .int .i8 ∨ T = .int .u8 ∨ T = .bool) ∧ run r (isInt T) 8 256 = true := by
  cases T with
  | bool => exact ⟨.inr (.inr rfl), h⟩
  | int t =>
    cases t
    case i8 => exact ⟨.inl rfl, h⟩
    case u8 => exact ⟨.inr (.inl rfl), h⟩
    all_goals exact Bool.noConfusion (show false = true from h)

/-- 8 is the width of the types `exhaust8` covers, under every pointer
    width (`bool` has none, and any width stands). -/
theorem width8 {pb : Nat} {T : STy} (h : T = .int .i8 ∨ T = .int .u8 ∨ T = .bool) :
    WidthOf pb T 8 := by
  rcases h with rfl | rfl | rfl
  · rfl
  · rfl
  · trivial

/-- The soundness of the procedure, with no other hypothesis: a rule on
    which `exhaust8` answers `true` at `T` is `Sound` at `T`. -/
theorem exhaust8_sound (r : Rule) (T : STy) (h : exhaust8 r T = true) : Sound r T := by
  intro pb env _ hadm hc
  obtain ⟨hT, hrun⟩ := exhaust8_run h
  exact sweep_sound (width8 hT) rfl r (run_parts hrun).2.2 env hadm hc

/-- The rule says something at `T`: at every admitted pointer width some
    admitted assignment satisfies the side conditions and both sides are one
    common value there. `EqsatRule.Sound` does not say this: a rule is `Sound`
    whatever its sides are when no assignment satisfies its conditions
    (`EqsatRule.Satisfiable` is that part), and a `refines` rule is `Sound`
    whatever its right side is when its left side is undefined behaviour on
    every assignment that does. -/
def Defined (r : Rule) (T : STy) : Prop :=
  ∀ pb, PbOk T pb → ∃ env v, Admits pb T r.vars env ∧ CondsHold pb T env r.conds ∧
    r.lhs.eval pb T env = .ok v ∧ r.rhs.eval pb T env = .ok v

/-- A rule on which `exhaust8` answers `true` at `T` says something there:
    `exhaust8` admits no rule that is `Sound` for want of an assignment, or
    for want of one on which its left side is defined. -/
theorem exhaust8_defined (r : Rule) (T : STy) (h : exhaust8 r T = true) : Defined r T := by
  intro pb _
  obtain ⟨hT, hrun⟩ := exhaust8_run h
  obtain ⟨env, hadm, hc, v, hv⟩ := live_defined (pb := pb) (width8 hT) rfl r (run_parts hrun).2.1
  have hh := sweep_sound (width8 hT) rfl r (run_parts hrun).2.2 env hadm hc
  rw [hv] at hh
  exact ⟨env, v, hadm, hc, hv, holds_ok hh⟩

/-- A rule on which `exhaust8` answers `true` at `T` has side conditions
    some assignment satisfies there (the first half of `exhaust8_defined`, in
    the `eqsat_rules` family's own statement). -/
theorem exhaust8_satisfiable (r : Rule) (T : STy) (h : exhaust8 r T = true) :
    Satisfiable r T := by
  intro pb _
  obtain ⟨hT, hrun⟩ := exhaust8_run h
  exact live_satisfiable (width8 hT) rfl r (run_parts hrun).2.1

end EqsatDecide
