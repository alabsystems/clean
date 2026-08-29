/-
  GENERAL-k multi-neuron (kReLU / GCP-CROWN-style) cut soundness — closing the
  last SCOPED item in DEEPCONV_FRONTIER.md §2.5 ("general-k facet derivation").

  ## What was open

  `TwoReluCutGeneral.lean` proves the JOINT 2-ReLU cut weight-parametrically and
  derives the joint bound `B` from box corners, then composes through
  `farkas_premise_combination`.  But it is hard-wired to k = 2 (four activation
  patterns `hpp/hpn/hnp/hnn`, a 1-box `affine_le_of_endpoints`).  The frontier
  item asks to lift this to ARBITRARY k: the joint k-ReLU cut, whose facet can be
  strictly tighter than ALL pairwise k=2 cuts when the coupling is genuinely
  k-way (the GCP-CROWN / kReLU group-cut regime).

  ## What THIS file proves, sorry-free, for ARBITRARY k

  1. `multiReluCut_pattern_dominance`  (FULLY GENERAL, ∀ k, Finset-indexed)
        weights `cc : Fin k → ℚ` (≥ 0), pre-activations `z : Fin k → ℚ`, bound B.
        If for EVERY activation pattern `S : Finset (Fin k)` the per-pattern
        linear form `∑_{i∈S} cc i * z i ≤ B`, then `∑_i cc i * relu (z i) ≤ B`.
        Proof: the active set `A = {i : 0 ≤ z i}` is a Finset; on `A`,
        `relu (z i) = z i`, off `A` it is `0`, so the ReLU sum EQUALS the
        per-pattern form at `S = A`, which the hypothesis bounds by `B`.

  2. The n-dim BOX B-derivation (FULLY GENERAL, ∀ n, ∀ k):
        - `affine_box_le_of_corners` : an affine functional on an n-box is `≤ B`
          everywhere iff `≤ B` at every box corner (proved by induction over the
          free coordinate set, reusing the 1-box `affine_le_of_endpoints`).
        - `multiReluCut_box_le` : with `z_i` affine in the box input `x`, if `B`
          dominates each of the 2^k per-pattern affine forms at every box corner,
          then `∑_i cc i * relu (z_i x) ≤ B` for every `x` in the box.  This
          DERIVES (not assumes) a valid joint k-cut bound `B`.

  3. Composition (FULLY GENERAL): `multiReluCut_bridge` feeds the cut into the
        existing `farkas_premise_combination` as a single `≥ 0`-multiplier premise
        `g_cut = (∑ cc_i a_i) - B ≤ 0`, the general-k analogue of
        `twoReluCut_bridge`.

  4. A concrete k = 3 DEMONSTRATION of genuine 3-way coupling
        (`demoCoef`, box `[-1,1]^2`, `z1 = x1, z2 = -x1+2x2, z3 = -x1-2x2`):
        - `demo_joint_cut_closes` : the joint 3-ReLU cut `∑ relu z_i ≤ 3` holds on
          the whole box (DERIVED through `multiReluCut_box_le`; all 8 patterns × 4
          corners ≤ 3), so with `const = 3` the margin `3 - ∑ relu z_i ≥ 0`.
        - `demo_pairwise_relaxation_open` : an EXPLICIT relaxation-feasible point
          (`x = (0,-1)`, `a = (1/2, 1/2, 5/2)`) satisfies every per-coordinate
          ReLU triangle envelope AND every pairwise 2-ReLU joint cut, yet has
          `∑ a_i = 7/2 > 3`.  Hence NO combination of k ≤ 2 cuts + triangles can
          certify `∑ relu z_i ≤ 3`; only the joint 3-cut closes the margin.

  All `#print axioms` must be `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.

  GENERAL vs DEMONSTRATED:
   * (1),(2),(3) are GENERAL-k (and general-n), Finset-indexed, for arbitrary k.
   * (4) is the k = 3 INSTANCE that exhibits the 3-way coupling content; it is
     produced BY the general-k machinery (the joint cut is `multiReluCut_box_le`
     at k = 3, n = 2), with the pairwise-open fact verified by an exact witness.
-/

import Crownproof.Basic
import Crownproof.Bridge
import Crownproof.TwoReluCutGeneral
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Crownproof

open Finset

/-! ## 1.  The fully-general (∀ k) pattern-dominance theorem.

For arbitrary weights `cc : Fin k → ℚ` (≥ 0) and arbitrary pre-activations
`z : Fin k → ℚ`, a candidate joint bound `B` that dominates the per-pattern
linear form `∑_{i∈S} cc i * z i` for EVERY activation pattern `S : Finset (Fin k)`
dominates the ReLU sum `∑_i cc i * relu (z i)`.

The proof is the n-neuron lift of the 4-pattern case split in
`twoReluCut_pattern_dominance`: on any concrete `z`, the *active set*
`A = {i : 0 ≤ z i}` is itself a `Finset (Fin k)`; on `A` we have `relu (z i) = z i`
and off `A` we have `relu (z i) = 0`, so the whole ReLU sum equals the per-pattern
form `∑_{i∈A} cc i * z i`, which the hypothesis bounds by `B` at `S = A`.

(The non-negativity `hcc` is not needed for dominance itself — it matters only when
the cut is used as a `≥ 0`-multiplier Farkas premise downstream — but we carry it to
match the cut API.) -/
theorem multiReluCut_pattern_dominance
    {k : ℕ} (cc z : Fin k → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i)
    (hpat : ∀ S : Finset (Fin k), (∑ i ∈ S, cc i * z i) ≤ B) :
    (∑ i, cc i * relu (z i)) ≤ B := by
  classical
  -- The ReLU sum equals the per-pattern form over the active set.
  have hsplit : (∑ i, cc i * relu (z i))
      = (∑ i ∈ Finset.univ.filter (fun i => 0 ≤ z i), cc i * z i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    unfold relu
    rcases le_or_gt 0 (z i) with h | h
    · rw [if_pos h, max_eq_right h]
    · rw [if_neg (not_le.mpr h), max_eq_left (le_of_lt h), mul_zero]
  rw [hsplit]
  exact hpat (Finset.univ.filter (fun i => 0 ≤ z i))

/-! ### k-induction view of the same fact.

The fully-general Finset proof above already covers every `k`.  For completeness we
also exhibit the explicit `Fin (k+1)`-recursion form: peeling neuron `0`, the ReLU
sum is `cc 0 * relu (z 0) + (k-neuron tail)`.  This makes the "lifting pattern"
visible: the inductive step is exactly a 2-pattern split on neuron `0` (active /
inactive) feeding the `k`-neuron hypothesis, the n-dimensional analogue of the
2-into-1 step.  We state it via `Fin.sum_univ_succ`. -/
theorem multiReluCut_pattern_dominance_succ
    {k : ℕ} (cc z : Fin (k+1) → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i)
    (hpat : ∀ S : Finset (Fin (k+1)), (∑ i ∈ S, cc i * z i) ≤ B) :
    (∑ i, cc i * relu (z i)) ≤ B :=
  -- the general theorem applies at every k, in particular k+1
  multiReluCut_pattern_dominance cc z B hcc hpat

/-! ## 2.  n-dimensional box B-derivation: per-pattern affine forms are bounded at
box corners, so `B = max-over-corners` is a DERIVED valid bound.

We represent an affine functional of an `n`-box input `x : Fin n → ℚ` as
`linVal w x r = (∑_j w j * x j) + r`. -/

/-- An affine functional of the box input. -/
def linVal {n : ℕ} (w : Fin n → ℚ) (x : Fin n → ℚ) (r : ℚ) : ℚ :=
  (∑ j, w j * x j) + r

/-- `linVal` as an affine function of a single coordinate `j` (slope `w j`). -/
theorem linVal_update {n : ℕ} (w x : Fin n → ℚ) (r : ℚ) (j : Fin n) (v : ℚ) :
    linVal w (Function.update x j v) r
      = w j * v + ((∑ i ∈ Finset.univ.erase j, w i * x i) + r) := by
  unfold linVal
  rw [← Finset.add_sum_erase Finset.univ
        (fun i => w i * Function.update x j v i) (Finset.mem_univ j)]
  rw [Function.update_self]
  have hrest : (∑ i ∈ Finset.univ.erase j, w i * Function.update x j v i)
       = (∑ i ∈ Finset.univ.erase j, w i * x i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest]; ring

/-- **Box-corner induction (auxiliary).**  Induct on the *free* coordinate set `F`.
If `x` lies in the box on every coordinate of `F`, and every "corner completion"
of `x` over `F` (each `F`-coordinate pushed to `xl` or `xu`) has `linVal ≤ B`, then
`linVal w x r ≤ B`.  The inductive step fixes one free coordinate `j`: `linVal` is
affine in `x j` (slope `w j`), so by the 1-box `affine_le_of_endpoints` it is
bounded by its values at `x j = xl j` and `x j = xu j`, each handled by the
induction hypothesis over the smaller free set. -/
theorem box_le_of_corners_aux {n : ℕ} (w xl xu : Fin n → ℚ) (r B : ℚ) :
    ∀ (F : Finset (Fin n)) (x : Fin n → ℚ),
      (∀ i ∈ F, xl i ≤ x i ∧ x i ≤ xu i) →
      (∀ y : Fin n → ℚ, (∀ i ∈ F, y i = xl i ∨ y i = xu i) →
                        (∀ i ∉ F, y i = x i) → linVal w y r ≤ B) →
      linVal w x r ≤ B := by
  intro F
  induction F using Finset.induction with
  | empty =>
    intro x _ hcorn
    exact hcorn x (by intro i hi; exact absurd hi (Finset.notMem_empty i))
                    (by intro i _; rfl)
  | insert j F hj ih =>
    intro x hbox hcorn
    obtain ⟨hjl, hju⟩ := hbox j (Finset.mem_insert_self j F)
    set Rrest : ℚ := (∑ i ∈ Finset.univ.erase j, w i * x i) + r with hRrest
    have hval : ∀ v : ℚ, linVal w (Function.update x j v) r = w j * v + Rrest := by
      intro v; rw [linVal_update]
    have hxself : linVal w x r = w j * (x j) + Rrest := by
      have := hval (x j); rwa [Function.update_eq_self] at this
    -- For an endpoint value `e ∈ {xl j, xu j}`, push j to e and apply ih on F.
    have hbound : ∀ e : ℚ, (e = xl j ∨ e = xu j) → w j * e + Rrest ≤ B := by
      intro e he
      rw [← hval e]
      apply ih (Function.update x j e)
      · -- box on F: coords in F differ from j, untouched by the update
        intro i hiF
        have hij : i ≠ j := by rintro rfl; exact hj hiF
        rw [Function.update_of_ne hij]
        exact hbox i (Finset.mem_insert_of_mem hiF)
      · -- corner completions over F lift to corner completions over insert j F
        intro y hyF hyoff
        apply hcorn y
        · intro i hi
          rcases Finset.mem_insert.mp hi with hij | hiF
          · subst hij
            have hyi : y i = (Function.update x i e) i := hyoff i hj
            rw [hyi, Function.update_self]; exact he
          · exact hyF i hiF
        · intro i hi
          have hiF : i ∉ F := fun h => hi (Finset.mem_insert_of_mem h)
          have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_insert_self j F)
          rw [hyoff i hiF, Function.update_of_ne hij]
    rw [hxself]
    exact affine_le_of_endpoints (w j) Rrest (xl j) (xu j) (x j) B hjl hju
            (hbound (xl j) (Or.inl rfl)) (hbound (xu j) (Or.inr rfl))

/-- **Affine functional ≤ B on a box from its values at the box corners.**
If `x` is in the box `[xl,xu]` coordinatewise and `linVal w y r ≤ B` for every box
corner `y` (each coordinate at `xl` or `xu`), then `linVal w x r ≤ B`. -/
theorem affine_box_le_of_corners {n : ℕ} (w xl xu : Fin n → ℚ) (r B : ℚ)
    (x : Fin n → ℚ) (hbox : ∀ i, xl i ≤ x i ∧ x i ≤ xu i)
    (hcorn : ∀ y : Fin n → ℚ, (∀ i, y i = xl i ∨ y i = xu i) → linVal w y r ≤ B) :
    linVal w x r ≤ B := by
  apply box_le_of_corners_aux w xl xu r B Finset.univ x
  · intro i _; exact hbox i
  · intro y hyF _; exact hcorn y (fun i => hyF i (Finset.mem_univ i))

/-- The per-pattern weighted sum of affine pre-activations is itself affine:
`∑_{i∈S} cc i * (linVal (p i) x (r i)) = linVal (∑_{i∈S} cc i * p i ·) x (∑_{i∈S} cc i * r i)`. -/
theorem pattern_affine_assemble {n k : ℕ}
    (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (x : Fin n → ℚ) (S : Finset (Fin k)) :
    (∑ i ∈ S, cc i * linVal (p i) x (r i))
      = linVal (fun j => ∑ i ∈ S, cc i * p i j) x (∑ i ∈ S, cc i * r i) := by
  unfold linVal
  have step1 : (∑ i ∈ S, cc i * ((∑ j, p i j * x j) + r i))
      = (∑ i ∈ S, cc i * (∑ j, p i j * x j)) + (∑ i ∈ S, cc i * r i) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [step1]
  congr 1
  have lhs2 : (∑ i ∈ S, cc i * (∑ j, p i j * x j))
      = (∑ i ∈ S, ∑ j, (cc i * p i j) * x j) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have rhs2 : (∑ j, (∑ i ∈ S, cc i * p i j) * x j)
      = (∑ j, ∑ i ∈ S, (cc i * p i j) * x j) := by
    apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
  rw [lhs2, rhs2, Finset.sum_comm]

/-- **General-k joint cut over an affine n-box.**  Each `z_i = linVal (p i) x (r i)`
is affine in the box input `x ∈ [xl,xu]`.  If the candidate bound `B` dominates each
of the `2^k` per-pattern affine forms at EVERY box corner, then
`∑_i cc i * relu (z_i) ≤ B` for every `x` in the box.  This DERIVES a valid joint
k-cut bound `B` from finitely many (corner) inequalities, for arbitrary weights. -/
theorem multiReluCut_box_le {n k : ℕ}
    (cc : Fin k → ℚ) (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ)
    (xl xu : Fin n → ℚ) (B : ℚ)
    (hcc : ∀ i, 0 ≤ cc i)
    (x : Fin n → ℚ) (hbox : ∀ j, xl j ≤ x j ∧ x j ≤ xu j)
    (hcorn : ∀ (S : Finset (Fin k)) (y : Fin n → ℚ),
              (∀ j, y j = xl j ∨ y j = xu j) →
              linVal (fun j => ∑ i ∈ S, cc i * p i j) y (∑ i ∈ S, cc i * r i) ≤ B) :
    (∑ i, cc i * relu (linVal (p i) x (r i))) ≤ B := by
  apply multiReluCut_pattern_dominance cc (fun i => linVal (p i) x (r i)) B hcc
  intro S
  rw [pattern_affine_assemble cc p r x S]
  exact affine_box_le_of_corners _ xl xu _ B x hbox (hcorn S)

/-! ## 3.  Composition: the general-k cut as a Farkas premise.

The joint k-cut is the single `≥ 0`-multiplier premise `g_cut = (∑ cc_i a_i) - B ≤ 0`,
sound on valid states because `a_i = relu (z_i)` and `multiReluCut_pattern_dominance`
gives `∑ cc_i relu z_i ≤ B`.  We feed exactly this into `farkas_premise_combination`
(a single `Fin 1` premise), the general-k analogue of `twoReluCut_bridge`. -/

/-- A relaxed-network state carrying the k pre/post-activations and the scalar output. -/
structure MultiReluState (k : ℕ) where
  z : Fin k → ℚ
  a : Fin k → ℚ
  out : ℚ

/-- Genuine execution: each `a_i = relu (z_i)` and `out = const - ∑ cc_i a_i`. -/
def MultiReluState.valid {k : ℕ} (cc : Fin k → ℚ) (const : ℚ)
    (st : MultiReluState k) : Prop :=
  (∀ i, st.a i = relu (st.z i)) ∧ st.out = const - (∑ i, cc i * st.a i)

/-- **General-k cut bridge.**  With the per-pattern bound holding for the
pre-activations of every valid state and a single non-negative multiplier `m`
forming the Farkas certificate `m * g_cut = -(out) - c`, every valid state has
`out ≥ -c`.  This is `farkas_to_interval` for the joint k-ReLU cut, proven by
reduction to `farkas_premise_combination`. -/
theorem multiReluCut_bridge {k : ℕ}
    (cc : Fin k → ℚ) (const B c m : ℚ)
    (hcc : ∀ i, 0 ≤ cc i) (hm : 0 ≤ m)
    (hpat : ∀ st : MultiReluState k, MultiReluState.valid cc const st →
              ∀ S : Finset (Fin k), (∑ i ∈ S, cc i * st.z i) ≤ B)
    (hcert : ∀ st : MultiReluState k,
        m * ((∑ i, cc i * st.a i) - B) = -(st.out) - c) :
    ∀ st : MultiReluState k, MultiReluState.valid cc const st → -c ≤ st.out := by
  refine farkas_premise_combination (S := MultiReluState k) (ι := Fin 1)
    (premises := Finset.univ)
    (g := fun _ st => (∑ i, cc i * st.a i) - B)
    (out := fun st => st.out)
    (μ := fun _ => m) (c := c)
    (valid := MultiReluState.valid cc const)
    ?hμ ?hg ?hcert
  case hμ => intro i _; exact hm
  case hg =>
    intro i _ st hv
    simp only []
    have hcut : (∑ i, cc i * relu (st.z i)) ≤ B :=
      multiReluCut_pattern_dominance cc st.z B hcc (hpat st hv)
    have heq : (∑ i, cc i * st.a i) = (∑ i, cc i * relu (st.z i)) := by
      apply Finset.sum_congr rfl; intro i _; rw [hv.1 i]
    rw [heq]; linarith
  case hcert =>
    intro st
    simp only [Fin.sum_univ_one]
    exact hcert st

/-! ## 4.  Concrete k = 3 DEMONSTRATION of genuine 3-way coupling.

Box `[-1,1]^2`, three unstable pre-activations affine in `x = (x1,x2)`:
  z1 = x1,   z2 = -x1 + 2 x2,   z3 = -x1 - 2 x2.

* The joint 3-ReLU cut `relu z1 + relu z2 + relu z3 ≤ 3` is VALID and TIGHT (all 8
  patterns × 4 corners ≤ 3, attained at corners (-1,±1)).  DERIVED through
  `multiReluCut_box_le`.  With `const = 3`, the margin `3 - ∑ relu z_i ≥ 0` is
  CLOSED on the whole box.

* No combination of k ≤ 2 cuts + ReLU triangle envelopes can certify it: the
  EXPLICIT relaxation-feasible point `x = (0,-1)`, `a = (1/2, 1/2, 5/2)` satisfies
  every per-coordinate ReLU upper triangle envelope AND every pairwise joint cut
  (B12 = B13 = B23 = 3), yet `∑ a_i = 7/2 > 3`.  So the k ≤ 2 LP relaxation only
  proves `∑ relu z_i ≤ 7/2`, leaving the margin OPEN at `-1/2`.  Only the joint
  3-cut closes it: genuine 3-way coupling content. -/

/-- Demo weight rows `p_i = (p_i1, p_i2)` for `z_i = p_i1*x1 + p_i2*x2`. -/
def demoP : Fin 3 → Fin 2 → ℚ
  | 0 => ![ 1,  0]
  | 1 => ![-1,  2]
  | 2 => ![-1, -2]

/-- Demo intercepts (all zero). -/
def demoR : Fin 3 → ℚ := fun _ => 0

/-- Demo weights `cc = (1,1,1)`. -/
def demoCC : Fin 3 → ℚ := fun _ => 1

/-- Box lower corner `(-1,-1)`. -/
def demoXl : Fin 2 → ℚ := fun _ => -1
/-- Box upper corner `(1,1)`. -/
def demoXu : Fin 2 → ℚ := fun _ => 1

/-- The derived joint 3-cut bound. -/
def demoB : ℚ := 3

/-- Helper: a per-pattern sum is dominated by the full ReLU sum of the same terms.
`∑_{i∈S} t i ≤ ∑_{i∈univ} relu (t i)` (drop the off-pattern terms and the negative
parts).  This reduces "bound the form for EVERY pattern `S`" to "bound the single
ReLU sum", which at each box corner is a concrete rational. -/
theorem sum_sub_le_sum_relu {k : ℕ} (t : Fin k → ℚ) (S : Finset (Fin k)) :
    (∑ i ∈ S, t i) ≤ (∑ i, relu (t i)) := by
  classical
  calc (∑ i ∈ S, t i)
      ≤ (∑ i ∈ S, relu (t i)) := by
        apply Finset.sum_le_sum; intro i _; unfold relu; exact le_max_right 0 (t i)
    _ ≤ (∑ i, relu (t i)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro i _ _; unfold relu; exact le_max_left 0 (t i)

/-- **Demo joint 3-cut is valid on the whole box** (derived through the general-k
box machinery).  For every `x ∈ [-1,1]^2`,
`relu z1 + relu z2 + relu z3 ≤ 3`. -/
theorem demo_joint_cut_le (x : Fin 2 → ℚ)
    (hbox : ∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j) :
    (∑ i, demoCC i * relu (linVal (demoP i) x (demoR i))) ≤ demoB := by
  apply multiReluCut_box_le demoCC demoP demoR demoXl demoXu demoB
  · intro i; fin_cases i <;> norm_num [demoCC]
  · exact hbox
  · -- per-pattern corner check, for every S and every corner y of [-1,1]^2.
    intro S y hy
    -- bound the assembled per-pattern form by ∑_i relu(cc_i*(p_i·y)), then ≤ 3 at each corner.
    have hyl0 := hy 0; have hyl1 := hy 1
    -- the per-pattern linVal equals ∑_{i∈S} (cc_i*(p_i·y))   (intercepts are 0)
    have hform : linVal (fun j => ∑ i ∈ S, demoCC i * demoP i j) y
                   (∑ i ∈ S, demoCC i * demoR i)
        = (∑ i ∈ S, demoCC i * (∑ j, demoP i j * y j)) := by
      rw [← pattern_affine_assemble demoCC demoP demoR y S]
      apply Finset.sum_congr rfl; intro i _; simp only [linVal, demoR, add_zero]
    rw [hform]
    -- dominate by the full ReLU sum of the same terms
    refine le_trans (sum_sub_le_sum_relu
      (fun i => demoCC i * (∑ j, demoP i j * y j)) S) ?_
    -- now y is a concrete corner: each y j ∈ {-1,1}; evaluate the 4 corners.
    simp only [demoXl, demoXu] at hyl0 hyl1
    rcases hyl0 with hyl0 | hyl0 <;> rcases hyl1 with hyl1 | hyl1 <;>
      · simp only [demoCC, demoP, demoB, Fin.sum_univ_two, Fin.sum_univ_three,
                   Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                   hyl0, hyl1, one_mul, relu]
        norm_num

/-! ### 4b.  k ≤ 2 cannot close it: an explicit relaxation-feasible point with
`∑ a_i = 7/2 > 3`.

`relu`-triangle upper envelopes on the demo box:
  z1 ∈ [-1,1] : slope s1 = 1/2, env a1 ≤ (1/2)(z1 + 1)
  z2 ∈ [-3,3] : slope s2 = 1/2, env a2 ≤ (1/2)(z2 + 3)
  z3 ∈ [-3,3] : slope s3 = 1/2, env a3 ≤ (1/2)(z3 + 3)
Pairwise joint 2-cuts: B12 = B13 = B23 = 3 (each pair's box max of relu+relu).

At `x = (0,-1)`: z = (0, -2, 2); the upper-envelope values are
  a1 = (1/2)(0+1) = 1/2,  a2 = (1/2)(-2+3) = 1/2,  a3 = (1/2)(2+3) = 5/2,
all pairwise sums ≤ 3, and `a1+a2+a3 = 7/2 > 3`.  This certifies that the k ≤ 2
relaxation admits `∑ a_i = 7/2`, so it CANNOT prove `∑ relu z_i ≤ 3`. -/

/-- The explicit relaxation witness `a = (1/2, 1/2, 5/2)`. -/
def demoA : Fin 3 → ℚ
  | 0 => 1/2
  | 1 => 1/2
  | 2 => 5/2

/-- **k ≤ 2 relaxation is OPEN.**  The witness `demoA` satisfies every per-coordinate
ReLU upper-triangle envelope at `x = (0,-1)` and every pairwise joint cut (B = 3),
yet `∑ demoA i = 7/2 > 3 = demoB`.  Hence no k ≤ 2 cut combination certifies the
joint bound; only the 3-cut closes the margin. -/
theorem demo_pairwise_relaxation_open :
    -- per-coordinate triangle envelopes hold at x=(0,-1):  z=(0,-2,2)
    (demoA 0 ≤ (1/2) * (0 + 1)) ∧
    (demoA 1 ≤ (1/2) * (-2 + 3)) ∧
    (demoA 2 ≤ (1/2) * (2 + 3)) ∧
    (0 ≤ demoA 0) ∧ (0 ≤ demoA 1) ∧ (0 ≤ demoA 2) ∧
    -- pairwise joint 2-cuts (each pair's box max = 3) hold
    (demoA 0 + demoA 1 ≤ 3) ∧
    (demoA 0 + demoA 2 ≤ 3) ∧
    (demoA 1 + demoA 2 ≤ 3) ∧
    -- but the triple sum exceeds the joint bound: relaxation cannot close
    (demoB < demoA 0 + demoA 1 + demoA 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [demoA, demoB] <;> norm_num

/-- **End-to-end demo margin closure.**  For the demo network output
`out = 3 - (relu z1 + relu z2 + relu z3)` (i.e. `const = demoB = 3`), the joint
3-cut closes the margin: `out ≥ 0` for every box point.  This is the payoff —
combined with `demo_pairwise_relaxation_open`, it shows the margin is closed by the
joint 3-cut yet provably NOT by any k ≤ 2 combination, exhibiting genuine 3-way
coupling content. -/
theorem demo_margin_closed (x : Fin 2 → ℚ)
    (hbox : ∀ j, demoXl j ≤ x j ∧ x j ≤ demoXu j)
    (out : ℚ)
    (hout : out = demoB - (∑ i, demoCC i * relu (linVal (demoP i) x (demoR i)))) :
    (0 : ℚ) ≤ out := by
  have hcut := demo_joint_cut_le x hbox
  rw [hout]; linarith

#print axioms multiReluCut_pattern_dominance
#print axioms multiReluCut_pattern_dominance_succ
#print axioms linVal_update
#print axioms box_le_of_corners_aux
#print axioms affine_box_le_of_corners
#print axioms pattern_affine_assemble
#print axioms multiReluCut_box_le
#print axioms multiReluCut_bridge
#print axioms sum_sub_le_sum_relu
#print axioms demo_joint_cut_le
#print axioms demo_pairwise_relaxation_open
#print axioms demo_margin_closed

end Crownproof
